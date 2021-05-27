use std::rc::Rc;

use byteorder::{ByteOrder, LittleEndian};

use scarf::{BinaryFile, DestOperand, MemAccessSize, Operand, OperandType, Operation};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::analysis::{self, Control, FuncAnalysis};

use crate::add_terms::collect_arith_add_terms;
use crate::{
    AnalysisCtx, ArgCache, EntryOf, OptionExt, entry_of_until, single_result_assign,
    OperandExt, ControlExt, FunctionFinder, SwitchTable,
};

#[derive(Clone)]
pub struct PrismShaders<Va: VirtualAddress> {
    pub vertex_shaders: Rc<Vec<Va>>,
    pub pixel_shaders: Rc<Vec<Va>>,
}

impl<Va: VirtualAddress> Default for PrismShaders<Va> {
    fn default() -> PrismShaders<Va> {
        PrismShaders {
            vertex_shaders: Rc::new(Vec::new()),
            pixel_shaders: Rc::new(Vec::new()),
        }
    }
}

struct DrawImageEntryCheck<'e, E: ExecutionState<'e>> {
    result: bool,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

// First check in DrawImage is `if (image->flags & hidden) { return; }`
impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for DrawImageEntryCheck<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(..) => {
                ctrl.end_analysis();
            }
            Operation::Jump { condition, .. } => {
                let condition = ctrl.resolve(condition);
                self.result = condition.iter_no_mem_addr().any(|x| {
                    x.if_arithmetic_and()
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0x40))
                        .and_then(|x| x.if_memory().map(|x| &x.address))
                        .and_then(|x| x.if_arithmetic_add())
                        .and_either(|x| x.if_register().filter(|&r| r.0 == 1))
                        .is_some()
                });
                ctrl.end_analysis();
            }
            _ => (),
        }
    }
}

pub(crate) fn draw_image<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    switches: &[SwitchTable<E::VirtualAddress>],
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    // Switch table for drawfunc-specific code.
    // Hopefully not going to be changed. Starts from func #2 (Cloaking start)
    let switches = switches.iter().filter(|switch| {
        let cases = &switch.cases;
        cases.len() == 0x10 &&
            cases[0x0] == cases[0x2] && // Cloak start == cloak end == detected start/end
            cases [0x0] == cases[0x3] &&
            cases[0x0] == cases[0x5] &&
            cases[0x1] == cases[0x6] && // Cloak == emp == remap == flag (?)
            cases[0x1] == cases[0x7] &&
            cases[0x1] == cases[0xc]
    });
    let funcs = functions.functions();
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut result = None;
    for table in switches {
        let value = entry_of_until(
            binary,
            &funcs,
            table.cases[0],
            |addr| {
                let mut analyzer = DrawImageEntryCheck::<E> {
                    result: false,
                    phantom: Default::default(),
                };
                let mut analysis = FuncAnalysis::new(binary, ctx, addr);
                analysis.analyze(&mut analyzer);
                if analyzer.result {
                    EntryOf::Ok(())
                } else {
                    EntryOf::Retry
                }
            }
        );
        if single_result_assign(value.into_option_with_entry().map(|x| x.0), &mut result) {
            break;
        }
    }

    result
}

pub(crate) fn renderer_vtables<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Vec<E::VirtualAddress> {
    crate::vtables::vtables(analysis, functions, b".?AVRenderer@@\0")
}

pub(crate) fn prism_shaders<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    renderer_vtables: &[E::VirtualAddress],
) -> PrismShaders<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let compare = b".?AVPrismRenderer";
    let prism_renderer_vtable = renderer_vtables.iter().copied().filter(|&vtable| {
        vtable_class_name(binary, vtable)
            .filter(|name| name.starts_with(compare))
            .is_some()
    }).next();
    let prism_renderer_vtable = match prism_renderer_vtable {
        Some(s) => s,
        None => return PrismShaders::default(),
    };
    let code_section = binary.code_section();
    for i in 0x10.. {
        let offset = E::VirtualAddress::SIZE * i;
        let func = match binary.read_address(prism_renderer_vtable + offset) {
            Ok(o) => o,
            Err(_) => break,
        };
        let code_end = code_section.virtual_address + code_section.virtual_size;
        if func < code_section.virtual_address || func >= code_end {
            break;
        }
        let arg_cache = &analysis.arg_cache;
        let bump = &analysis.bump;
        let mut analyzer = FindPrismShaders::<E> {
            vertex: Vec::new(),
            pixel: Vec::new(),
            arg_cache,
            bump,
            inline_depth: 0,
            binary,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, func);
        analysis.analyze(&mut analyzer);
        if !analyzer.vertex.is_empty() || !analyzer.pixel.is_empty() {
            return PrismShaders {
                vertex_shaders: Rc::new(analyzer.vertex),
                pixel_shaders: Rc::new(analyzer.pixel),
            };
        }
    }
    PrismShaders::default()
}

struct FindPrismShaders<'a, 'e, E: ExecutionState<'e>> {
    vertex: Vec<E::VirtualAddress>,
    pixel: Vec<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    bump: &'a bumpalo::Bump,
    binary: &'e BinaryFile<E::VirtualAddress>,
    inline_depth: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindPrismShaders<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if self.inline_depth == 0 {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        if arg1 == self.arg_cache.on_entry(0) {
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if !self.vertex.is_empty() && !self.pixel.is_empty() {
                                ctrl.end_analysis();
                                return;
                            }
                        }
                    }
                }
            }
            Operation::Move(_, unresolved, None) => {
                let value = ctrl.resolve(unresolved);
                if is_vertex_shader_name(self.binary, value) {
                    let addr = match *unresolved.ty() {
                        OperandType::Memory(mem) => mem.address,
                        OperandType::Register(_) => unresolved,
                        _ => return,
                    };
                    let addr = ctrl.resolve(addr);
                    self.check_vertex_shaders(ctrl, addr);
                } else {
                    self.check_pixel_shaders(ctrl, value);
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> FindPrismShaders<'a, 'e, E> {
    fn check_vertex_shaders(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, addr: Operand<'e>) {
        static VERTEX_SHADER_NAMES: &[&[u8]] = &[
            b"vert_uv1",
            b"vert_uv2",
            b"vert_uv3",
            b"flat_color_vert",
            b"colored_vert",
            b"deferred_blit_vert",
        ];
        if self.vertex.len() == VERTEX_SHADER_NAMES.len() {
            return;
        }
        let mut result = Vec::new();
        let word_size = match E::VirtualAddress::SIZE {
            4 => MemAccessSize::Mem32,
            _ => MemAccessSize::Mem64,
        };
        for i in 0.. {
            let name_addr = ctrl.const_word_offset(addr, i * 2);
            let set_addr = ctrl.const_word_offset(addr, i * 2 + 1);
            let name = match ctrl.read_memory(name_addr, word_size).if_constant() {
                Some(s) => s,
                None => break,
            };
            let set = match ctrl.read_memory(set_addr, word_size).if_constant() {
                Some(s) => s,
                None => break,
            };
            let shader_id = self.binary.section_by_addr(E::VirtualAddress::from_u64(name))
                .and_then(|section| {
                    name.checked_sub(section.virtual_address.as_u64())
                        .and_then(|rel| section.data.get(rel as usize..))
                })
                .and_then(|slice| VERTEX_SHADER_NAMES.iter().position(|&x| slice.starts_with(x)));
            let shader_id = match shader_id {
                Some(s) => s,
                None => break,
            };
            if result.len() <= shader_id {
                result.resize(shader_id + 1, E::VirtualAddress::from_u64(0));
            }
            result[shader_id] = E::VirtualAddress::from_u64(set);
        }
        let final_len = result.iter().position(|x| x.as_u64() == 0).unwrap_or(result.len());
        result.resize(final_len, E::VirtualAddress::from_u64(0));
        if result.len() > self.vertex.len() {
            self.vertex = result;
        }
    }

    fn check_pixel_shaders(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, value: Operand<'e>) {
        let word_size = match E::VirtualAddress::SIZE {
            4 => MemAccessSize::Mem32,
            _ => MemAccessSize::Mem64,
        };
        let addr = match ctrl.if_mem_word(value) {
            Some(s) => s,
            None => return,
        };
        let mut terms = match collect_arith_add_terms(addr, self.bump) {
            Some(s) => s,
            None => return,
        };
        let ctx = ctrl.ctx();
        let ok = terms.remove_one(|term, neg| {
            !neg && term.if_arithmetic_mul()
                .filter(|(_, r)| {
                    r.if_constant().filter(|&c| c == E::VirtualAddress::SIZE as u64).is_some()
                })
                .and_then(|(l, _)| ctrl.if_mem_word(l))
                .filter(|&x| x == self.arg_cache.on_entry(0))
                .is_some()
        });
        if ok {
            let base = terms.join(ctx);
            let mut result = Vec::with_capacity(0x30);
            for i in 0.. {
                let addr = ctrl.const_word_offset(base, i);
                let value = match ctrl.read_memory(addr, word_size).if_constant() {
                    Some(s) => s,
                    None => break,
                };
                let addr = E::VirtualAddress::from_u64(value);
                if !self.is_shader_set(addr) {
                    break;
                }
                result.push(E::VirtualAddress::from_u64(value));
            }
            if result.len() > self.pixel.len() {
                self.pixel = result;
            }
        }
    }

    fn is_shader_set(&self, addr: E::VirtualAddress) -> bool {
        let section = match self.binary.section_by_addr(addr) {
            Some(s) => s,
            None => return false,
        };
        let relative = (addr.as_u64() - section.virtual_address.as_u64()) as usize;
        let slice = &section.data[relative..];
        if slice.len() < 16 {
            return false;
        }
        let len = LittleEndian::read_u32(slice);
        let ptr = if E::VirtualAddress::SIZE == 4 {
            E::VirtualAddress::from_u64(LittleEndian::read_u32(&slice[4..]) as u64)
        } else {
            E::VirtualAddress::from_u64(LittleEndian::read_u64(&slice[8..]))
        };
        if len > 8 || len == 0 {
            return false;
        }
        self.binary.section_by_addr(ptr).is_some()
    }
}

fn is_vertex_shader_name<'e, Va: VirtualAddress>(
    binary: &'e BinaryFile<Va>,
    value: Operand<'e>,
) -> bool {
    let compare = b"vert_uv1";
    if let Some(c) = value.if_constant() {
        if let Some(addr) = c.checked_sub(binary.base().as_u64()).map(|x| x as u32) {
            if let Some(end) = addr.checked_add(compare.len() as u32) {
                if let Ok(slice) = binary.slice_from(addr..end){
                    if slice == compare {
                        return true;
                    }
                }
            }
        }
    }
    false
}

pub(crate) fn player_unit_skins<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    draw_image: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let arg_cache = &analysis.arg_cache;
    // Search for a child function of draw_image
    // thiscall f(player_unit_skins, player, unit_id, image_id)
    let mut analyzer = PlayerUnitSkins::<E> {
        arg_cache,
        result: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, draw_image);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct PlayerUnitSkins<'a, 'e, E: ExecutionState<'e>> {
    arg_cache: &'a ArgCache<'e, E>,
    result: Option<Operand<'e>>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for PlayerUnitSkins<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(_) => {
                let ctx = ctrl.ctx();
                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                let ok = ctx.and_const(arg1, 0xff).if_mem8().is_some() &&
                    arg3.if_mem16()
                        .and_then(|x| x.if_arithmetic_add_const(8))
                        .and_then(|x| x.if_register())
                        .filter(|r| r.0 == 1)
                        .is_some();
                if ok {
                    let ecx = ctrl.resolve(ctx.register(1));
                    if ecx.if_constant().is_some() || ctrl.if_mem_word(ecx).is_some() {
                        if single_result_assign(Some(ecx), &mut self.result) {
                            ctrl.end_analysis();
                        }
                    }
                }
                // Assume cdecl calls
                ctrl.skip_operation();
                let state = ctrl.exec_state();
                state.move_to(
                    &DestOperand::Register64(scarf::operand::Register(0)),
                    ctx.new_undef(),
                );
            }
            _ => (),
        }
    }
}

pub(crate) fn vertex_buffer<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    vtables: &[E::VirtualAddress],
) -> Option<Operand<'e>> {
    // Renderer_Draw (vtable + 0x1c) calls a function that uploads vertex
    // buffer (vtable + 0x28)
    // Renderer_Draw(this, draw_commands, width, height)
    //    upload_vertices_indices_and_sort_order(draw_commands)
    //      upload_vertices_indices_and_sort_order2(draw_commands)
    //        upload_vertices_indices(get_vertex_buf())
    //          Renderer_UploadVerticesIndices(global_renderer, buffer.x48, buffer.x8,
    //              buffer.x4, buffer.x38, buffer.x34)
    // Gl renderer is best for finding this function as it calls it pretty much
    // immediately, but have a fallback for prism renderer.
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let arg_cache = &analysis.arg_cache;
    let word_size = E::VirtualAddress::SIZE;

    for &renderer in &[&b".?AVGLRenderer"[..], b".?AVPrismRenderer"] {
        let vtable = vtables.iter().copied().filter(|&vtable| {
            vtable_class_name(binary, vtable)
                .filter(|name| name.starts_with(renderer))
                .is_some()
        }).next();
        let draw = match vtable.and_then(|x| binary.read_address(x + 7 * word_size).ok()) {
            Some(s) => s,
            None => continue,
        };
        let mut analyzer = FindVertexBuffer::<E> {
            arg_cache,
            result: None,
            get_fn_result: None,
            inline_depth: 0,
            checking_get_fn: false,
            get_fn_ok: false,
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, draw);
        analysis.analyze(&mut analyzer);
        if analyzer.result.is_some() {
            return analyzer.result;
        }
    }
    None
}

struct FindVertexBuffer<'a, 'e, E: ExecutionState<'e>> {
    arg_cache: &'a ArgCache<'e, E>,
    result: Option<Operand<'e>>,
    get_fn_result: Option<Operand<'e>>,
    inline_depth: u8,
    checking_get_fn: bool,
    get_fn_ok: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindVertexBuffer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if self.get_fn_ok {
            match *op {
                Operation::Call(..) | Operation::Jump { .. } => {
                    self.get_fn_ok = false;
                    if self.checking_get_fn {
                        ctrl.end_analysis();
                    }
                }
                Operation::Return(..) => {
                    let ret = ctrl.resolve(ctx.register(0));
                    self.get_fn_result = Some(ret);
                }
                _ => (),
            }
            if self.checking_get_fn {
                return;
            }
        }
        match *op {
            Operation::Call(dest) => {
                let dest = ctrl.resolve(dest);
                if let Some(dest) = dest.if_constant().map(|x| E::VirtualAddress::from_u64(x)) {
                    if self.inline_depth < 2 {
                        // Check for first two funcs which take draw_commands as an arg
                        if ctrl.resolve(self.arg_cache.on_call(0)) == self.arg_cache.on_entry(0) {
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if self.result.is_some() {
                                ctrl.end_analysis();
                            }
                            return;
                        }
                    }
                    if self.inline_depth != 0 {
                        // Check for upload_vertices_indices with this == global
                        if let Some(_) = ctrl.resolve_va(ctx.register(1)) {
                            let old = self.inline_depth;
                            self.inline_depth = 9;
                            self.get_fn_ok = true;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = old;
                            if self.result.is_some() {
                                ctrl.end_analysis();
                            }
                            self.check_get_fn_result(ctrl);
                            return;
                        }
                        // Just inline in case it's a get fn
                        self.get_fn_ok = true;
                        self.checking_get_fn = true;
                        ctrl.analyze_with_current_state(self, dest);
                        self.checking_get_fn = false;
                        self.check_get_fn_result(ctrl);
                    }
                } else {
                    if self.inline_depth != 0 {
                        // Check for the actual renderer.upload_vertices_indices virtual call
                        let word_size = E::VirtualAddress::SIZE;
                        let is_vtable_fn_28 = ctrl.if_mem_word(dest)
                            .and_then(|x| x.if_arithmetic_add_const(0xa * word_size as u64))
                            .is_some();
                        if is_vtable_fn_28 {
                            let arg2 = ctrl.resolve(self.arg_cache.on_entry(1));
                            // Arg2 is Mem32[vertex_buf + 4]
                            let vertex_buf = ctrl.if_mem_word(arg2)
                                .map(|x| ctx.sub_const(x, word_size as u64));
                            if let Some(vertex_buf) = vertex_buf {
                                self.result = Some(vertex_buf);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> FindVertexBuffer<'a, 'e, E> {
    // Post-processing after inlining a function that may have been simple
    // `return x` get_fn()
    fn check_get_fn_result(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.get_fn_ok {
            if let Some(eax) = self.get_fn_result {
                let state = ctrl.exec_state();
                state.move_resolved(
                    &DestOperand::Register64(scarf::operand::Register(0)),
                    eax,
                );
                ctrl.skip_operation();
            }
            self.get_fn_ok = false;
        }
    }
}

fn vtable_class_name<Va: VirtualAddress>(binary: &BinaryFile<Va>, vtable: Va) -> Option<&[u8]> {
    let rtti = binary.read_address(vtable - Va::SIZE).ok()?;
    let class_info = binary.read_address(rtti + 0xc).ok()?;
    let start = class_info + 8;
    let section = binary.section_by_addr(start)?;
    let section_relative = start.as_u64().wrapping_sub(section.virtual_address.as_u64()) as usize;
    let slice = section.data.get(section_relative..)?;
    let end = slice.iter().position(|&x| x == 0)?;
    slice.get(..end)
}

pub(crate) fn draw_game_layer<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    draw_layers: Operand<'e>,
    funcs: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    // Find assignment to draw_layers[5].func = draw_game_layer, should be the only value
    // that it ever is set to.
    let binary = actx.binary;
    let ctx = actx.ctx;

    let dest_addr_op = ctx.add_const(
        draw_layers,
        0x14 * 5 + 0x10,
    );
    let dest_addr = E::VirtualAddress::from_u64(dest_addr_op.if_constant()?);
    let refs = funcs.find_functions_using_global(actx, dest_addr);
    let mut result = None;
    let functions = funcs.functions();
    for global_ref in &refs {
        let new = entry_of_until(binary, &functions, global_ref.use_address, |entry| {
            let mut analyzer = FindDrawGameLayer::<E> {
                dest_addr: dest_addr_op,
                result: EntryOf::Retry,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option();
        if single_result_assign(new, &mut result) {
            break;
        }
    }
    result
}

struct FindDrawGameLayer<'e, E: ExecutionState<'e>> {
    dest_addr: Operand<'e>,
    result: EntryOf<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindDrawGameLayer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Move(DestOperand::Memory(ref mem), value, None) => {
                if mem.size == E::WORD_SIZE && mem.address == self.dest_addr {
                    if let Some(value) = ctrl.resolve_va(value) {
                        self.result = EntryOf::Ok(value);
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}
