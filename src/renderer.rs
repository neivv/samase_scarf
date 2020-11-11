use std::rc::Rc;

use byteorder::{ByteOrder, LittleEndian};

use scarf::{BinaryFile, DestOperand, MemAccessSize, Operand, OperandType, Operation};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::analysis::{self, Control, FuncAnalysis};

use crate::add_terms::collect_arith_add_terms;
use crate::{
    AnalysisCtx, ArgCache, EntryOf, OptionExt, entry_of_until, single_result_assign,
    OperandExt,
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
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let switch_tables = analysis.switch_tables();
    // Switch table for drawfunc-specific code.
    // Hopefully not going to be changed. Starts from func #2 (Cloaking start)
    let switches = switch_tables.iter().filter(|switch| {
        let cases = &switch.cases;
        cases.len() == 0x10 &&
            cases[0x0] == cases[0x2] && // Cloak start == cloak end == detected start/end
            cases [0x0] == cases[0x3] &&
            cases[0x0] == cases[0x5] &&
            cases[0x1] == cases[0x6] && // Cloak == emp == remap == flag (?)
            cases[0x1] == cases[0x7] &&
            cases[0x1] == cases[0xc]
    });
    let funcs = analysis.functions();
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
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Vec<E::VirtualAddress> {
    crate::vtables::vtables(analysis, b".?AVRenderer@@\0")
}

pub(crate) fn prism_shaders<'e, E: ExecutionState<'e>>(
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> PrismShaders<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let vtables = analysis.renderer_vtables();
    let compare = b".?AVPrismRenderer";
    let prism_renderer_vtable = vtables.iter().filter_map(|&vtable| {
        let rtti = binary.read_address(vtable - E::VirtualAddress::SIZE).ok()?;
        let class_info = binary.read_address(rtti + 0xc).ok()?;
        let relative = class_info.as_u64().checked_sub(binary.base().as_u64())? as u32;
        let start = relative.checked_add(8)?;
        let end = start.checked_add(compare.len() as u32)?;
        let name = binary.slice_from(start..end).ok()?;
        Some(vtable).filter(|_| name == compare)
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
        let arg_cache = analysis.arg_cache;
        let bump = analysis.bump;
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
    analysis: &mut AnalysisCtx<'_, 'e, E>,
) -> Option<Operand<'e>> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let arg_cache = analysis.arg_cache;
    let draw_image = analysis.draw_image()?;
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
