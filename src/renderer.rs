use std::rc::Rc;

use byteorder::{ByteOrder, LittleEndian};

use scarf::{
    ArithOpType, BinaryFile, BinarySection, DestOperand, MemAccessSize, Operand, OperandType,
    Operation,
};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::operand::{OperandHashByAddress};

use crate::add_terms::collect_arith_add_terms;
use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{FunctionFinder, entry_of_until, EntryOf};
use crate::call_tracker::CallTracker;
use crate::float_cmp::{FloatEqTracker, FloatCmpJump};
use crate::hash_map::{HashSet};
use crate::util::{
    ControlExt, ExecStateExt, OperandExt, OptionExt, single_result_assign, is_global,
    resolve_rdata_const,
};
use crate::vtables::Vtables;

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

pub(crate) fn prism_shaders<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    vtables: &Vtables<'e, E::VirtualAddress>,
) -> PrismShaders<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let compare = b".?AVPrismRenderer";
    let prism_renderer_vtable = vtables.vtables_starting_with(compare)
        .map(|x| x.address)
        .next();
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
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve_arg(0);
                        if arg1 == self.arg_cache.on_thiscall_entry(0) {
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
            Operation::Move(_, unresolved) => {
                let value = ctrl.resolve(unresolved);
                if is_vertex_shader_name(self.binary, value) {
                    let ctx = ctrl.ctx();
                    let addr = match *unresolved.ty() {
                        OperandType::Memory(mem) => mem.address_op(ctx),
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
        let ctx = ctrl.ctx();
        let word_size = E::VirtualAddress::SIZE as u64;
        for i in 0.. {
            let name_addr = ctx.mem_access(addr, i * 2 * word_size, E::WORD_SIZE);
            let set_addr = ctx.mem_access(addr, (i * 2 + 1) * word_size, E::WORD_SIZE);
            let name = match ctrl.read_memory(&name_addr).if_constant() {
                Some(s) => s,
                None => break,
            };
            let set = match ctrl.read_memory(&set_addr).if_constant() {
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
        let mem = match ctrl.if_mem_word(value) {
            Some(s) => s,
            None => return,
        };
        let (mem_base, mem_offset) = mem.address();
        let mut terms = collect_arith_add_terms(mem_base, self.bump);
        let ctx = ctrl.ctx();
        let ok = terms.remove_one(|term, neg| {
            !neg && term.if_arithmetic_mul_const(E::VirtualAddress::SIZE.into())
                .and_then(|x| x.unwrap_sext().if_mem32()?.if_offset(0))
                .filter(|&x| x == self.arg_cache.on_thiscall_entry(0))
                .is_some()
        });
        if ok {
            let base = ctx.add_const(terms.join(ctx), mem_offset);
            let mut result = Vec::with_capacity(0x30);
            for i in 0.. {
                let addr = ctx.mem_access(base, i * E::VirtualAddress::SIZE as u64, E::WORD_SIZE);
                let value = match ctrl.read_memory(&addr).if_constant() {
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

pub(crate) fn analyze_draw_image<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    draw_image: E::VirtualAddress,
) -> DrawImage<'e, E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    // Search for a child function of draw_image
    // thiscall get_unit_skin(player_unit_skins, player, unit_id, image_id)
    let mut result = DrawImage {
        player_unit_skins: None,
        get_unit_skin: None,
    };
    let mut analyzer = PlayerUnitSkins::<E> {
        result: &mut result,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, draw_image);
    analysis.analyze(&mut analyzer);
    result
}

struct PlayerUnitSkins<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut DrawImage<'e, E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for PlayerUnitSkins<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let ctx = ctrl.ctx();
                let arg1 = ctrl.resolve_arg_thiscall_u8(0);
                let arg3 = ctrl.resolve_arg_thiscall(2);
                let ok = arg1.if_mem8().is_some() &&
                    arg3.if_mem16_offset(E::struct_layouts().image_id())
                        .filter(|&x| x == ctx.register(1))
                        .is_some();
                if ok {
                    let ecx = ctrl.resolve_register(1);
                    if ecx.if_constant().is_some() || ctrl.if_mem_word(ecx).is_some() {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            single_result_assign(Some(dest), &mut self.result.get_unit_skin);
                        }
                        if single_result_assign(Some(ecx), &mut self.result.player_unit_skins) {
                            ctrl.end_analysis();
                        }
                    }
                }
                // Assume cdecl calls
                ctrl.skip_call_preserve_esp();
            }
            _ => (),
        }
    }
}

pub(crate) fn vertex_buffer<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    vtables: &Vtables<'e, E::VirtualAddress>,
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

    for vtable in [&b".?AVGLRenderer"[..], b".?AVPrismRenderer"].iter()
        .flat_map(|name| vtables.vtables_starting_with(name))
        .map(|x| x.address)
    {
        let draw = match binary.read_address(vtable + 7 * word_size).ok() {
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
                    let ret = ctrl.resolve_register(0);
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
                        // Check for first two funcs which take draw_commands as an arg1
                        // One is thiscall, one is cdecl
                        if ctrl.resolve_arg(0) == self.arg_cache.on_thiscall_entry(0) ||
                            ctrl.resolve_arg_thiscall(0) == self.arg_cache.on_thiscall_entry(0)
                        {
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
                        let is_vtable_fn_28 = ctrl
                            .if_mem_word_offset(dest, 0xa * word_size as u64)
                            .is_some();
                        if is_vtable_fn_28 {
                            let arg3 = ctrl.resolve_arg_thiscall(2);
                            // Arg3 is Mem32[vertex_buf + 4] (Mem32 even on 64bit too)
                            let vertex_buf = arg3.if_mem32()
                                .map(|x| ctx.mem_sub_const_op(x, word_size as u64));
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
                ctrl.set_register(0, eax);
                ctrl.skip_operation();
            }
            self.get_fn_ok = false;
        }
    }
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
        E::struct_layouts().graphic_layer_size() * 5 +
            E::struct_layouts().graphic_layer_draw_func()
    );
    let dest_addr = E::VirtualAddress::from_u64(dest_addr_op.if_constant()?);
    let refs = funcs.find_functions_using_global(actx, dest_addr);
    let mut result = None;
    let functions = funcs.functions();
    for global_ref in &refs {
        let new = entry_of_until(binary, &functions, global_ref.use_address, |entry| {
            let mut analyzer = FindDrawGameLayer::<E> {
                dest_addr,
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
    dest_addr: E::VirtualAddress,
    result: EntryOf<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindDrawGameLayer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Move(DestOperand::Memory(ref mem), value) => {
                if mem.size == E::WORD_SIZE {
                    let dest = ctrl.resolve_mem(mem);
                    if dest.if_constant_address() == Some(self.dest_addr.as_u64()) {
                        if let Some(value) = ctrl.resolve_va(value) {
                            self.result = EntryOf::Ok(value);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) struct DrawImage<'e, Va: VirtualAddress> {
    pub get_unit_skin: Option<Va>,
    pub player_unit_skins: Option<Operand<'e>>,
}

pub(crate) struct DrawGameLayer<'e, E: ExecutionState<'e>> {
    pub prepare_draw_image: Option<E::VirtualAddress>,
    pub draw_image: Option<E::VirtualAddress>,
    pub draw_terrain: Option<E::VirtualAddress>,
    pub cursor_marker: Option<Operand<'e>>,
    pub update_game_screen_size: Option<E::VirtualAddress>,
    pub zoom_action_active: Option<Operand<'e>>,
    pub zoom_action_mode: Option<Operand<'e>>,
    pub zoom_action_start: Option<Operand<'e>>,
    pub zoom_action_target: Option<Operand<'e>>,
    pub zoom_action_completion: Option<Operand<'e>>,
}

pub(crate) struct RenderScreen<'e, E: ExecutionState<'e>> {
    pub config_vsync_value: Option<E::VirtualAddress>,
    pub get_render_target: Option<E::VirtualAddress>,
    pub clear_render_target: Option<E::VirtualAddress>,
    pub renderer: Option<Operand<'e>>,
    pub draw_commands: Option<Operand<'e>>,
}

pub(crate) struct DrawTerrain<'e, E: ExecutionState<'e>> {
    pub get_atlas_page_coords_for_terrain_tile: Option<E::VirtualAddress>,
}

pub(crate) fn analyze_draw_game_layer<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    draw_game_layer: E::VirtualAddress,
    sprite_size: u32,
    is_paused: Operand<'e>,
) -> DrawGameLayer<'e, E> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut result = DrawGameLayer {
        prepare_draw_image: None,
        draw_image: None,
        draw_terrain: None,
        cursor_marker: None,
        update_game_screen_size: None,
        zoom_action_active: None,
        zoom_action_mode: None,
        zoom_action_start: None,
        zoom_action_target: None,
        zoom_action_completion: None,
    };
    let sprite_first_overlay_offset = match E::struct_layouts().sprite_first_overlay(sprite_size) {
        Some(s) => s,
        None => return result,
    };

    let mut analyzer = AnalyzeDrawGameLayer::<E> {
        state: DrawGameLayerState::Init,
        result: &mut result,
        inline_depth: 0,
        inline_limit: 0,
        sprite_first_overlay_offset,
        arg_cache: &actx.arg_cache,
        rdata: actx.binary_sections.rdata,
        call_seen: false,
        first_jump: false,
        is_paused,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
        current_func: draw_game_layer,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, draw_game_layer);
    analysis.analyze(&mut analyzer);

    result
}

struct AnalyzeDrawGameLayer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    state: DrawGameLayerState,
    result: &'a mut DrawGameLayer<'e, E>,
    inline_depth: u8,
    inline_limit: u8,
    sprite_first_overlay_offset: u32,
    arg_cache: &'a ArgCache<'e, E>,
    rdata: &'a BinarySection<E::VirtualAddress>,
    call_seen: bool,
    first_jump: bool,
    is_paused: Operand<'e>,
    call_tracker: CallTracker<'acx, 'e, E>,
    current_func: E::VirtualAddress,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum DrawGameLayerState {
    /// Find jump for a5 == 0, follow the 0 branch
    /// (Code that is only ran on main draw, not secondary asset draw)
    Init,
    /// Inline once to step_zooming(), first jump should be is_zooming == 0
    /// (Follow nonzero branch)
    /// Then jump where global == 0 should be zoom_mode, follow zero branch
    IsZoomingAndMode,
    /// Find completion + step * 8.0 instruction
    ZoomCompletion,
    /// Find (target - start) * x
    ZoomStartTarget,
    /// prepare_draw_image and draw_image are from functions which are called
    /// with this = some_sprite.first_overlay and some_sprite.last_overlay
    /// draw_terrain is called in between those two, so detect it here as well
    /// from jump based on is_paused
    DrawImage,
    CursorMarker,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    AnalyzeDrawGameLayer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Jump { .. } = *op {
            if self.inline_limit != 0 {
                self.inline_limit -= 1;
                if self.inline_limit == 0 {
                    ctrl.end_analysis();
                    return;
                }
            }
        }
        match self.state {
            DrawGameLayerState::Init => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let ctx = ctrl.ctx();
                    if let Some((op, jump_if_zero)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        let op = ctx.and_const(op, 0xff);
                        let arg5 = ctx.and_const(self.arg_cache.on_entry(4), 0xff);
                        if op == arg5 {
                            let dest = match jump_if_zero {
                                false => ctrl.current_instruction_end(),
                                true => match ctrl.resolve_va(to) {
                                    Some(s) => s,
                                    None => return,
                                },
                            };
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_address(dest);
                            self.state = DrawGameLayerState::IsZoomingAndMode;
                        }
                    }
                }
            }
            DrawGameLayerState::IsZoomingAndMode => {
                if self.result.zoom_action_active.is_some() && !self.call_seen {
                    // Wait for at least one call after zoom_action_active
                    // Avoids false positives from assertions
                    if let Operation::Call(..) = *op {
                        self.call_seen = true;
                        ctrl.clear_unchecked_branches();
                    }
                    return;
                }

                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let ctx = ctrl.ctx();
                    if let Some((op, jump_if_zero)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        if is_global(op) {
                            let follow_zero;
                            if self.result.zoom_action_active.is_none() {
                                self.result.zoom_action_active = Some(op);
                                self.inline_limit = 0;
                                follow_zero = false;
                            } else {
                                self.result.zoom_action_mode = Some(op);
                                self.state = DrawGameLayerState::ZoomCompletion;
                                follow_zero = true;
                            }
                            let dest = match jump_if_zero ^ !follow_zero {
                                false => ctrl.current_instruction_end(),
                                true => match ctrl.resolve_va(to) {
                                    Some(s) => s,
                                    None => return,
                                },
                            };
                            ctrl.clear_unchecked_branches();
                            ctrl.continue_at_address(dest);
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if self.inline_depth == 0 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.inline_limit = 2;
                            self.inline_depth = 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = 0;
                            if self.result.zoom_action_active.is_some() {
                                self.state = DrawGameLayerState::DrawImage;
                            }
                        }
                    }
                }
            }
            DrawGameLayerState::ZoomCompletion => {
                if let Operation::Move(_, value) = *op {
                    let value = ctrl.resolve(value);
                    let result = value.if_arithmetic_float(ArithOpType::Add)
                        .and_either_other(|x| {
                            x.if_arithmetic_float(ArithOpType::Mul)
                                .and_either(|x| resolve_rdata_const(x, self.rdata))
                        });
                    if let Some(result) = result {
                        if is_global(result) {
                            self.result.zoom_action_completion = Some(result);
                            self.state = DrawGameLayerState::ZoomStartTarget;
                            ctrl.clear_unchecked_branches();
                        }
                    }
                }
            }
            DrawGameLayerState::ZoomStartTarget => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let a1 = ctrl.resolve(self.arg_cache.on_call_f32(0));
                        // start + (end - start) * pos
                        let result = a1.if_arithmetic_float(ArithOpType::Add)
                            .and_either(|x| {
                                x.if_arithmetic_float(ArithOpType::Mul)
                                    .and_either(|x| {
                                        x.if_arithmetic_float(ArithOpType::Sub)
                                    })
                                    .map(|x| x.0)
                            })
                            .map(|x| x.0);
                        if let Some((end, start)) = result {
                            if is_global(end) && is_global(start) {
                                self.result.zoom_action_target = Some(end);
                                self.result.zoom_action_start = Some(start);
                                self.result.update_game_screen_size = Some(dest);
                                self.state = DrawGameLayerState::DrawImage;
                                if self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
            DrawGameLayerState::DrawImage => {
                match *op {
                    Operation::Call(dest) => {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let this = ctrl.resolve_register(1);
                            let overlay_offset = if self.result.prepare_draw_image.is_none() {
                                self.sprite_first_overlay_offset
                            } else {
                                self.sprite_first_overlay_offset + E::VirtualAddress::SIZE
                            };
                            let is_overlay = ctrl.if_mem_word_offset(this, overlay_offset.into())
                                .is_some();
                            if is_overlay {
                                if self.result.prepare_draw_image.is_none() {
                                    self.result.prepare_draw_image = Some(dest);
                                } else {
                                    self.result.draw_image = Some(dest);
                                    self.state = DrawGameLayerState::CursorMarker;
                                }
                                if self.inline_depth != 0 {
                                    ctrl.end_analysis();
                                }
                            } else if self.inline_depth == 0 {
                                self.inline_depth = 1;
                                self.inline_limit = 12;
                                self.first_jump = true;
                                self.current_func = dest;
                                ctrl.analyze_with_current_state(self, dest);
                                self.first_jump = false;
                                self.inline_limit = 0;
                                self.inline_depth = 0;
                            } else if self.result.prepare_draw_image.is_some() {
                                // Track calls for draw_terrain
                                self.call_tracker.add_call(ctrl, dest);
                            }
                        }
                    }
                    Operation::Jump { condition, .. } => {
                        // Check for draw_terrain (Jump on is_paused)
                        if self.first_jump &&
                            self.result.prepare_draw_image.is_some() &&
                            self.inline_depth == 1
                        {
                            self.first_jump = false;
                            let ctx = ctrl.ctx();
                            let condition = ctrl.resolve(condition);
                            if let Some((val, _)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                                let val =
                                    self.call_tracker.resolve_calls_with_branch_limit(val, 4);
                                if val == self.is_paused {
                                    self.result.draw_terrain = Some(self.current_func);
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                    _ => (),
                }
            }
            DrawGameLayerState::CursorMarker => {
                let draw_image = match self.result.draw_image {
                    Some(s) => s,
                    None => return,
                };
                // Cursor marker.
                // Search for draw_image call with this = cursor_marker.sprite.last_overlay
                // Inline from 0 -> 1 unconditionally, 1 -> 2 if this could be cursor_marker.sprite
                ctrl.aliasing_memory_fix(op);
                match *op {
                    Operation::Call(dest) => {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            let this = ctrl.resolve_register(1);
                            if dest == draw_image {
                                let offset = self.sprite_first_overlay_offset +
                                    E::VirtualAddress::SIZE;
                                let cursor_marker = ctrl.if_mem_word_offset(this, offset.into())
                                    .and_then(|sprite| {
                                        let sprite_offset = E::struct_layouts().unit_sprite();
                                        ctrl.if_mem_word_offset(sprite, sprite_offset)
                                    });
                                if let Some(cursor_marker) = cursor_marker {
                                    self.result.cursor_marker = Some(cursor_marker);
                                    ctrl.end_analysis();
                                }
                            } else {
                                let should_inline = self.inline_depth == 0 ||
                                    (self.inline_depth == 1 && {
                                        let sprite_offset = E::struct_layouts().unit_sprite();
                                        ctrl.if_mem_word_offset(this, sprite_offset).is_some()
                                    });
                                if should_inline {
                                    self.inline_depth += 1;
                                    let old_inline_limit = self.inline_limit;
                                    if self.inline_depth == 1 {
                                        self.inline_limit = 16;
                                    }
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth -= 1;
                                    self.inline_limit = old_inline_limit;
                                    if self.result.cursor_marker.is_some() {
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
    }
}

pub(crate) fn analyze_render_screen<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    render_screen: E::VirtualAddress,
) -> RenderScreen<'e, E> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut result = RenderScreen {
        config_vsync_value: None,
        get_render_target: None,
        clear_render_target: None,
        renderer: None,
        draw_commands: None,
    };

    let mut analyzer = AnalyzeRenderScreen::<E> {
        result: &mut result,
        rdata: actx.binary_sections.rdata,
        state: RenderScreenState::FindCmpZero,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
        float_eq_tracker: FloatEqTracker::new(ctx),
        vsync_candidate: None,
        get_render_target_candidate: None,
        inline_depth: 0,
        inline_limit: 0,
        seen_funcs: HashSet::with_capacity_and_hasher(0x80, Default::default()),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, render_screen);
    analysis.analyze(&mut analyzer);

    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum RenderScreenState {
    /// Find comparision of float == 0.0, follow path where it is true
    /// (sd_hd_fade_amount == 0.0 comparision to skip queueing second set of draw commands
    /// with the other asset type so they can be blended together)
    FindCmpZero,
    /// After the jump, there should be the following function calls
    /// finish_draw() (small function, may be inlined) {
    ///     cap_fps(); (only called from finish_draw, may be inlined when finish_draw is not)
    ///     flush_frame();
    ///     something_minor();
    /// }
    /// cap_fps does get_vsync_value() == -1 and get_vsync_value() == 1 jumps
    FindVsyncJump,
    /// flush_frame will do
    /// clear_render_targets() (usually inlined) {
    ///     clear_render_target(get_render_target(0))
    ///     clear_render_target(get_render_target(1))
    ///     clear_render_target(get_render_target(2))
    /// }
    /// Find that. Specifically detect one with arg2
    RenderTargets,
    /// Find renderer.vtable[7](renderer, draw_commands, _, _)
    /// May be inner function of flush_frame
    Draw,
}

struct AnalyzeRenderScreen<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut RenderScreen<'e, E>,
    rdata: &'a BinarySection<E::VirtualAddress>,
    state: RenderScreenState,
    call_tracker: CallTracker<'acx, 'e, E>,
    float_eq_tracker: FloatEqTracker<'e>,
    vsync_candidate: Option<Operand<'e>>,
    get_render_target_candidate: Option<E::VirtualAddress>,
    inline_depth: u8,
    inline_limit: u8,
    /// Used to avoid unnecessarily repeated inlining into child functions.
    /// All ones we care about will not have been seen before.
    seen_funcs: HashSet<OperandHashByAddress<'e>>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    AnalyzeRenderScreen<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let mut call_was_seen = false;
        if let Operation::Call(dest) = *op {
            call_was_seen = !self.seen_funcs.insert(dest.hash_by_address());
        }
        ctrl.aliasing_memory_fix(op);
        match self.state {
            RenderScreenState::FindCmpZero => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    match self.float_eq_tracker.check_jump(condition) {
                        FloatCmpJump::Done(a, b, jump) => {
                            if resolve_rdata_const(a, self.rdata) == Some(0) ||
                                resolve_rdata_const(b, self.rdata) == Some(0)
                            {
                                let eq_zero_branch = match jump {
                                    true => match ctrl.resolve_va(to) {
                                        Some(s) => s,
                                        None => return,
                                    },
                                    false => ctrl.current_instruction_end(),
                                };
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_address(eq_zero_branch);
                                self.state = RenderScreenState::FindVsyncJump;
                            }
                        }
                        FloatCmpJump::ContinueAt(jump) => {
                            let next = match jump {
                                true => match ctrl.resolve_va(to) {
                                    Some(s) => s,
                                    None => return,
                                },
                                false => ctrl.current_instruction_end(),
                            };
                            ctrl.continue_at_address(next);
                        }
                        FloatCmpJump::Nothing => (),
                    }
                }
            }
            RenderScreenState::FindVsyncJump => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if !call_was_seen && self.inline_depth < 2 {
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if self.state != RenderScreenState::FindVsyncJump {
                                if self.inline_depth >= 2 {
                                    ctrl.end_analysis();
                                }
                                return;
                            }
                        }
                        self.call_tracker.add_call(ctrl, dest);
                    }
                } else if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    let result = condition.if_arithmetic_eq_neq()
                        .and_then(|x| {
                            let c = x.1.if_constant()?;
                            if c == 1 || c == 0xffff_ffff {
                                Some((x.0, x.2))
                            } else {
                                None
                            }
                        });
                    if let Some((vsync, jump_if_eq)) = result {
                        if let Some(old) = self.vsync_candidate {
                            if old == vsync {
                                let value = Operand::and_masked(vsync).0;
                                if let Some(c) = value.if_custom() {
                                    if let Some(func) = self.call_tracker.custom_id_to_func(c) {
                                        self.result.config_vsync_value = Some(func);
                                    }
                                }
                                // Continue at point after fps limiting
                                let addr = match jump_if_eq {
                                    true => match ctrl.resolve_va(to) {
                                        Some(s) => s,
                                        None => return,
                                    },
                                    false => ctrl.current_instruction_end(),
                                };
                                ctrl.clear_unchecked_branches();
                                ctrl.continue_at_address(addr);
                                self.state = RenderScreenState::RenderTargets;
                                if self.inline_depth >= 2 {
                                    ctrl.end_analysis();
                                    self.inline_limit = 1 + 2;
                                } else {
                                    self.inline_limit = self.inline_depth + 2;
                                }
                            }
                        } else {
                            self.vsync_candidate = Some(vsync);
                        }
                    }
                }
            }
            RenderScreenState::RenderTargets => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve_arg(0);
                        let ctx = ctrl.ctx();
                        if arg1.if_constant() == Some(2) {
                            self.get_render_target_candidate = Some(dest);
                            ctrl.do_call_with_result(ctx.custom(0));
                        } else {
                            let this = ctrl.resolve_register(1);
                            if this.if_custom() == Some(0) {
                                if let Some(get) = self.get_render_target_candidate {
                                    self.result.get_render_target = Some(get);
                                    self.result.clear_render_target = Some(dest);
                                    ctrl.clear_unchecked_branches();
                                    self.state = RenderScreenState::Draw;
                                    if self.inline_depth == self.inline_limit {
                                        ctrl.end_analysis();
                                    } else {
                                        self.inline_limit = self.inline_depth + 1;
                                    }
                                }
                            } else {
                                self.get_render_target_candidate = None;
                                if !call_was_seen && self.inline_depth < self.inline_limit {
                                    self.inline_depth += 1;
                                    ctrl.analyze_with_current_state(self, dest);
                                    self.inline_depth -= 1;
                                }
                            }
                        }
                    }
                }
            }
            RenderScreenState::Draw => {
                if self.result.renderer.is_some() {
                    ctrl.end_analysis();
                    return;
                }
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if !call_was_seen && self.inline_depth < self.inline_limit {
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                        }
                        self.call_tracker.add_call(ctrl, dest);
                    } else {
                        let dest = ctrl.resolve(dest);
                        let offset = 7 * E::VirtualAddress::SIZE;
                        let renderer = ctrl.if_mem_word_offset(dest, offset as u64)
                            .and_then(|x| ctrl.if_mem_word_offset(x, 0));
                        if let Some(renderer) = renderer {
                            let arg1 = ctrl.resolve_arg_thiscall(0);
                            let draw_commands = self.call_tracker.resolve_calls(arg1);
                            if is_global(draw_commands) {
                                self.result.draw_commands = Some(draw_commands);
                                self.result.renderer = Some(renderer);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_draw_terrain<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    draw_terrain: E::VirtualAddress,
    is_paused: Operand<'e>,
) -> DrawTerrain<'e, E> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut result = DrawTerrain {
        get_atlas_page_coords_for_terrain_tile: None,
    };

    let mut analyzer = AnalyzeDrawTerrain::<E> {
        result: &mut result,
        state: DrawTerrainState::FindIsPausedCheck,
        call_tracker: CallTracker::with_capacity(actx, 0x1000_0000, 0x20),
        inline_depth: 0,
        draw_tiles_depth: 0,
        is_paused,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, draw_terrain);
    analysis.analyze(&mut analyzer);

    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum DrawTerrainState {
    /// Find jump checking is_paused, follow true branch (Skip over water animation code)
    FindIsPausedCheck,
    /// Inline once to draw_terrain_tiles, verify from
    /// vx4_tiles_ids + game.screen_y * game_map_width + game.screen_x being calculated
    /// but not used before first jump.
    DrawTiles,
    /// Inline to
    /// -> draw_terrain_tile_row with arg3 = tile_ptr
    /// -> draw_terrain_tile with arg3 = tile
    /// (From same vx4 array), then find
    /// get_atlas_page_coords_for_terrain_tile(
    ///     this = stack object,
    ///     a1 = is_creep ? 5 : 1 (1 : 5?)
    ///     a2 = tile
    ///     a3 = stack vec4 { 0, 0, 0, 0 }
    /// )
    DrawTilesVerified,
}

struct AnalyzeDrawTerrain<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut DrawTerrain<'e, E>,
    state: DrawTerrainState,
    call_tracker: CallTracker<'acx, 'e, E>,
    inline_depth: u8,
    draw_tiles_depth: u8,
    is_paused: Operand<'e>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    AnalyzeDrawTerrain<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            DrawTerrainState::FindIsPausedCheck => {
                if let Operation::Jump { condition, to } = *op {
                    let condition = ctrl.resolve(condition);
                    if let Some((val, eq)) = condition.if_arithmetic_eq_neq_zero(ctx) {
                        let val =
                            self.call_tracker.resolve_calls_with_branch_limit(val, 4);
                        if val == self.is_paused {
                            ctrl.continue_at_neq_address(eq, to);
                            self.state = DrawTerrainState::DrawTiles;
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        self.call_tracker.add_call(ctrl, dest);
                    }
                }
            }
            DrawTerrainState::DrawTiles => {
                if let Operation::Call(dest) = *op {
                    if self.inline_depth == 0 {
                        if let Some(dest) = ctrl.resolve_va(dest) {
                            self.inline_depth = 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth = 0;
                            if self.state != DrawTerrainState::DrawTiles {
                                ctrl.end_analysis();
                            }
                        }
                    }
                } else if let Operation::Jump { .. } = *op {
                    if self.inline_depth != 0 {
                        ctrl.end_analysis();
                    }
                } else if let Operation::Move(ref dest, value) = *op {
                    let value = ctrl.resolve(value);
                    // vx4_map_tiles + ([game_e0] + [game_e4] * [game_e2]) * 2
                    let is_game_screen_xy_ptr = value.if_arithmetic_add()
                        .and_either(|x| {
                            // Scarf doesn't currently remove mask from sext_32_64(x & ffff_ffff)
                            // Maybe it should?
                            x.if_arithmetic_mul_const(2)?
                                .unwrap_sext()
                                .unwrap_and_mask()
                                .if_arithmetic_add()
                                .and_either(|x| {
                                    x.if_arithmetic_mul()
                                        .and_either_other(|x| x.if_mem16_offset(0xe2))?
                                        .if_mem16_offset(0xe4)
                                })
                        })
                        .is_some();
                    if is_game_screen_xy_ptr {
                        ctrl.skip_operation();
                        ctrl.move_unresolved(dest, ctx.custom(0));
                        self.draw_tiles_depth = self.inline_depth;
                        self.state = DrawTerrainState::DrawTilesVerified;
                    }
                }
            }
            DrawTerrainState::DrawTilesVerified => {
                fn is_tile<'e>(op: Operand<'e>) -> bool {
                    op.if_arithmetic_and_const(0x7fff)
                        .and_then(|x| x.if_mem16()?.address().0.if_custom()) == Some(0)
                }

                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ok = {
                                let arg3 = ctrl.resolve_arg_thiscall(2);
                                let mem = ctx.mem_access(arg3, 0, MemAccessSize::Mem64);
                                ctrl.read_memory(&mem) == ctx.const_0()
                            } &&
                            is_tile(ctrl.resolve_arg_thiscall(1));
                        if ok {
                            self.result.get_atlas_page_coords_for_terrain_tile = Some(dest);
                            ctrl.end_analysis();
                            return;
                        }
                        let inline_depth = self.inline_depth - self.draw_tiles_depth;
                        if inline_depth < 2 {
                            let mut inline = false;
                            if inline_depth < 1 {
                                // draw_terrain_tile_row
                                let arg2 = ctrl.resolve_arg(1);
                                inline = arg2.if_custom() == Some(0);
                            }
                            if !inline {
                                // draw_terrain_tile inlining
                                let arg3 = ctrl.resolve_arg(2);
                                inline = is_tile(arg3);
                            }
                            if inline {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.result.get_atlas_page_coords_for_terrain_tile.is_some() {
                                    ctrl.end_analysis();
                                }
                                return;
                            }
                        }

                    }
                }
            }
        }
    }
}
