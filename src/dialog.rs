use bumpalo::collections::Vec as BumpVec;
use fxhash::FxHashMap;

use std::convert::TryInto;

use scarf::analysis::{self, AnalysisState, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{ArithOpType, MemAccess, MemAccessSize};
use scarf::{BinaryFile, DestOperand, Operation, Operand, OperandCtx};

use crate::{
    AnalysisCtx, ArgCache, ControlExt, EntryOf, OperandExt, OptionExt, single_result_assign,
    StringRefs, FunctionFinder, bumpvec_with_capacity, if_arithmetic_eq_neq, is_global,
    is_stack_address,
};
use crate::struct_layouts;

#[derive(Clone)]
pub struct TooltipRelated<'e, Va: VirtualAddress> {
    pub tooltip_draw_func: Option<Operand<'e>>,
    pub current_tooltip_ctrl: Option<Operand<'e>>,
    pub graphic_layers: Option<Operand<'e>>,
    pub layout_draw_text: Option<Va>,
    pub draw_f10_menu_tooltip: Option<Va>,
    pub draw_tooltip_layer: Option<Va>,
}

#[derive(Clone, Default)]
pub struct ButtonDdsgrps<'e> {
    pub cmdicons: Option<Operand<'e>>,
    pub cmdbtns: Option<Operand<'e>>,
}

#[derive(Clone)]
pub struct MouseXy<'e, Va: VirtualAddress> {
    pub x_var: Option<Operand<'e>>,
    pub y_var: Option<Operand<'e>>,
    pub x_func: Option<Va>,
    pub y_func: Option<Va>,
}

#[derive(Clone)]
pub struct MultiWireframes<'e, Va: VirtualAddress> {
    pub grpwire_grp: Option<Operand<'e>>,
    pub grpwire_ddsgrp: Option<Operand<'e>>,
    pub tranwire_grp: Option<Operand<'e>>,
    pub tranwire_ddsgrp: Option<Operand<'e>>,
    pub status_screen: Option<Operand<'e>>,
    pub status_screen_event_handler: Option<Va>,
    pub init_status_screen: Option<Va>,
}

pub(crate) struct UiEventHandlers<'e, Va: VirtualAddress> {
    pub reset_ui_event_handlers: Option<Va>,
    pub default_scroll_handler: Option<Va>,
    pub global_event_handlers: Option<Operand<'e>>,
}

pub(crate) struct RunMenus<Va: VirtualAddress> {
    pub set_music: Option<Va>,
    pub pre_mission_glue: Option<Va>,
    pub show_mission_glue: Option<Va>,
}

pub(crate) struct RunDialog<Va: VirtualAddress> {
    pub run_dialog: Option<Va>,
    pub glucmpgn_event_handler: Option<Va>,
}

pub(crate) struct GluCmpgnEvents<'e, Va: VirtualAddress> {
    pub swish_in: Option<Va>,
    pub swish_out: Option<Va>,
    pub dialog_return_code: Option<Operand<'e>>,
}

impl<'e, Va: VirtualAddress> Default for MultiWireframes<'e, Va> {
    fn default() -> Self {
        MultiWireframes {
            grpwire_grp: None,
            grpwire_ddsgrp: None,
            tranwire_grp: None,
            tranwire_ddsgrp: None,
            status_screen: None,
            status_screen_event_handler: None,
            init_status_screen: None,
        }
    }
}

pub(crate) fn run_dialog<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> RunDialog<E::VirtualAddress> {
    let mut result = RunDialog {
        run_dialog: None,
        glucmpgn_event_handler: None,
    };
    let ctx = analysis.ctx;

    let binary = analysis.binary;
    let funcs = functions.functions();
    let mut str_refs = functions.string_refs(analysis, b"rez\\glucmpgn");
    if str_refs.is_empty() {
        str_refs = functions.string_refs(analysis, b"glucmpgn.ui");
    }
    let args = &analysis.arg_cache;
    for str_ref in &str_refs {
        crate::entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            let mut analyzer = RunDialogAnalyzer {
                string_address: str_ref.string_address,
                result: &mut result,
                args,
            };

            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if result.run_dialog.is_some() {
                EntryOf::Ok(())
            } else {
                EntryOf::Retry
            }
        });
        if result.run_dialog.is_some() {
            break;
        }
    }
    result
}

struct RunDialogAnalyzer<'exec, 'b, E: ExecutionState<'exec>> {
    string_address: E::VirtualAddress,
    args: &'b ArgCache<'exec, E>,
    result: &'b mut RunDialog<E::VirtualAddress>,
}

impl<'exec, 'b, E: ExecutionState<'exec>> scarf::Analyzer<'exec> for
    RunDialogAnalyzer<'exec, 'b, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation<'exec>) {
        let ctx = ctrl.ctx();
        match *op {
            Operation::Call(to) => {
                let arg1 = ctrl.resolve(self.args.on_call(0));
                let arg2 = ctrl.resolve(self.args.on_call(1));
                let arg3 = ctrl.resolve(self.args.on_call(2));
                let arg4 = ctrl.resolve(self.args.on_call(3));
                let arg1_is_dialog_ptr = arg1.if_custom() == Some(0);
                if arg1_is_dialog_ptr {
                    // run_dialog(dialog, 0, event_handler)
                    let arg2_zero = arg2 == ctx.const_0();
                    let arg3_ptr = arg3.if_constant().filter(|&c| c != 0);
                    if arg2_zero {
                        if let Some(arg3) = arg3_ptr {
                            if let Some(to) = ctrl.resolve_va(to) {
                                if single_result_assign(Some(to), &mut self.result.run_dialog) {
                                    ctrl.end_analysis();
                                }
                                self.result.glucmpgn_event_handler =
                                    Some(E::VirtualAddress::from_u64(arg3));
                                return;
                            }
                        }
                    }
                }
                let arg1_is_string_ptr = {
                    arg1.if_constant()
                        .filter(|&c| c == self.string_address.as_u64())
                        .is_some()
                };
                if arg1_is_string_ptr {
                    ctrl.do_call_with_result(ctx.custom(0));
                }
                let arg4_is_string_ptr = arg4.if_constant()
                    .filter(|&c| c == self.string_address.as_u64())
                    .is_some();
                let arg2_is_string_ptr = arg2.if_constant()
                    .filter(|&c| c == self.string_address.as_u64())
                    .is_some();
                let arg3_value = ctrl.read_memory(arg3, E::WORD_SIZE);
                let arg3_inner = ctrl.read_memory(arg3_value, E::WORD_SIZE);
                // Can be join(String *out, String *path1, String *path2)
                let arg3_is_string_struct_ptr = arg3_inner.if_memory()
                    .map(|x| x.address)
                    .and_then(|x| x.if_constant())
                    .filter(|&x| x == self.string_address.as_u64())
                    .is_some();
                if arg2_is_string_ptr || arg4_is_string_ptr || arg3_is_string_struct_ptr {
                    // String creation function returns eax = arg1
                    ctrl.do_call_with_result(arg1);
                    // Mem[string + 0] is character data
                    let dest2 = DestOperand::from_oper(ctrl.mem_word(arg1));
                    let state = ctrl.exec_state();
                    state.move_resolved(&dest2, ctx.constant(self.string_address.as_u64()));
                }
            }
            _ => (),
        }
    }
}

/// Assuming that `func` calls the load_dialog function with a constant string somewhere in
/// arguments, returns the global variable(s) load_dialog's return value is stored to (if any)
pub(crate) fn find_dialog_global<'exec, E: ExecutionState<'exec>>(
    analysis: &AnalysisCtx<'exec, E>,
    func: E::VirtualAddress,
    str_ref: &StringRefs<E::VirtualAddress>,
) -> EntryOf<E::VirtualAddress> {
    let ctx = analysis.ctx;
    let return_marker = ctx.truncate(ctx.custom(0), E::VirtualAddress::SIZE as u8 * 8);
    let args = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(analysis.binary, ctx, func);
    let mut analyzer = DialogGlobalAnalyzer {
        result: EntryOf::Retry,
        after_call: false,
        path_string: None,
        str_ref,
        ctx,
        args,
        return_marker,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct DialogGlobalAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<E::VirtualAddress>,
    after_call: bool,
    path_string: Option<Operand<'e>>,
    str_ref: &'a StringRefs<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
    args: &'a ArgCache<'e, E>,
    return_marker: Operand<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for DialogGlobalAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() == self.str_ref.use_address {
            self.result = EntryOf::Stop;
        }
        if self.after_call {
            // Has to be done like this since just writing to eax before call would
            // just get overwritten later
            let eax = DestOperand::Register64(scarf::operand::Register(0));
            let state = ctrl.exec_state();
            state.move_to(&eax, self.return_marker);
            self.after_call = false;
        }
        if let Some(path_string) = self.path_string.take() {
            let dest = DestOperand::Register64(scarf::operand::Register(0));
            let dest2 = DestOperand::from_oper(ctrl.mem_word(path_string));
            let state = ctrl.exec_state();
            // String creation function returns eax = arg1
            state.move_resolved(&dest, path_string);
            // Mem[string + 0] is character data
            state.move_resolved(
                &dest2,
                self.ctx.constant(self.str_ref.string_address.as_u64()),
            );
        }
        match *op {
            Operation::Call(_dest) => {
                let string_in_args = (0..4).any(|i| {
                    ctrl.resolve(self.args.on_call(i)).if_constant() ==
                        Some(self.str_ref.string_address.as_u64())
                });
                if string_in_args {
                    let arg2 = ctrl.resolve(self.args.on_call(1));
                    let arg4 = ctrl.resolve(self.args.on_call(3));
                    let arg4_is_string_ptr = arg4.if_constant()
                        .filter(|&c| c == self.str_ref.string_address.as_u64())
                        .is_some();
                    let arg2_is_string_ptr = arg2.if_constant()
                        .filter(|&c| c == self.str_ref.string_address.as_u64())
                        .is_some();
                    // Check for either creating a string (1.23.2+) or const char ptr
                    if arg2_is_string_ptr || arg4_is_string_ptr {
                        let arg1 = ctrl.resolve(self.args.on_call(0));
                        self.path_string = Some(arg1);
                    } else {
                        self.after_call = true;
                    }
                } else {
                    let arg3 = ctrl.resolve(self.args.on_call(2));
                    let arg3_value = ctrl.read_memory(arg3, E::WORD_SIZE);
                    let arg3_inner = ctrl.read_memory(arg3_value, E::WORD_SIZE);
                    // Can be join(String *out, String *path1, String *path2)
                    let arg3_is_string_struct_ptr = arg3_inner.if_memory()
                        .map(|x| x.address)
                        .and_then(|x| x.if_constant())
                        .filter(|&x| x == self.str_ref.string_address.as_u64())
                        .is_some();
                    if arg3_is_string_struct_ptr {
                        let arg1 = ctrl.resolve(self.args.on_call(0));
                        self.path_string = Some(arg1);
                    }
                }
            }
            Operation::Move(ref dest, val, _condition) => {
                let resolved = ctrl.resolve(val);
                if resolved == self.return_marker {
                    if let DestOperand::Memory(ref mem) = *dest {
                        if let Some(c) = ctrl.resolve(mem.address).if_constant() {
                            self.result = EntryOf::Ok(E::VirtualAddress::from_u64(c));
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn spawn_dialog<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    // This is currently just copypasted from run_dialog, it ends up working fine as the
    // signature and dialog init patterns are same between run (blocking) and spawn (nonblocking).
    // If it won't in future then this should be refactored to have its own Analyzer
    let ctx = analysis.ctx;

    let binary = analysis.binary;
    let funcs = functions.functions();
    let mut str_refs = functions.string_refs(analysis, b"rez\\statlb");
    if str_refs.is_empty() {
        str_refs = functions.string_refs(analysis, b"statlb.ui");
    }
    let args = &analysis.arg_cache;
    let mut result = RunDialog {
        run_dialog: None,
        glucmpgn_event_handler: None,
    };
    for str_ref in &str_refs {
        crate::entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            let mut analyzer = RunDialogAnalyzer {
                string_address: str_ref.string_address,
                result: &mut result,
                args,
            };

            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if result.run_dialog.is_some() {
                EntryOf::Ok(())
            } else {
                EntryOf::Retry
            }
        });
        if result.run_dialog.is_some() {
            break;
        }
    }
    result.run_dialog
}

pub(crate) fn tooltip_related<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    spawn_dialog: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> TooltipRelated<'e, E::VirtualAddress> {
    let mut result = TooltipRelated {
        tooltip_draw_func: None,
        current_tooltip_ctrl: None,
        graphic_layers: None,
        layout_draw_text: None,
        draw_tooltip_layer: None,
        draw_f10_menu_tooltip: None,
    };

    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let funcs = functions.functions();
    let mut str_refs = functions.string_refs(analysis, b"rez\\stat_f10");
    if str_refs.is_empty() {
        str_refs = functions.string_refs(analysis, b"stat_f10.ui");
    }
    for str_ref in &str_refs {
        crate::entry_of_until(binary, funcs, str_ref.use_address, |entry| {
            let arg_cache = &analysis.arg_cache;
            let exec_state = E::initial_state(ctx, binary);
            let mut analysis = FuncAnalysis::custom_state(
                binary,
                ctx,
                entry,
                exec_state,
                TooltipState::FindEventHandler,
            );
            let mut analyzer = TooltipAnalyzer {
                result: &mut result,
                arg_cache,
                entry_of: EntryOf::Retry,
                spawn_dialog,
                inline_depth: 0,
            };
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        });
        if result.tooltip_draw_func.is_some() {
            break;
        }
    }
    result
}

#[derive(Clone)]
enum TooltipState<'e, E: ExecutionState<'e>> {
    FindEventHandler,
    FindTooltipCtrl(FindTooltipCtrlState<'e, E>),
    FindLayoutText,
}

// set_tooltip function writes the following variables:
//   current_tooltip_ctrl = ctrl (undef for this analysis)
//   tooltip_draw_func = func
//   graphic_layers[1].enable = 1
//   graphic_layers[1].func = func
//   (And some zeroes and width/height to layer 1 as well)
#[derive(Clone, Eq)]
struct FindTooltipCtrlState<'e, E: ExecutionState<'e>> {
    tooltip_ctrl: Option<Operand<'e>>,
    one: Option<Operand<'e>>,
    func1: Option<(Operand<'e>, E::VirtualAddress)>,
    func2: Option<(Operand<'e>, E::VirtualAddress)>,
}

// Derive doesn't work for these due to E
impl<'e, E: ExecutionState<'e>> Copy for TooltipState<'e, E> { }
impl<'e, E: ExecutionState<'e>> Copy for FindTooltipCtrlState<'e, E> { }

impl<'e, E: ExecutionState<'e>> PartialEq for FindTooltipCtrlState<'e, E> {
    fn eq(&self, other: &Self) -> bool {
        match self {
            FindTooltipCtrlState {
                tooltip_ctrl,
                one,
                func1,
                func2,
            } => {
                *tooltip_ctrl == other.tooltip_ctrl &&
                    *one == other.one &&
                    *func1 == other.func1 &&
                    *func2 == other.func2
            }
        }
    }
}


impl<'e, E: ExecutionState<'e>> FindTooltipCtrlState<'e, E> {
    fn check_ready(
        &self,
        ctx: OperandCtx<'e>,
        result: &mut TooltipRelated<'e, E::VirtualAddress>,
    ) {
        let tooltip_ctrl = match self.tooltip_ctrl {
            Some(s) => s,
            None => return,
        };
        let one = match self.one {
            Some(s) => s,
            None => return,
        };
        let func1 = match self.func1 {
            Some(s) => s,
            None => return,
        };
        let func2 = match self.func2 {
            Some(s) => s,
            None => return,
        };
        // Assuming that 1 gets stored to graphic_layers[1].should_draw (Offset 0 in struct),
        // and one of the two func ptrs is graphic_layers[1].draw_func
        let expected_draw_func = ctx.add_const(
            one,
            struct_layouts::graphic_layer_draw_func::<E::VirtualAddress>(),
        );
        let (draw_tooltip_layer, other) = if expected_draw_func == func1.0 {
            (func1.1, func2)
        } else if expected_draw_func == func2.0 {
            (func2.1, func1)
        } else {
            return;
        };
        result.tooltip_draw_func = Some(E::operand_mem_word(ctx, other.0));
        result.draw_f10_menu_tooltip = Some(other.1);
        result.graphic_layers = Some(ctx.sub_const(
            one,
            struct_layouts::graphic_layer_size::<E::VirtualAddress>(),
        ));
        result.current_tooltip_ctrl = Some(tooltip_ctrl);
        result.draw_tooltip_layer = Some(draw_tooltip_layer);
    }
}

struct TooltipAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut TooltipRelated<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    entry_of: EntryOf<()>,
    spawn_dialog: E::VirtualAddress,
    inline_depth: u8,
}

impl<'e, E: ExecutionState<'e>> AnalysisState for TooltipState<'e, E> {
    fn merge(&mut self, newer: Self) {
        use self::TooltipState::*;
        match (self, newer) {
            (&mut FindTooltipCtrl(ref mut a), FindTooltipCtrl(ref b)) => {
                if a != b {
                    *a = FindTooltipCtrlState {
                        tooltip_ctrl: None,
                        one: None,
                        func1: None,
                        func2: None,
                    }
                }
            }
            (_, _) => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for TooltipAnalyzer<'a, 'e, E> {
    type State = TooltipState<'e, E>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *ctrl.user_state() {
            TooltipState::FindEventHandler => self.state1(ctrl, op),
            TooltipState::FindTooltipCtrl(..) => self.state2(ctrl, op),
            TooltipState::FindLayoutText => self.state3(ctrl, op),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> TooltipAnalyzer<'a, 'e, E> {
    fn state1(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let dest = ctrl.resolve(dest);
                if dest.if_constant() == Some(self.spawn_dialog.as_u64()) {
                    if let Some(addr) = ctrl.resolve_va(self.arg_cache.on_call(2)) {
                        *ctrl.user_state() = TooltipState::FindTooltipCtrl(FindTooltipCtrlState {
                            tooltip_ctrl: None,
                            one: None,
                            func1: None,
                            func2: None,
                        });
                        // Set event type to 0x3, causing it to reach set_tooltip
                        // Event ptr is arg2
                        let ctx = ctrl.ctx();
                        let exec_state = ctrl.exec_state();
                        exec_state.move_to(
                            &DestOperand::from_oper(self.arg_cache.on_call(1)),
                            ctx.custom(0),
                        );
                        exec_state.move_to(
                            &DestOperand::from_oper(self.arg_cache.on_call(0)),
                            ctx.custom(1),
                        );
                        let type_offset = struct_layouts::event_type::<E::VirtualAddress>();
                        exec_state.move_to(
                            &DestOperand::Memory(MemAccess {
                                address: ctx.add_const(ctx.custom(0), type_offset),
                                size: MemAccessSize::Mem16,
                            }),
                            ctx.constant(0x3),
                        );
                        ctrl.analyze_with_current_state(self, addr);
                        self.entry_of = EntryOf::Ok(());
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }

    fn state2(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) if self.inline_depth < 2 => {
                // set_tooltip arg2 is a fnptr (arg 1 child ctrl)
                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                if arg2.if_constant().is_none() {
                    // Alternatively just accept fn (ctrl, event)
                    if arg2.if_custom() != Some(0) || arg1.if_custom() != Some(1) {
                        return;
                    }
                }

                if let Some(dest) = ctrl.resolve_va(dest) {
                    let old_inline = self.inline_depth;
                    self.inline_depth += 1;
                    ctrl.analyze_with_current_state(self, dest);
                    self.inline_depth = old_inline;
                    if self.result.tooltip_draw_func.is_some() {
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Move(DestOperand::Memory(mem), value, None) => {
                let addr = ctrl.resolve(mem.address);
                if !is_global(addr) {
                    return;
                }
                let value = ctrl.resolve(value);
                let ctx = ctrl.ctx();
                if let TooltipState::FindTooltipCtrl(ref mut state) = ctrl.user_state() {
                    if value.is_undefined() {
                        if mem.size == E::WORD_SIZE {
                            state.tooltip_ctrl = Some(E::operand_mem_word(ctx, addr));
                        }
                    } else {
                        if let Some(c) = value.if_constant() {
                            if c == 1 && mem.size == MemAccessSize::Mem8 {
                                state.one = Some(addr);
                            }
                            if mem.size == E::WORD_SIZE {
                                if c > 0x1000 {
                                    let dest = E::VirtualAddress::from_u64(c);
                                    if state.func1.is_none() {
                                        state.func1 = Some((addr, dest));
                                    } else if state.func2.is_none() {
                                        state.func2 = Some((addr, dest));
                                    }
                                }
                            }
                        }
                    };
                    state.check_ready(ctx, &mut self.result);
                }
                if let Some(addr) = self.result.draw_f10_menu_tooltip {
                    self.inline_depth = 0;
                    *ctrl.user_state() = TooltipState::FindLayoutText;
                    ctrl.analyze_with_current_state(self, addr);
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }

    fn state3(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let dest = ctrl.resolve(dest);
                if let Some(dest) = dest.if_constant().map(E::VirtualAddress::from_u64) {
                    // text_layout_draw args are for this f10 menu tooltip
                    // 2, 0, char *, 0, 0, 0, 1, 1
                    let vals = [2, 0, 0, 0, 0, 0, 1, 1];
                    let ok = (0..8).all(|i| {
                        if i == 2 {
                            true
                        } else {
                            let ctx = ctrl.ctx();
                            let arg = ctrl.resolve(self.arg_cache.on_call(i));
                            match ctx.and_const(arg, 0xff).if_constant() {
                                Some(s) => s as u8 == vals[i as usize],
                                _ => false,
                            }
                        }
                    });
                    if ok {
                        self.result.layout_draw_text = Some(dest);
                        ctrl.end_analysis();
                        return;
                    }
                    if self.inline_depth == 0 {
                        self.inline_depth = 1;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth = 0;
                        if self.result.layout_draw_text.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn draw_graphic_layers<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    graphic_layers: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<E::VirtualAddress> {
    let graphic_layers_addr = E::VirtualAddress::from_u64(graphic_layers.if_constant()?);

    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let funcs = functions.functions();
    let global_refs = functions.find_functions_using_global(analysis, graphic_layers_addr);
    let mut result = None;
    let expected_call_addr = ctx.mem32(ctx.add_const(graphic_layers, 0x14 * 7 + 0x10));
    for func in &global_refs {
        let val = crate::entry_of_until(binary, &funcs, func.use_address, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = IsDrawGraphicLayers::<E> {
                entry_of: EntryOf::Retry,
                use_address: func.use_address,
                expected_call_addr,
            };
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        }).into_option_with_entry().map(|x| x.0);
        if single_result_assign(val, &mut result) {
            break;
        }
    }
    result
}

struct IsDrawGraphicLayers<'e, E: ExecutionState<'e>> {
    entry_of: EntryOf<()>,
    use_address: E::VirtualAddress,
    expected_call_addr: Operand<'e>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for IsDrawGraphicLayers<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() <= self.use_address &&
            ctrl.current_instruction_end() > self.use_address
        {
            self.entry_of = EntryOf::Stop;
        }
        match *op {
            Operation::Call(dest) => {
                let dest = ctrl.resolve(dest);
                if dest == self.expected_call_addr {
                    self.entry_of = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn button_ddsgrps<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    unit_status_funcs: E::VirtualAddress,
) -> ButtonDdsgrps<'e> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;

    let mut result = ButtonDdsgrps {
        cmdbtns: None,
        cmdicons: None,
    };

    let gateway_status = match binary.read_address(unit_status_funcs + 0xa0 * 0xc + 0x8).ok() {
        Some(s) => s,
        None => return result,
    };
    // Search for [Control.user_pointer].field0 = *cmdicons_ddsgrp
    // Right before that it sets Control.user_u16 to 0xc
    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, gateway_status);
    let mut analyzer = CmdIconsDdsGrp::<E> {
        result: &mut result,
        inline_depth: 0,
        arg_cache,
        current_function_u16_param_set: None,
        u16_param_offset: 0,
    };
    analysis.analyze(&mut analyzer);
    result
}

struct CmdIconsDdsGrp<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut ButtonDdsgrps<'e>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    // Base operand, offset
    current_function_u16_param_set: Option<(Operand<'e>, u16)>,
    u16_param_offset: u16,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for CmdIconsDdsGrp<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.inline_depth < 5 {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        // Only inline when status_screen dialog is being passed to the function
                        // as arg1
                        if arg1 == self.arg_cache.on_entry(0) {
                            self.inline_depth += 1;
                            let u16_param_set = self.current_function_u16_param_set;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            self.current_function_u16_param_set = u16_param_set;
                        } else if self.current_function_u16_param_set.is_some() {
                            let u16_param_set = self.current_function_u16_param_set;
                            self.current_function_u16_param_set = None;
                            ctrl.inline(self, dest);
                            ctrl.skip_operation();
                            let ctx = ctrl.ctx();
                            let eax = ctrl.resolve(ctx.register(0));
                            if eax.if_constant().is_some() &&
                                ctrl.read_memory(eax, E::WORD_SIZE).is_undefined()
                            {
                                // hackfix to fix get_ddsgrp() static constructor
                                // writing 0 to [ddsgrp], causing it be undefined.
                                // Make it back [ddsgrp]
                                let val = ctrl.mem_word(eax);
                                let exec_state = ctrl.exec_state();
                                exec_state.move_resolved(&DestOperand::from_oper(val), val);
                            }
                            self.current_function_u16_param_set = u16_param_set;
                        }
                        if self.result.cmdbtns.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(mem), val, None) => {
                let dest = ctrl.resolve(mem.address);
                let val = ctrl.resolve(val);
                if mem.size == MemAccessSize::Mem16 {
                    if let Some(c) = val.if_constant() {
                        if self.result.cmdicons.is_none() && c == 0xc {
                            let is_u16_move = dest.if_arithmetic_add()
                                .and_then(|(l, r)| {
                                    let c = r.if_constant()?;
                                    match c {
                                        // 0x26 is older offset
                                        0x3e | 0x26 => Some((l, c as u16)),
                                        _ => None,
                                    }
                                });
                            if let Some(base) = is_u16_move {
                                self.current_function_u16_param_set = Some(base);
                            }
                        } else if self.result.cmdicons.is_some() && c == 0x2 {
                            let is_u16_move = dest.if_arithmetic_add()
                                .and_then(|(l, r)| {
                                    let c = r.if_constant()?;
                                    match c == self.u16_param_offset as u64 {
                                        true => Some((l, c as u16)),
                                        false => None,
                                    }
                                });
                            if let Some(base) = is_u16_move {
                                self.current_function_u16_param_set = Some(base);
                            }
                        }
                    }
                }
                if mem.size == MemAccessSize::Mem32 {
                    if let Some((base, offset)) = self.current_function_u16_param_set {
                        let ok = ctrl.if_mem_word(dest)
                            .and_then(|x| x.if_arithmetic_add())
                            .filter(|&(l, _)| l == base)
                            .and_then(|(_, r)| r.if_constant())
                            .filter(|&c| c == offset as u64 + 2)
                            .is_some();
                        if ok {
                            if let Some(outer) = ctrl.if_mem_word(val) {
                                match self.result.cmdicons {
                                    None => {
                                        self.result.cmdicons = Some(outer);
                                        self.u16_param_offset = offset;
                                        ctrl.end_analysis();
                                    }
                                    Some(s) => {
                                        if s != outer {
                                            self.result.cmdbtns = Some(outer);
                                            ctrl.end_analysis();
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn mouse_xy<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    run_dialog: E::VirtualAddress,
) -> MouseXy<'e, E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let bump = &analysis.bump;

    let mut result = MouseXy {
        x_var: None,
        y_var: None,
        x_func: None,
        y_func: None,
    };

    // Search for [Control.user_pointer].field0 = *cmdicons_ddsgrp
    // Right before that it sets Control.user_u16 to 0xc
    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, run_dialog);
    let mut analyzer = MouseXyAnalyzer::<E> {
        result: &mut result,
        inline_depth: 0,
        arg_cache,
        funcs: bumpvec_with_capacity(32, bump),
    };
    analysis.analyze(&mut analyzer);
    result
}

struct MouseXyAnalyzer<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut MouseXy<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    funcs: BumpVec<'acx, E::VirtualAddress>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    MouseXyAnalyzer<'a, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let dest = ctrl.resolve(dest);
                if let Some(dest) = dest.if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.inline_depth < 2 {
                        self.inline_depth += 1;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth -= 1;
                        if self.result.x_var.is_some() || self.result.x_func.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                    ctrl.skip_operation();
                    let ctx = ctrl.ctx();
                    let custom = ctx.custom(self.funcs.len() as u32);
                    self.funcs.push(dest);
                    let exec_state = ctrl.exec_state();
                    exec_state.move_to(
                        &DestOperand::Register64(scarf::operand::Register(0)),
                        custom,
                    );
                } else {
                    let ctx = ctrl.ctx();
                    let is_calling_event_handler = ctrl.if_mem_word(dest)
                        .and_then(|addr| addr.if_arithmetic_add())
                        .and_then(|(_, r)| r.if_constant())
                        .filter(|&c| c > 0x28 && c < 0x80)
                        .is_some();
                    if is_calling_event_handler {
                        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                        let x_offset = struct_layouts::event_mouse_xy::<E::VirtualAddress>();
                        let x = ctrl.read_memory(
                            ctx.add_const(arg2, x_offset),
                            MemAccessSize::Mem16,
                        );
                        let y = ctrl.read_memory(
                            ctx.add_const(arg2, x_offset + 2),
                            MemAccessSize::Mem16,
                        );
                        if let Some(c) = Operand::and_masked(x).0.if_custom() {
                            self.result.x_func = Some(self.funcs[c as usize]);
                        } else {
                            self.result.x_var = Some(x);
                        }
                        if let Some(c) = Operand::and_masked(y).0.if_custom() {
                            self.result.y_func = Some(self.funcs[c as usize]);
                        } else {
                            self.result.y_var = Some(y);
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn status_screen_mode<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    status_arr: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;

    let goliath_turret_status = binary.read_address(status_arr + 0x4 * 0xc + 0x8).ok()?;
    // First variable that goliath turret's status screen function writes to is
    // setting that mode to 0.
    let mut analysis = FuncAnalysis::new(binary, ctx, goliath_turret_status);
    let mut analyzer = StatusScreenMode::<E> {
        result: None,
        inline_depth: 0,
        phantom: Default::default(),
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct StatusScreenMode<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    inline_depth: u8,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for StatusScreenMode<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.inline_depth < 1 {
                        self.inline_depth += 1;
                        ctrl.analyze_with_current_state(self, dest);
                        self.inline_depth -= 1;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(mem), val, None) => {
                if mem.size == MemAccessSize::Mem8 {
                    let ctx = ctrl.ctx();
                    if ctx.and_const(ctrl.resolve(val), 0xff).if_constant() == Some(0) {
                        let dest = ctrl.resolve(mem.address);
                        if dest.if_constant().is_some() {
                            self.result = Some(ctx.mem8(dest));
                            ctrl.end_analysis();
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn multi_wireframes<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    spawn_dialog: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> MultiWireframes<'e, E::VirtualAddress> {
    let mut result = MultiWireframes::default();
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let funcs = functions.functions();
    let str_refs = functions.string_refs(analysis, b"unit\\wirefram\\tranwire");
    let arg_cache = &analysis.arg_cache;
    for str_ref in &str_refs {
        let res = crate::entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            let mut analyzer = MultiWireframeAnalyzer {
                result: &mut result,
                arg_cache,
                binary,
                check_return_store: None,
                spawn_dialog,
                last_global_store_address: None,
            };

            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if result.status_screen.is_some() {
                EntryOf::Ok(())
            } else {
                EntryOf::Retry
            }
        }).into_option_with_entry();
        if let Some((addr, ())) = res {
            if result.grpwire_grp.is_some() {
                result.init_status_screen = Some(addr);
                break;
            }
        }
    }
    result
}

struct MultiWireframeAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut MultiWireframes<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    check_return_store: Option<MultiGrpType>,
    spawn_dialog: E::VirtualAddress,
    last_global_store_address: Option<Operand<'e>>,
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
enum MultiGrpType {
    Group,
    Transport,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for MultiWireframeAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        // load_grp(path, 0, ..)
        // load_ddsgrp(path, out, ..)
        // Both are called by same status screen init func
        match *op {
            Operation::Move(DestOperand::Memory(mem), val, None) => {
                let val = ctrl.resolve(val);
                if let Some(c) = val.if_custom() {
                    let address = ctrl.resolve(mem.address);
                    if c == 0 {
                        if let Some(ty) = self.check_return_store.take() {
                            let dest = ctrl.mem_word(address);
                            match ty {
                                MultiGrpType::Group => self.result.grpwire_grp = Some(dest),
                                MultiGrpType::Transport => self.result.tranwire_grp = Some(dest),
                            };
                        }
                    } else {
                        if address.if_constant().is_some() {
                            // Skip storing other func returns to globals
                            // (So that spawn_dialog call doesn't just get Custom(1) for
                            // status_screen)
                            ctrl.skip_operation();
                            self.last_global_store_address = Some(address);
                        }
                    }
                }
            }
            Operation::Call(dest) => {
                let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if dest == self.spawn_dialog {
                        let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                        // spawn_dialog(dialog, 0, event_handler)
                        // The dialog variable may have been written and is reread for the call,
                        // or it may just pass the return address directly (but still have
                        // it written to the global before call)
                        if arg1.if_custom() == Some(1) {
                            self.result.status_screen = self.last_global_store_address.take()
                                .map(|x| ctrl.mem_word(x));
                        } else {
                            self.result.status_screen = Some(arg1);
                        }
                        self.result.status_screen_event_handler = arg3.if_constant()
                            .map(|x| E::VirtualAddress::from_u64(x));
                        return;
                    }
                }
                if let Some(ty) = self.is_multi_grp_path(arg1) {
                    let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                    if arg2.if_constant() == Some(0) {
                        self.check_return_store = Some(ty);
                        ctrl.skip_operation();
                        let ctx = ctrl.ctx();
                        let custom = ctx.custom(0);
                        let exec_state = ctrl.exec_state();
                        exec_state.move_to(
                            &DestOperand::Register64(scarf::operand::Register(0)),
                            custom,
                        );
                    } else {
                        match ty {
                            MultiGrpType::Group => self.result.grpwire_ddsgrp = Some(arg2),
                            MultiGrpType::Transport => self.result.tranwire_ddsgrp = Some(arg2),
                        }
                    }
                } else {
                    // Make other call results Custom(1), and prevent writing them to
                    // memory (Prevent writing load_dialog result to status_screen global)
                    ctrl.skip_operation();
                    let ctx = ctrl.ctx();
                    let custom = ctx.custom(1);
                    let exec_state = ctrl.exec_state();
                    exec_state.move_to(
                        &DestOperand::Register64(scarf::operand::Register(0)),
                        custom,
                    );
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> MultiWireframeAnalyzer<'a, 'e, E> {
    fn is_multi_grp_path(&self, val: Operand<'e>) -> Option<MultiGrpType> {
        let address = E::VirtualAddress::from_u64(val.if_constant()?);
        static CANDIDATES: &[(&[u8], MultiGrpType)] = &[
            (b"unit\\wirefram\\grpwire", MultiGrpType::Group),
            (b"unit\\wirefram\\tranwire", MultiGrpType::Transport),
        ];

        CANDIDATES.iter()
            .filter_map(|&(path, ty)| {
                let bytes = self.binary.slice_from_address(address, path.len() as u32).ok()?;
                Some(ty).filter(|_| bytes.eq_ignore_ascii_case(path))
            })
            .next()
    }
}

pub(crate) fn wirefram_ddsgrp<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    ss_event_handler: E::VirtualAddress,
) -> Option<Operand<'e>> {
    // Search for control draw function of the main wireframe control
    // - Status screen event handler w/ init event calls init_child_event_handlers
    // - Index 0 of those handlers is wireframe
    // - Wireframe control handler w/ init event sets the drawfunc
    // Then search for grp_frame_header(wirefram_ddsgrp, index, stack_out1, stack_out2)
    // wirefram_ddsgrp is likely `deref_this(get_wirefram_ddsgrp())`, so inline a bit
    let ctx = analysis.ctx;
    let binary = analysis.binary;

    let wireframe_event = find_child_event_handler::<E>(analysis, ss_event_handler, 0)?;
    let draw_func = find_child_draw_func::<E>(analysis, wireframe_event)?;
    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, draw_func);
    let mut analyzer = WireframDdsgrpAnalyzer {
        inline_depth: 0,
        arg_cache,
        result: None,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct WireframDdsgrpAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
    result: Option<Operand<'e>>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for WireframDdsgrpAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if self.inline_depth == 0 {
                    // Arg 3 and 4 should be referring to stack, arg 1 global mem
                    let result = Some(())
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(2)))
                        .filter(|&a3| is_stack_address(a3))
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(3)))
                        .filter(|&a4| is_stack_address(a4))
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(0)))
                        .and_then(|a1| ctrl.if_mem_word(a1))
                        .filter(|&a1| a1.if_constant().is_some());
                    if result.is_some() {
                        self.result = result;
                        ctrl.end_analysis();
                        return;
                    }
                }
                if self.inline_depth < 2 {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let ctx = ctrl.ctx();
                        let dest = E::VirtualAddress::from_u64(dest);
                        // Force keep esp/ebp same across calls
                        // esp being same can be wrong but oh well
                        let esp = ctrl.resolve(ctx.register(4));
                        let ebp = ctrl.resolve(ctx.register(5));
                        self.inline_depth += 1;
                        ctrl.inline(self, dest);
                        self.inline_depth -= 1;
                        ctrl.skip_operation();
                        let eax = ctrl.resolve(ctx.register(0));
                        if eax.if_constant().is_some() &&
                            ctrl.read_memory(eax, E::WORD_SIZE).is_undefined()
                        {
                            // hackfix to fix get_ddsgrp() static constructor
                            // writing 0 to [ddsgrp], causing it be undefined.
                            // Make it back [ddsgrp]
                            let val = ctrl.mem_word(eax);
                            let exec_state = ctrl.exec_state();
                            exec_state.move_resolved(&DestOperand::from_oper(val), val);
                        }
                        let exec_state = ctrl.exec_state();
                        exec_state.move_resolved(
                            &DestOperand::Register64(scarf::operand::Register(4)),
                            esp,
                        );
                        exec_state.move_resolved(
                            &DestOperand::Register64(scarf::operand::Register(5)),
                            ebp,
                        );
                    }
                }
            }
            _ => (),
        }
    }
}

/// Given address of a dialog event handler, tries to find
/// `handlers` in init_child_event_handlers(dlg, handlers, handler_len_bytes)
fn find_child_event_handlers<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    event_handler: E::VirtualAddress,
) -> Option<(E::VirtualAddress, u32)> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;

    let arg_cache = &analysis.arg_cache;
    // Move event (custom 0) to arg2, and write
    // event.type = 0xe, event.ext_type = 0x0
    let mut exec_state = E::initial_state(ctx, binary);
    let arg2_loc = arg_cache.on_entry(1);
    let event_address = ctx.custom(0);
    exec_state.move_to(
        &DestOperand::from_oper(arg2_loc),
        event_address,
    );
    exec_state.move_to(
        &DestOperand::from_oper(ctx.mem16(ctx.add_const(event_address, 0x10))),
        ctx.constant(0xe),
    );
    exec_state.move_to(
        &DestOperand::from_oper(ctx.mem32(ctx.add_const(event_address, 0x0))),
        ctx.constant(0x0),
    );
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        event_handler,
        exec_state,
        Default::default(),
    );
    let mut analyzer = FindChildEventHandlers {
        arg_cache,
        result: None,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

fn find_child_event_handler<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    event_handler: E::VirtualAddress,
    index: u32
) -> Option<E::VirtualAddress> {
    let (array, len) = find_child_event_handlers(analysis, event_handler)?;
    if index * E::VirtualAddress::SIZE >= len {
        return None;
    }
    let binary = analysis.binary;
    binary.read_address(array + index * E::VirtualAddress::SIZE).ok()
        .filter(|addr| addr.as_u64() != 0)
}

struct FindChildEventHandlers<'a, 'e, E: ExecutionState<'e>> {
    arg_cache: &'a ArgCache<'e, E>,
    result: Option<(E::VirtualAddress, u32)>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindChildEventHandlers<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(_) => {
                let result = Some(())
                    .map(|_| ctrl.resolve(self.arg_cache.on_call(0)))
                    .filter(|&a1| a1 == self.arg_cache.on_entry(0))
                    .map(|_| ctrl.resolve(self.arg_cache.on_call(1)))
                    .and_then(|a2| {
                        let addr = E::VirtualAddress::from_u64(a2.if_constant()?);
                        let a3 = ctrl.resolve(self.arg_cache.on_call(2));
                        let len: u32 = a3.if_constant()?.try_into().ok()?;
                        Some((addr, len))
                    });
                if single_result_assign(result, &mut self.result) {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}

fn find_child_draw_func<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    event_handler: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;

    let arg_cache = &analysis.arg_cache;
    // Move event (custom 0) to arg2, and write
    // event.type = 0xe, event.ext_type = 0x0
    let mut exec_state = E::initial_state(ctx, binary);
    let arg2_loc = arg_cache.on_entry(1);
    let event_address = ctx.custom(0);
    exec_state.move_to(
        &DestOperand::from_oper(arg2_loc),
        event_address,
    );
    let event_type = struct_layouts::event_type::<E::VirtualAddress>();
    exec_state.move_to(
        &DestOperand::from_oper(ctx.mem16(ctx.add_const(event_address, event_type))),
        ctx.constant(0xe),
    );
    exec_state.move_to(
        &DestOperand::from_oper(ctx.mem32(event_address)),
        ctx.constant(0x0),
    );
    let mut analysis = FuncAnalysis::custom_state(
        binary,
        ctx,
        event_handler,
        exec_state,
        Default::default(),
    );
    let mut analyzer = FindChildDrawFunc {
        result: None,
        arg_cache,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindChildDrawFunc<'a, 'e, E: ExecutionState<'e>> {
    arg_cache: &'a ArgCache<'e, E>,
    result: Option<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindChildDrawFunc<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Move(DestOperand::Memory(mem), val, None) if mem.size == E::WORD_SIZE => {
                if let Some(val) = ctrl.resolve(val).if_constant() {
                    let addr = ctrl.resolve(mem.address);
                    // Older offset for draw func was 0x30, 0x48 is current
                    let ok = struct_layouts::control_draw_funcs::<E::VirtualAddress>()
                        .iter()
                        .any(|&offset| {
                            addr.if_arithmetic_add_const(offset)
                                .filter(|&other| other == self.arg_cache.on_entry(0))
                                .is_some()
                        });
                    if ok && val > 0x10000 {
                        self.result = Some(E::VirtualAddress::from_u64(val));
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn ui_event_handlers<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    game_screen_rclick: E::VirtualAddress,
    functions: &FunctionFinder<'_, 'e, E>,
) -> UiEventHandlers<'e, E::VirtualAddress> {
    let mut result = UiEventHandlers {
        reset_ui_event_handlers: None,
        default_scroll_handler: None,
        global_event_handlers: None,
    };

    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let funcs = functions.functions();
    let global_refs = functions.find_functions_using_global(analysis, game_screen_rclick);
    for func in &global_refs {
        let val = crate::entry_of_until(binary, &funcs, func.use_address, |entry| {
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = ResetUiEventHandlersAnalyzer::<E> {
                entry_of: EntryOf::Retry,
                use_address: func.use_address,
                result: &mut result,
                stores: FxHashMap::with_capacity_and_hasher(0x20, Default::default()),
                ctx,
            };
            analysis.analyze(&mut analyzer);
            analyzer.finish();
            analyzer.entry_of
        }).into_option_with_entry().map(|x| x.0);
        if let Some(addr) = val {
            result.reset_ui_event_handlers = Some(addr);
            break;
        }
    }

    result
}

struct ResetUiEventHandlersAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    entry_of: EntryOf<()>,
    use_address: E::VirtualAddress,
    result: &'a mut UiEventHandlers<'e, E::VirtualAddress>,
    // Base, offset -> value
    stores: FxHashMap<(scarf::operand::OperandHashByAddress<'e>, u64), E::VirtualAddress>,
    ctx: OperandCtx<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    ResetUiEventHandlersAnalyzer<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() <= self.use_address &&
            ctrl.current_instruction_end() > self.use_address
        {
            self.entry_of = EntryOf::Stop;
        }
        match *op {
            Operation::Move(DestOperand::Memory(mem), val, None)
                if mem.size == E::WORD_SIZE =>
            {
                // Search for stores to
                // global_event_handlers[0] = func1
                // global_event_handlers[1] = (not set)
                // global_event_handlers[2] = func2
                // global_event_handlers[3] = 0
                // ..
                // global_event_handlers[0x11] = scroll_handler
                // global_event_handlers[0x12] = scroll_handler
                let val = ctrl.resolve(val);
                if let Some(c) = val.if_constant() {
                    let val = E::VirtualAddress::from_u64(c);
                    let address = ctrl.resolve(mem.address);
                    if !address.contains_undefined() {
                        let (base, offset) = Operand::const_offset(address, self.ctx)
                            .unwrap_or_else(|| (address, 0));
                        self.stores.insert((base.hash_by_address(), offset), val);
                    }
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> ResetUiEventHandlersAnalyzer<'a, 'e, E> {
    fn finish(&mut self) {
        'outer: for (&(base, offset), _) in &self.stores {
            let mut val_11 = E::VirtualAddress::from_u64(0);
            for i in 0..0x13 {
                if matches!(i, 1 | 5 | 8 | 9 | 0xc | 0xe | 0x10) {
                    // These indices aren't set by this func
                    // (Though at least idx 1 gets set by a func that is called)
                    continue;
                }
                let i_offset = offset.wrapping_add(u64::from(E::VirtualAddress::SIZE) * i);
                let val = match self.stores.get(&(base, i_offset)) {
                    Some(&s) => s,
                    None => continue 'outer,
                };
                if i == 3 && val != E::VirtualAddress::from_u64(0) {
                    continue 'outer;
                }
                if i != 3 && val == E::VirtualAddress::from_u64(0) {
                    continue 'outer;
                }
                if i == 0x11 {
                    val_11 = val;
                }
                if i == 0x12 && val_11 != val {
                    continue 'outer;
                }
            }
            let addr = self.ctx.add_const(base.0, offset);
            self.result.global_event_handlers = Some(addr);
            self.result.default_scroll_handler = Some(val_11);
            self.entry_of = EntryOf::Ok(());
            return;
        }
    }
}

pub(crate) fn clamp_zoom<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    scroll_handler: E::VirtualAddress,
    is_multiplayer: Operand<'e>,
) -> Option<E::VirtualAddress> {
    // ui_default_scroll_handler calls into scroll_zoom(-0.1f32),
    // which calls into clamp_zoom((a1 + val1) * val2),
    // which jumps based on is_multiplayer

    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut analysis = FuncAnalysis::new(binary, ctx, scroll_handler);
    let mut analyzer = FindClampZoom::<E> {
        inline_depth: 0,
        is_multiplayer,
        arg_cache: &actx.arg_cache,
        result: None,
    };
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindClampZoom<'a, 'e, E: ExecutionState<'e>> {
    inline_depth: u8,
    arg_cache: &'a ArgCache<'e, E>,
    is_multiplayer: Operand<'e>,
    result: Option<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindClampZoom<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if let Operation::Call(dest) = *op {
            if let Some(dest) = ctrl.resolve_va(dest) {
                let (inline, clamp_zoom) = self.check_inline(ctrl);
                if inline {
                    self.inline_depth += 1;
                    ctrl.analyze_with_current_state(self, dest);
                    self.inline_depth -= 1;
                    if self.result.is_some() {
                        if clamp_zoom {
                            self.result = Some(dest);
                        }
                        ctrl.end_analysis();
                    }
                }
            }
        } else if let Operation::Jump { condition, to } = *op {
            if condition == ctx.const_1() &&
                ctrl.resolve(ctx.register(4)) == ctx.register(4)
            {
                if let Some(to) = ctrl.resolve_va(to) {
                    // Tail call
                    let (inline, clamp_zoom) = self.check_inline(ctrl);
                    if inline {
                        let binary = ctrl.binary();
                        self.inline_depth += 1;
                        let mut analysis = FuncAnalysis::custom_state(
                            binary,
                            ctx,
                            to,
                            ctrl.exec_state().clone(),
                            Default::default(),
                        );
                        analysis.analyze(self);
                        self.inline_depth -= 1;
                        if self.result.is_some() {
                            if clamp_zoom {
                                self.result = Some(to);
                            }
                            ctrl.end_analysis();
                            return;
                        }
                    }
                    ctrl.end_branch();
                }
            }
            let condition = ctrl.resolve(condition);
            let ok = if_arithmetic_eq_neq(condition)
                .filter(|x| x.1 == ctx.const_0())
                .filter(|&x| x.0 == self.is_multiplayer)
                .is_some();
            if ok {
                self.result = Some(E::VirtualAddress::from_u64(0));
                ctrl.end_analysis();
            }
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> FindClampZoom<'a, 'e, E> {
    /// Returns (should_inline, is_clamp_zoom_candidate)
    fn check_inline(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) -> (bool, bool) {
        let ctx = ctrl.ctx();
        let arg1 = match E::VirtualAddress::SIZE == 4 {
            true => ctrl.resolve(self.arg_cache.on_call(0)),
            false => ctrl.resolve(ctx.xmm(0, 0)),
        };
        let binary = ctrl.binary();
        // 0xbdcc_cccd == -0.1 f32
        if self.inline_depth == 0 {
            if arg1.if_constant_or_read_binary(binary) == Some(0xbdcc_cccd) {
                return (true, false);
            }
        }
        let clamp_zoom_call = arg1.if_arithmetic_float(ArithOpType::Mul)
            .and_either(|x| x.if_arithmetic_float(ArithOpType::Add))
            .map(|x| x.0)
            .and_either(|x| {
                x.if_constant_or_read_binary(binary).filter(|&c| c == 0xbdcc_cccd)
            })
            .is_some();
        if clamp_zoom_call {
            return (true, true);
        }
        (false, false)
    }
}

pub(crate) fn analyze_run_menus<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    run_menus: E::VirtualAddress,
) -> RunMenus<E::VirtualAddress> {
    let mut result = RunMenus {
        set_music: None,
        pre_mission_glue: None,
        show_mission_glue: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;
    let mut analysis = FuncAnalysis::new(binary, ctx, run_menus);
    let mut analyzer = RunMenusAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        state: RunMenusState::Start,
        inline_depth: 0,
    };
    analysis.analyze(&mut analyzer);
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum RunMenusState {
    Start,
    TerranBriefing,
    CheckPreMissionGlue,
    FindShowMissionGlue,
}

struct RunMenusAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut RunMenus<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    state: RunMenusState,
    inline_depth: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for RunMenusAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            RunMenusState::Start => {
                // Find switch jump
                if let Operation::Jump { condition, to } = *op {
                    if condition == ctx.const_1() {
                        let to = ctrl.resolve(to);
                        let switch_table = ctrl.if_mem_word(to)
                            .and_then(|x| x.if_arithmetic_add())
                            .and_then(|x| x.1.if_constant())
                            .map(|x| E::VirtualAddress::from_u64(x));
                        if let Some(switch_table) = switch_table {
                            let binary = ctrl.binary();
                            let case = binary.read_address(
                                switch_table + 0x13 * E::VirtualAddress::SIZE
                            );
                            if let Ok(case) = case {
                                self.state = RunMenusState::TerranBriefing;
                                ctrl.analyze_with_current_state(self, case);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            RunMenusState::TerranBriefing => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        if self.result.set_music.is_none() {
                            let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                            if arg1.if_constant() == Some(0xe) {
                                self.result.set_music = Some(dest);
                                return;
                            }
                            if self.inline_depth == 0 {
                                self.inline_depth += 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth -= 1;
                                if self.result.set_music.is_some() {
                                    ctrl.end_analysis();
                                }
                            }
                        } else {
                            self.state = RunMenusState::CheckPreMissionGlue;
                            ctrl.analyze_with_current_state(self, dest);
                            self.state = RunMenusState::TerranBriefing;
                            if self.result.pre_mission_glue.is_some() {
                                self.result.pre_mission_glue = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                if let Operation::Jump { to, .. } = *op {
                    if to.if_memory().is_some() {
                        // Looped back to switch probably.
                        ctrl.end_analysis();
                    }
                }
            }
            RunMenusState::CheckPreMissionGlue => {
                if let Operation::Jump { condition, .. } = *op {
                    let cond = ctrl.resolve(condition);
                    let ok = if_arithmetic_eq_neq(cond)
                        .map(|x| (x.0, x.1))
                        .and_either_other(|x| Some(()).filter(|&()| x == ctx.const_0()))
                        .and_then(|x| {
                            x.if_arithmetic_and_const(0x20)
                                .or_else(|| x.if_arithmetic_and_const(0x2000_0000))
                        })
                        .is_some();
                    if ok {
                        self.result.pre_mission_glue = Some(E::VirtualAddress::from_u64(0));
                        self.state = RunMenusState::FindShowMissionGlue;
                    }
                }
            }
            RunMenusState::FindShowMissionGlue => {
                if let Operation::Call(dest) = *op {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                        let ok = arg1.if_mem32().is_some() && arg2.if_constant() == Some(1);
                        if ok {
                            self.result.show_mission_glue = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn analyze_glucmpgn_events<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    event_handler: E::VirtualAddress,
) -> GluCmpgnEvents<'e, E::VirtualAddress> {
    let mut result = GluCmpgnEvents {
        swish_in: None,
        swish_out: None,
        dialog_return_code: None,
    };
    let ctx = actx.ctx;
    let binary = actx.binary;
    let exec = E::initial_state(ctx, binary);
    let state = GluCmpgnState {
        dialog_return_stored: false,
    };
    let mut analysis = FuncAnalysis::custom_state(binary, ctx, event_handler, exec, state);
    let mut analyzer = GluCmpgnAnalyzer::<E> {
        result: &mut result,
        arg_cache: &actx.arg_cache,
        ext_event_branch: 0,
        inlining: false,
    };
    analysis.analyze(&mut analyzer);
    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct GluCmpgnState {
    dialog_return_stored: bool,
}

impl AnalysisState for GluCmpgnState {
    fn merge(&mut self, newer: Self) {
        self.dialog_return_stored |= newer.dialog_return_stored;
    }
}

struct GluCmpgnAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut GluCmpgnEvents<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    ext_event_branch: u8,
    inlining: bool,
}

fn resolve_memory<Va: VirtualAddress>(binary: &BinaryFile<Va>, op: Operand<'_>) -> Option<u64> {
    if let Some(mem) = op.if_memory() {
        let val = resolve_memory(binary, mem.address)?;
        let val = binary.read_u64(Va::from_u64(val)).ok()?;
        Some(val & mem.size.mask())
    } else if let Some(c) = op.if_constant() {
        Some(c)
    } else if let scarf::OperandType::Arithmetic(arith) = op.ty() {
        let left = resolve_memory(binary, arith.left)?;
        let right = resolve_memory(binary, arith.right)?;
        match arith.ty {
            ArithOpType::Add => Some(left.wrapping_add(right)),
            ArithOpType::Sub => Some(left.wrapping_sub(right)),
            ArithOpType::Mul => Some(left.wrapping_mul(right)),
            _ => None,
        }
    } else {
        None
    }
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for GluCmpgnAnalyzer<'a, 'e, E>
{
    type State = GluCmpgnState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, to } => {
                let ctx = ctrl.ctx();
                let binary = ctrl.binary();
                if condition == ctx.const_1() {
                    let to = ctrl.resolve(to);
                    // Case 2 = Activate button (end), 0xa = Init
                    let ext_param = ctx.mem32(self.arg_cache.on_entry(1));
                    for &case in &[2u8, 0xa] {
                        let op = ctx.substitute(to, ext_param, ctx.constant(case.into()), 8);
                        let dest = resolve_memory(binary, op);
                        if let Some(dest) = dest {
                            let dest = E::VirtualAddress::from_u64(dest);
                            self.ext_event_branch = case;
                            ctrl.analyze_with_current_state(self, dest);
                        }
                    }
                    ctrl.end_analysis();
                }
            }
            Operation::Call(dest) if self.ext_event_branch != 0 => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if self.ext_event_branch == 0xa && self.result.swish_in.is_none() {
                        // swish_in(this, ptr, 2, 2, 0)
                        let is_swish_in = Some(())
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(0)))
                            .filter(|&x| x == self.arg_cache.on_entry(0))
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(1)))
                            .and_then(|x| x.if_constant().filter(|&c| c > 0x1000))
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(2)))
                            .filter(|x| x.if_constant() == Some(2))
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(3)))
                            .filter(|x| x.if_constant() == Some(2))
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(4)))
                            .filter(|x| x.if_constant() == Some(0))
                            .is_some();
                        if is_swish_in {
                            self.result.swish_in = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                    if self.ext_event_branch == 2 {
                        let state = ctrl.user_state();
                        if state.dialog_return_stored {
                            state.dialog_return_stored = false;
                            if self.result.swish_out.is_none() {
                                self.result.swish_out = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                        if !self.inlining {
                            let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                            if arg1 == self.arg_cache.on_entry(0) {
                                self.inlining = true;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inlining = false;
                                if self.result.swish_out.is_some() {
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(mem), val, None)
                if self.ext_event_branch == 2 =>
            {
                if self.result.dialog_return_code.is_none() {
                    let val = ctrl.resolve(val);
                    if val.if_constant() == Some(8) {
                        let ctx = ctrl.ctx();
                        self.result.dialog_return_code =
                            Some(ctx.mem_variable_rc(mem.size, mem.address));
                        ctrl.user_state().dialog_return_stored = true;
                    }
                }
            }
            _ => (),
        }
    }
}
