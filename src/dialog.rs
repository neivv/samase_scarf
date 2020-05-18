use scarf::analysis::{self, AnalysisState, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{MemAccess, MemAccessSize};
use scarf::{DestOperand, Operation, Operand, OperandCtx};

use crate::{Analysis, ArgCache, EntryOf, single_result_assign, StringRefs};

#[derive(Clone)]
pub struct TooltipRelated<'e, Va: VirtualAddress> {
    pub tooltip_draw_func: Option<Operand<'e>>,
    pub current_tooltip_ctrl: Option<Operand<'e>>,
    pub layout_draw_text: Option<Va>,
}

pub fn run_dialog<'a, E: ExecutionState<'a>>(
    analysis: &mut Analysis<'a, E>,
) -> Option<E::VirtualAddress> {
    let ctx = analysis.ctx;

    let binary = analysis.binary;
    let funcs = analysis.functions();
    let mut str_refs = crate::string_refs(binary, analysis, b"rez\\glucmpgn");
    if str_refs.is_empty() {
        str_refs = crate::string_refs(binary, analysis, b"glucmpgn.ui");
    }
    let args = &analysis.arg_cache;
    let mut result = None;
    for str_ref in &str_refs {
        let val = crate::entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            let mut analyzer = RunDialogAnalyzer {
                string_address: str_ref.string_address,
                result: None,
                args,
                ctx,
            };

            let exec_state = E::initial_state(ctx, binary);
            let mut analysis = FuncAnalysis::custom_state(
                binary,
                ctx,
                entry,
                exec_state,
                RunDialogState {
                    calling_load_dialog: false,
                    calling_create_string: false,
                    load_dialog_result: None,
                    path_string: None,
                },
            );
            analysis.analyze(&mut analyzer);
            if let Some(result) = analyzer.result {
                EntryOf::Ok(result)
            } else {
                EntryOf::Retry
            }
        }).into_option();
        if single_result_assign(val, &mut result) {
            break;
        }
    }
    result
}

struct RunDialogAnalyzer<'exec, 'b, E: ExecutionState<'exec>> {
    string_address: E::VirtualAddress,
    result: Option<E::VirtualAddress>,
    args: &'b ArgCache<'exec, E>,
    ctx: OperandCtx<'exec>,
}

#[derive(Copy, Clone)]
struct RunDialogState<'e> {
    calling_load_dialog: bool,
    calling_create_string: bool,
    load_dialog_result: Option<Operand<'e>>,
    path_string: Option<Operand<'e>>,
}

impl<'e> AnalysisState for RunDialogState<'e> {
    fn merge(&mut self, newer: Self) {
        self.calling_load_dialog = newer.calling_load_dialog && self.calling_load_dialog;
        self.calling_create_string = newer.calling_create_string && self.calling_create_string;
        if self.load_dialog_result != newer.load_dialog_result {
            self.load_dialog_result = None;
        }
        if self.path_string != newer.path_string {
            self.path_string = None;
        }
    }
}

impl<'exec, 'b, E: ExecutionState<'exec>> scarf::Analyzer<'exec> for
    RunDialogAnalyzer<'exec, 'b, E>
{
    type State = RunDialogState<'exec>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation<'exec>) {
        if ctrl.user_state().calling_load_dialog {
            let rax = ctrl.resolve(self.ctx.register(0));
            let user_state = ctrl.user_state();
            user_state.calling_load_dialog = false;
            user_state.load_dialog_result = Some(rax);
        }
        if ctrl.user_state().calling_create_string {
            let path_string = ctrl.user_state().path_string;
            ctrl.user_state().calling_create_string = false;
            if let Some(path_string) = path_string {
                let dest = DestOperand::from_oper(self.ctx.register(0));
                let dest2 = DestOperand::from_oper(ctrl.mem_word(path_string));
                let state = ctrl.exec_state();
                // String creation function returns eax = arg1
                state.move_resolved(&dest, path_string);
                // Mem[string + 0] is character data
                state.move_resolved(&dest2, self.ctx.constant(self.string_address.as_u64()));
            }
        }
        match *op {
            Operation::Call(to) => {
                let arg1 = ctrl.resolve(self.args.on_call(0));
                let arg2 = ctrl.resolve(self.args.on_call(1));
                let arg3 = ctrl.resolve(self.args.on_call(2));
                let arg4 = ctrl.resolve(self.args.on_call(3));
                let arg1_is_dialog_ptr = {
                    let user_state = ctrl.user_state();
                    if let Some(ref val) = user_state.load_dialog_result {
                        *val == arg1
                    } else {
                        false
                    }
                };
                if arg1_is_dialog_ptr {
                    // run_dialog(dialog, 0, event_handler)
                    let arg2_zero = arg2.if_constant().filter(|&c| c == 0).is_some();
                    let arg3_ptr = arg3.if_constant().filter(|&c| c != 0).is_some();
                    if arg2_zero && arg3_ptr {
                        if let Some(to) = ctrl.resolve(to).if_constant() {
                            let result = Some(E::VirtualAddress::from_u64(to));
                            if single_result_assign(result, &mut self.result) {
                                ctrl.end_analysis();
                            }
                            return;
                        }
                    }
                }
                let arg1_is_string_ptr = {
                    arg1.if_constant()
                        .filter(|&c| c == self.string_address.as_u64())
                        .is_some()
                };
                if arg1_is_string_ptr {
                    ctrl.user_state().calling_load_dialog = true;
                }
                let arg4_is_string_ptr = arg4.if_constant()
                    .filter(|&c| c == self.string_address.as_u64())
                    .is_some();
                let arg2_is_string_ptr = arg2.if_constant()
                    .filter(|&c| c == self.string_address.as_u64())
                    .is_some();
                if arg2_is_string_ptr || arg4_is_string_ptr {
                    let state = ctrl.user_state();
                    state.calling_create_string = true;
                    state.path_string = Some(arg1);
                }
            }
            _ => (),
        }
    }
}

/// Assuming that `func` calls the load_dialog function with a constant string somewhere in
/// arguments, returns the global variable(s) load_dialog's return value is stored to (if any)
pub fn find_dialog_global<'exec, E: ExecutionState<'exec>>(
    analysis: &mut Analysis<'exec, E>,
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
                let addr_const = self.ctx.constant(self.str_ref.string_address.as_u64());
                if value_in_call_args(ctrl, addr_const) {
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

fn value_in_call_args<'exec, A: analysis::Analyzer<'exec>>(
    ctrl: &mut Control<'exec, '_, '_, A>,
    value: Operand<'exec>,
) -> bool {
    let ctx = ctrl.ctx();
    let esp = ctx.register(4);

    (0..8).map(|i| {
        ctx.mem32(ctx.add(esp, ctx.constant(i * 4)))
    }).chain({
        [1].iter().cloned().map(|reg| ctx.register(reg))
    }).filter(|&oper| {
        let oper = ctrl.resolve(oper);
        oper == value
    }).next().is_some()
}

pub fn spawn_dialog<'a, E: ExecutionState<'a>>(
    analysis: &mut Analysis<'a, E>,
) -> Option<E::VirtualAddress> {
    // This is currently just copypasted from run_dialog, it ends up working fine as the
    // signature and dialog init patterns are same between run (blocking) and spawn (nonblocking).
    // If it won't in future then this should be refactored to have its own Analyzer
    let ctx = analysis.ctx;

    let binary = analysis.binary;
    let funcs = analysis.functions();
    let mut str_refs = crate::string_refs(binary, analysis, b"rez\\statlb");
    if str_refs.is_empty() {
        str_refs = crate::string_refs(binary, analysis, b"statlb.ui");
    }
    let args = &analysis.arg_cache;
    let mut result = None;
    for str_ref in &str_refs {
        let val = crate::entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
            let mut analyzer = RunDialogAnalyzer {
                string_address: str_ref.string_address,
                result: None,
                args,
                ctx,
            };

            let exec_state = E::initial_state(ctx, binary);
            let mut analysis = FuncAnalysis::custom_state(
                binary,
                ctx,
                entry,
                exec_state,
                RunDialogState {
                    calling_load_dialog: false,
                    calling_create_string: false,
                    load_dialog_result: None,
                    path_string: None,
                },
            );
            analysis.analyze(&mut analyzer);
            if let Some(result) = analyzer.result {
                EntryOf::Ok(result)
            } else {
                EntryOf::Retry
            }
        }).into_option();
        if single_result_assign(val, &mut result) {
            break;
        }
    }
    result
}

pub fn tooltip_related<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> TooltipRelated<'e, E::VirtualAddress> {
    let mut result = TooltipRelated {
        tooltip_draw_func: None,
        current_tooltip_ctrl: None,
        layout_draw_text: None,
    };

    let spawn_dialog = match analysis.spawn_dialog() {
        Some(s) => s,
        None => return result,
    };

    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let funcs = analysis.functions();
    let mut str_refs = crate::string_refs(binary, analysis, b"rez\\stat_f10");
    if str_refs.is_empty() {
        str_refs = crate::string_refs(binary, analysis, b"stat_f10.ui");
    }
    for str_ref in &str_refs {
        crate::entry_of_until(binary, &funcs, str_ref.use_address, |entry| {
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
                draw_menu_tooltip: None,
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

#[derive(Copy, Clone)]
enum TooltipState<'e> {
    FindEventHandler,
    FindTooltipCtrl {
        tooltip_ctrl: Option<Operand<'e>>,
        tooltip_fn: Option<Operand<'e>>,
    },
    FindLayoutText,
}

struct TooltipAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut TooltipRelated<'e, E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    entry_of: EntryOf<()>,
    spawn_dialog: E::VirtualAddress,
    inline_depth: u8,
    // The actual function that is being set as tooltip draw callback
    draw_menu_tooltip: Option<E::VirtualAddress>,
}

impl<'e> AnalysisState for TooltipState<'e> {
    fn merge(&mut self, newer: Self) {
        use self::TooltipState::*;
        match (*self, newer) {
            (
                FindTooltipCtrl { tooltip_ctrl: ref mut a, tooltip_fn: ref mut b },
                FindTooltipCtrl { tooltip_ctrl: ref a2, tooltip_fn: ref b2 },
            ) => {
                if a != a2 || b != b2 {
                    *a = None;
                    *b = None;
                }
            }
            (_, _) => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for TooltipAnalyzer<'a, 'e, E> {
    type State = TooltipState<'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *ctrl.user_state() {
            TooltipState::FindEventHandler => self.state1(ctrl, op),
            TooltipState::FindTooltipCtrl { .. } => self.state2(ctrl, op),
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
                    let event_handler = ctrl.resolve(self.arg_cache.on_call(2));
                    if let Some(c) = event_handler.if_constant() {
                        let addr = E::VirtualAddress::from_u64(c);
                        *ctrl.user_state() = TooltipState::FindTooltipCtrl {
                            tooltip_ctrl: None,
                            tooltip_fn: None,
                        };
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
                        exec_state.move_to(
                            &DestOperand::Memory(MemAccess {
                                address: ctx.add_const(ctx.custom(0), 0x10),
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

                let dest = ctrl.resolve(dest);
                if let Some(dest) = dest.if_constant().map(E::VirtualAddress::from_u64) {
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
                if mem.size.bits() != E::VirtualAddress::SIZE * 8 {
                    return;
                }
                let addr = ctrl.resolve(mem.address);
                if addr.contains_undefined() {
                    return;
                }
                let value = ctrl.resolve(value);
                let ctx = ctrl.ctx();
                let ok = if let TooltipState::FindTooltipCtrl {
                    ref mut tooltip_ctrl,
                    ref mut tooltip_fn,
                } = ctrl.user_state() {
                    let ok = if value.is_undefined() {
                        *tooltip_ctrl = Some(E::operand_mem_word(ctx, addr));
                        tooltip_fn.is_some()
                    } else {
                        if let Some(c) = value.if_constant() {
                            *tooltip_fn = Some(E::operand_mem_word(ctx, addr));
                            self.draw_menu_tooltip = Some(E::VirtualAddress::from_u64(c));
                            tooltip_ctrl.is_some()
                        } else {
                            false
                        }
                    };
                    if ok {
                        self.result.tooltip_draw_func = *tooltip_fn;
                        self.result.current_tooltip_ctrl = *tooltip_ctrl;
                    }
                    ok
                } else {
                    false
                };
                if ok {
                    if let Some(addr) = self.draw_menu_tooltip {
                        self.inline_depth = 0;
                        *ctrl.user_state() = TooltipState::FindLayoutText;
                        ctrl.analyze_with_current_state(self, addr);
                        ctrl.end_analysis();
                    }
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
                            match ctrl.resolve(self.arg_cache.on_call(i)).if_constant() {
                                Some(s) if s < 4 => s as u8 == vals[i as usize],
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
