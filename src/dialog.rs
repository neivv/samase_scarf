use std::rc::Rc;

use scarf::analysis::{self, AnalysisState, Control, FuncAnalysis};
use scarf::exec_state::{InternMap, ExecutionState, VirtualAddress};
use scarf::{DestOperand, Operation, Operand, OperandContext};

use crate::{Analysis, ArgCache, EntryOf, single_result_assign, StringRefs};

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

            let mut interner = InternMap::new();
            let exec_state = E::initial_state(ctx, binary, &mut interner);
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
                interner,
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
    ctx: &'exec OperandContext,
}

#[derive(Clone)]
struct RunDialogState {
    calling_load_dialog: bool,
    calling_create_string: bool,
    load_dialog_result: Option<Rc<Operand>>,
    path_string: Option<Rc<Operand>>,
}

impl AnalysisState for RunDialogState {
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
    type State = RunDialogState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation) {
        if ctrl.user_state().calling_load_dialog {
            let rax = ctrl.resolve(&self.ctx.register(0));
            let user_state = ctrl.user_state();
            user_state.calling_load_dialog = false;
            user_state.load_dialog_result = Some(rax);
        }
        if ctrl.user_state().calling_create_string {
            let path_string = ctrl.user_state().path_string.clone();
            ctrl.user_state().calling_create_string = false;
            if let Some(path_string) = path_string {
                let dest = DestOperand::from_oper(&self.ctx.register(0));
                let dest2 = DestOperand::from_oper(&ctrl.mem_word(path_string.clone()));
                let (state, i) = ctrl.exec_state();
                // String creation function returns eax = arg1
                state.move_resolved(&dest, path_string, i);
                // Mem[string + 0] is character data
                state.move_resolved(&dest2, self.ctx.constant(self.string_address.as_u64()), i);
            }
        }
        match op {
            Operation::Call(ref to) => {
                let arg1 = ctrl.resolve(&self.args.on_call(0));
                let arg2 = ctrl.resolve(&self.args.on_call(1));
                let arg3 = ctrl.resolve(&self.args.on_call(2));
                let arg4 = ctrl.resolve(&self.args.on_call(3));
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
    let mut analysis = FuncAnalysis::new(analysis.binary, &ctx, func);
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
    path_string: Option<Rc<Operand>>,
    str_ref: &'a StringRefs<E::VirtualAddress>,
    ctx: &'e OperandContext,
    args: &'a ArgCache<'e, E>,
    return_marker: Rc<Operand>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for DialogGlobalAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        if ctrl.address() == self.str_ref.use_address {
            self.result = EntryOf::Stop;
        }
        if self.after_call {
            // Has to be done like this since just writing to eax before call would
            // just get overwritten later
            let eax = DestOperand::Register64(scarf::operand::Register(0));
            let (state, interner) = ctrl.exec_state();
            state.move_to(&eax, self.return_marker.clone(), interner);
            self.after_call = false;
        }
        if let Some(path_string) = self.path_string.take() {
            let dest = DestOperand::Register64(scarf::operand::Register(0));
            let dest2 = DestOperand::from_oper(&ctrl.mem_word(path_string.clone()));
            let (state, interner) = ctrl.exec_state();
            // String creation function returns eax = arg1
            state.move_resolved(&dest, path_string, interner);
            // Mem[string + 0] is character data
            state.move_resolved(
                &dest2,
                self.ctx.constant(self.str_ref.string_address.as_u64()),
                interner,
            );
        }
        match op {
            Operation::Call(_dest) => {
                let addr_const = self.ctx.constant(self.str_ref.string_address.as_u64());
                if value_in_call_args(ctrl, addr_const) {
                    let arg2 = ctrl.resolve(&self.args.on_call(1));
                    let arg4 = ctrl.resolve(&self.args.on_call(3));
                    let arg4_is_string_ptr = arg4.if_constant()
                        .filter(|&c| c == self.str_ref.string_address.as_u64())
                        .is_some();
                    let arg2_is_string_ptr = arg2.if_constant()
                        .filter(|&c| c == self.str_ref.string_address.as_u64())
                        .is_some();
                    // Check for either creating a string (1.23.2+) or const char ptr
                    if arg2_is_string_ptr || arg4_is_string_ptr {
                        let arg1 = ctrl.resolve(&self.args.on_call(0));
                        self.path_string = Some(arg1);
                    } else {
                        self.after_call = true;
                    }
                }
            }
            Operation::Move(dest, val, _condition) => {
                let resolved = ctrl.resolve(val);
                if resolved == self.return_marker {
                    if let DestOperand::Memory(ref mem) = *dest {
                        if let Some(c) = ctrl.resolve(&mem.address).if_constant() {
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
    value: Rc<Operand>,
) -> bool {
    use scarf::operand_helpers::*;
    let esp = || operand_register(4);
    let val = Operand::simplified(value);

    (0..8).map(|i| {
        mem32(operand_add(esp(), constval(i * 4)))
    }).chain({
        [1].iter().cloned().map(|reg| operand_register(reg))
    }).filter(|oper| {
        let oper = ctrl.resolve(&oper);
        oper == val
    }).next().is_some()
}
