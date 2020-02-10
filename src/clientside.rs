use std::rc::Rc;

use scarf::analysis::{self, Control};
use scarf::exec_state::{ExecutionState};
use scarf::{DestOperand, Operand, Operation, VirtualAddress};
use scarf::operand::{OperandContext, Register};

use scarf::exec_state::VirtualAddress as VirtualAddressTrait;

use crate::{
    Analysis, ArgCache, EntryOf, EntryOfResult, find_callers, entry_of_until,
    single_result_assign, OptionExt, DatType, find_functions_using_global,
};

use scarf::ExecutionStateX86;
type FuncAnalysis<'a, T> = scarf::analysis::FuncAnalysis<'a, ExecutionStateX86<'a>, T>;

pub enum ResultOrEntries<T, Va: VirtualAddressTrait> {
    Result(T),
    /// "not ok", but have entries of the functions for further analysis.
    Entries(Vec<Va>),
}

#[derive(Default)]
pub struct GameCoordConversion {
    pub screen_x: Option<Rc<Operand>>,
    pub screen_y: Option<Rc<Operand>>,
    pub scale: Option<Rc<Operand>>,
}

#[derive(Clone, Debug)]
pub struct GameScreenRClick<Va: VirtualAddressTrait> {
    pub game_screen_rclick: Option<Va>,
    pub client_selection: Option<Rc<Operand>>,
}

// Candidates are either a global ref with Some(global), or a call with None
fn game_screen_rclick_inner<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    candidates: &[(E::VirtualAddress, Option<E::VirtualAddress>)],
) -> ResultOrEntries<(E::VirtualAddress, Rc<Operand>), E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = &analysis.functions();

    let mut result: Option<(E::VirtualAddress, Rc<Operand>)> = None;
    let mut entries = Vec::new();
    for &(middle_of_func, global_addr) in candidates {
        let res = entry_of_until(binary, funcs, middle_of_func, |entry| {
            let mut analyzer = GameScreenRClickAnalyzer::<E> {
                call_found: false,
                result: None,
                mov_u32_max_seen: false,
                first_branch: true,
                middle_of_func,
                ctx,
                global_addr,
            };
            let mut analysis = analysis::FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if let Some(res) = analyzer.result {
                return EntryOf::Ok(res);
            }
            if analyzer.call_found {
                EntryOf::Stop
            } else {
                EntryOf::Retry
            }
        });
        match res {
            EntryOfResult::Ok(show_rclick_error_if_needed, client_selection) => {
                entries.push(show_rclick_error_if_needed);
                let callers = find_callers(analysis, show_rclick_error_if_needed);
                for f in callers {
                    let res: EntryOfResult<(), E::VirtualAddress> = entry_of_until(
                        binary,
                        funcs,
                        f,
                        |entry| {
                            let mut analyzer = WasInstructionRan::<E> {
                                ins: f,
                                result: false,
                            };
                            let mut analysis = analysis::FuncAnalysis::new(binary, ctx, entry);
                            analysis.analyze(&mut analyzer);
                            if analyzer.result {
                                EntryOf::Stop
                            } else {
                                EntryOf::Retry
                            }
                        }
                    );
                    if let EntryOfResult::Entry(e) = res {
                        let res = Some((e, client_selection.clone()));
                        if single_result_assign(res, &mut result) {
                            break;
                        }
                    }
                }
            }
            EntryOfResult::Entry(e) => {
                entries.push(e);
            }
            EntryOfResult::None => (),
        }
    }
    match result {
        Some(s) => ResultOrEntries::Result(s),
        None => ResultOrEntries::Entries(entries),
    }
}

struct WasInstructionRan<'e, E: ExecutionState<'e>> {
    ins: E::VirtualAddress,
    result: bool,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for WasInstructionRan<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, _op: &Operation) {
        if ctrl.address() == self.ins {
            self.result = true;
            ctrl.end_analysis();
        }
    }
}

struct GameScreenRClickAnalyzer<'e, E: ExecutionState<'e>> {
    call_found: bool,
    first_branch: bool,
    mov_u32_max_seen: bool,
    result: Option<Rc<Operand>>,
    middle_of_func: E::VirtualAddress,
    ctx: &'e OperandContext,
    global_addr: Option<E::VirtualAddress>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for GameScreenRClickAnalyzer<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation) {
        let address = ctrl.address();
        if !self.call_found {
            let in_possible_range =
                address.as_u64() >= self.middle_of_func.as_u64() - 8 &&
                address <= self.middle_of_func;
            if in_possible_range {
                if let Some(global_addr) = self.global_addr {
                    if let Operation::Move(_, ref val, _) = *op {
                        // No need to resolve here, as the constant
                        // was found by just binary scanning,
                        self.call_found = val.iter()
                            .flat_map(|x| x.if_constant())
                            .any(|x| x == global_addr.as_u64());
                    }
                } else {
                    self.call_found = address == self.middle_of_func;
                }
            }
        }
        if self.call_found && !self.first_branch {
            ctrl.end_analysis();
            return;
        }
        match op {
            Operation::Move(_, val, _) => {
                if !self.mov_u32_max_seen && self.first_branch {
                    let val = ctrl.resolve(val);
                    if val.if_constant().map(|x| x as u32) == Some(u32::max_value()) {
                        self.mov_u32_max_seen = true;
                    }
                }
            }
            Operation::Jump { condition, .. } => {
                if self.mov_u32_max_seen {
                    let condition = ctrl.resolve(condition);
                    let client_selection = condition.if_arithmetic_eq()
                        .and_either(|x| x.if_constant())
                        .and_then(|(c, op)| match c == 0 {
                            true => op.if_memory(),
                            false => None,
                        })
                        .map(|mem| {
                            self.ctx.sub(
                                &mem.address,
                                &self.ctx.constant(11 * 4),
                            )
                        });
                    if let Some(csl) = client_selection {
                        self.result = Some(csl);
                    }
                }
                self.first_branch = false;
            }
            Operation::Call(..) => {
                self.first_branch = false;
            }
            _ => (),
        }
    }
}

// Candidates are either a global ref with Some(global), or a call with None
pub fn is_outside_game_screen<'a>(
    analysis: &mut Analysis<'a, ExecutionStateX86<'a>>,
) -> Option<VirtualAddress> {
    let game_screen_rclick = analysis.game_screen_rclick().game_screen_rclick?;
    struct Analyzer<'a, 'b, E: ExecutionState<'a>> {
        result: Option<E::VirtualAddress>,
        args: &'b ArgCache<'a, E>,
    }

    impl<'a, 'b, E: ExecutionState<'a>> scarf::Analyzer<'a> for Analyzer<'a, 'b, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
            match op {
                Operation::Jump { .. } => {
                    ctrl.end_analysis();
                }
                Operation::Call(to) => {
                    let to = ctrl.resolve(to);
                    let arg1 = ctrl.resolve(&self.args.on_call(0));
                    let arg1 = unwrap_sext(&arg1);
                    let arg2 = ctrl.resolve(&self.args.on_call(1));
                    let arg2 = unwrap_sext(&arg2);
                    if let Some(dest) = to.if_constant() {
                        if arg1.if_mem16().is_some() && arg2.if_mem16().is_some() {
                            self.result = Some(E::VirtualAddress::from_u64(dest));
                            ctrl.end_analysis();
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut analyzer = Analyzer {
        result: None,
        args: &analysis.arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, game_screen_rclick);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

fn unwrap_sext(operand: &Rc<Operand>) -> &Rc<Operand> {
    match operand.ty {
        scarf::operand::OperandType::SignExtend(ref val, ..) => val,
        _ => operand,
    }
}

fn if_float_to_int(operand: &Rc<Operand>) -> Option<&Rc<Operand>> {
    match operand.ty {
        scarf::operand::OperandType::Arithmetic(ref arith)
            if arith.ty == scarf::operand::ArithOpType::FloatToInt => Some(&arith.left),
        _ => None,
    }
}

fn if_int_to_float(operand: &Rc<Operand>) -> Option<&Rc<Operand>> {
    match operand.ty {
        scarf::operand::OperandType::Arithmetic(ref arith)
            if arith.ty == scarf::operand::ArithOpType::IntToFloat => Some(&arith.left),
        _ => None,
    }
}

fn if_f32_div(operand: &Rc<Operand>) -> Option<(&Rc<Operand>, &Rc<Operand>)> {
    match operand.ty {
        scarf::operand::OperandType::ArithmeticF32(ref arith)
            if arith.ty == scarf::operand::ArithOpType::Div => Some((&arith.left, &arith.right)),
        _ => None,
    }
}

pub fn game_coord_conversion<'a>(
    analysis: &mut Analysis<'a, ExecutionStateX86<'a>>,
) -> GameCoordConversion {
    let mut result = GameCoordConversion::default();
    let game_screen_rclick = match analysis.game_screen_rclick().game_screen_rclick {
        Some(s) => s,
        None => return result,
    };
    let is_outside_game_screen = match analysis.is_outside_game_screen() {
        Some(s) => s,
        None => return result,
    };

    // Search for the collowing start in game_screen_rclick:
    // if is_outside_game_screen(event.x, event.y) == 0 {
    //     convert_screen_to_game(event, &mut out_xy);
    //     ...
    // } else {
    //     ...
    // }

    struct Analyzer<'a, 'b, E: ExecutionState<'a>> {
        depth: u32,
        result: &'b mut GameCoordConversion,
        set_eax_to_zero: bool,
        is_outside_game_screen: E::VirtualAddress,
        is_outside_game_screen_seen: bool,
        ctx: &'a OperandContext,
        args: &'b ArgCache<'a, E>,
    }

    impl<'a, 'b, E: ExecutionState<'a>> Analyzer<'a, 'b, E> {
        fn is_event_pos_in_game_coords_call<'e, A: scarf::Analyzer<'e>>(
            &self,
            ctrl: &mut Control<'e, '_, '_, A>,
        ) -> bool {
            let arg2 = ctrl.resolve(&self.args.on_call(1));
            arg2 == self.args.on_entry(0)
        }

        // Check for screen_x + mem16[&event.x] / scale
        fn check_move(val: &Rc<Operand>) -> Option<(&Rc<Operand>, &Rc<Operand>, u32)> {
            val.if_arithmetic_add()
                .and_either(|x| x.if_mem32().map(|_| x))
                .and_then(|(screen_coord, other)| {
                    if_float_to_int(other)
                        .and_then(if_f32_div)
                        .and_then(|(l, divisor)| {
                            if_int_to_float(l)
                                .map(unwrap_sext)
                                .and_then(|x| x.if_mem16()?.if_arithmetic_add())
                                .and_either(|x| x.if_constant())
                                .map(|(c, _)| (screen_coord, divisor, c as u32))
                        })
                })
        }
    }

    impl<'a, 'b, E: ExecutionState<'a>> scarf::Analyzer<'a> for Analyzer<'a, 'b, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
            if self.set_eax_to_zero {
                self.set_eax_to_zero = false;
                let (exec_state, i) = ctrl.exec_state();
                exec_state.move_to(&DestOperand::Register64(Register(0)), self.ctx.const_0(), i);
                return;
            }
            match op {
                Operation::Call(to) => {
                    let to = ctrl.resolve(to);
                    if let Some(dest) = to.if_constant() {
                        if !self.is_outside_game_screen_seen {
                            if dest == self.is_outside_game_screen.as_u64() {
                                self.is_outside_game_screen_seen = true;
                                self.set_eax_to_zero = true;
                            }
                            return;
                        }

                        if self.depth == 0 {
                            if self.is_event_pos_in_game_coords_call(ctrl) {
                                self.depth += 1;
                                ctrl.inline(self, E::VirtualAddress::from_u64(dest));
                                ctrl.skip_operation();
                                self.depth -= 1;
                            }
                        } else if self.depth == 3 {
                            ctrl.end_analysis();
                            return;
                        } else {
                            self.depth += 1;
                            ctrl.inline(self, E::VirtualAddress::from_u64(dest));
                            ctrl.skip_operation();
                            self.depth -= 1;
                        }
                        if self.result.screen_x.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                }
                Operation::Move(_, val, None) => {
                    if self.depth != 0 {
                        let val = ctrl.resolve(val);
                        let result = Self::check_move(&val);
                        if let Some((screen_coord, scale, struct_offset)) = result {
                            if struct_offset == 0x12 {
                                self.result.screen_x = Some(screen_coord.clone());
                                self.result.scale = Some(scale.clone());
                            } else {
                                self.result.screen_y = Some(screen_coord.clone());
                            }
                            if self.result.screen_x.is_some() && self.result.screen_y.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut analyzer = Analyzer {
        result: &mut result,
        depth: 0,
        set_eax_to_zero: false,
        is_outside_game_screen_seen: false,
        is_outside_game_screen,
        ctx,
        args: &analysis.arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, game_screen_rclick);
    analysis.analyze(&mut analyzer);

    result
}

pub fn game_screen_rclick<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> GameScreenRClick<E::VirtualAddress> {
    let binary = analysis.binary;

    // units_dat_rlick_order is accessed by get_rclick_order,
    // which is called/inlined by show_rclick_error_if_needed,
    // which is recognized from moving -1 into a local at start of the function,
    // which also contains loop over client selection (while ptr != &client_selection[0])
    // game_screen_rclick should be only caller of show_rclick_error_if_needed

    let units_dat = analysis.dat_virtual_address(DatType::Units);
    let uses = units_dat.and_then(|(dat, dat_table_size)| {
        binary.read_u32(dat + 0x1c * dat_table_size).ok()
    }).map(|rclick_order| {
        let addr = E::VirtualAddress::from_u64(rclick_order as u64);
        find_functions_using_global(analysis, addr)
            .into_iter()
            .map(|x| (x.use_address, Some(addr)))
            .collect::<Vec<_>>()
    }).unwrap_or_else(|| Vec::new());
    let result = game_screen_rclick_inner(analysis, &uses);
    let result = match result {
        ResultOrEntries::Entries(entries) => {
            let callers = entries.iter().flat_map(|&f| {
                find_callers(analysis, f).into_iter().map(|x| (x, None))
            }).collect::<Vec<_>>();
            game_screen_rclick_inner(analysis, &callers)
        }
        ResultOrEntries::Result(o) => ResultOrEntries::Result(o),
    };

    match result {
        ResultOrEntries::Result((rclick, csl)) => GameScreenRClick {
            client_selection: Some(csl),
            game_screen_rclick: Some(rclick),
        },
        ResultOrEntries::Entries(..) => GameScreenRClick {
            client_selection: None,
            game_screen_rclick: None,
        },
    }
}
