use std::hash::{Hash, Hasher};

use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::OperandHashByAddress;
use scarf::{BinaryFile, DestOperand, Operand, OperandCtx, Operation};

use crate::analysis::{AnalysisCtx};
use crate::hash_map::HashMap;
use crate::util::{ControlExt, bumpvec_with_capacity};

/// Converts return values of calls to Custom(x) representing the function,
/// and allows converting the Custom(x) to inlined return value of the function.
/// (Assumes no arguments to functions)
pub struct CallTracker<'acx, 'e, E: ExecutionState<'e>> {
    func_to_id: HashMap<FuncInput<'acx, 'e, E::VirtualAddress>, Operand<'e>>,
    /// (input, func return once analyzed)
    id_to_func:
        BumpVec<'acx, (FuncInput<'acx, 'e, E::VirtualAddress>, Option<Option<Operand<'e>>>)>,
    first_custom: u32,
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
struct FuncInput<'acx, 'e, Va: VirtualAddress> {
    address: Va,
    constraint: Option<Operand<'e>>,
    state: &'acx [(DestOperand<'e>, Operand<'e>)],
}

impl<'acx, 'e, Va: VirtualAddress> Hash for FuncInput<'acx, 'e, Va> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.address.hash(state);
        if let Some(c) = self.constraint {
            0u8.hash(state);
            OperandHashByAddress(c).hash(state);
        } else {
            1u8.hash(state);
        }
        self.state.len().hash(state);
        for (dest, op) in self.state {
            // Would be nice to hash entire dest though, but not super critical
            // since hash collisions likely won't happen with how this is currently used..
            std::mem::discriminant(dest).hash(state);
            OperandHashByAddress(*op).hash(state);
        }
    }
}

impl<'acx, 'e, E: ExecutionState<'e>> CallTracker<'acx, 'e, E> {
    pub(crate) fn with_capacity(
        actx: &'acx AnalysisCtx<'e, E>,
        first_custom: u32,
        cap: usize,
    ) -> CallTracker<'acx, 'e, E> {
        CallTracker {
            func_to_id: HashMap::with_capacity_and_hasher(cap, Default::default()),
            id_to_func: bumpvec_with_capacity(cap, &actx.bump),
            first_custom,
            binary: actx.binary,
            ctx: actx.ctx,
        }
    }

    /// Registers and simulates a call to specific address, also skips current operation.
    ///
    /// Note that this mean it clobbers volatile registers, usually Analyzer::operation() wants
    /// to do this after everything else at call operation has been checked.
    pub fn add_call<A: scarf::Analyzer<'e>>(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, A>,
        address: E::VirtualAddress,
    ) {
        let ctx = ctrl.ctx();
        let custom = self.func_to_custom(ctx, address, &[]);
        ctrl.do_call_with_result(custom);
    }

    /// Registers and simulates a call to specific address, also skips current operation,
    /// saving specified (DestOperand, Operand) pairs as input if/when the function
    /// is executed later.
    ///
    /// Note that this mean it clobbers volatile registers, usually Analyzer::operation() wants
    /// to do this after everything else at call operation has been checked.
    pub fn add_call_with_state<A: scarf::Analyzer<'e>>(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, A>,
        address: E::VirtualAddress,
        state: &'acx [(DestOperand<'e>, Operand<'e>)],
    ) {
        let ctx = ctrl.ctx();
        let custom = self.func_to_custom(ctx, address, state);
        ctrl.do_call_with_result(custom);
    }

    pub fn add_call_preserve_esp<A: scarf::Analyzer<'e>>(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, A>,
        address: E::VirtualAddress,
    ) {
        let ctx = ctrl.ctx();
        let custom = self.func_to_custom(ctx, address, &[]);
        ctrl.skip_call_preserve_esp();
        ctrl.exec_state().set_register(0, custom);
    }

    fn func_to_custom(
        &mut self,
        ctx: OperandCtx<'e>,
        address: E::VirtualAddress,
        state: &'acx [(DestOperand<'e>, Operand<'e>)],
    ) -> Operand<'e> {
        let input = FuncInput {
            address,
            constraint: None,
            state,
        };
        let entry = self.func_to_id.entry(input);
        let id_to_func = &mut self.id_to_func;
        let new_id = id_to_func.len() as u32 + self.first_custom;
        let &mut custom = entry.or_insert_with(|| {
            id_to_func.push((input, None));
            ctx.custom(new_id)
        });
        custom
    }

    /// Registers and simulates a call to specific address, resolving immeditaly
    /// instead of add_call which produces Custom(x). Also skips current operation.
    ///
    /// Note that this mean it clobbers volatile registers, usually Analyzer::operation() wants
    /// to do this after everything else at call operation has been checked.
    pub fn add_call_resolve<A: scarf::Analyzer<'e>>(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, A>,
        address: E::VirtualAddress,
    ) {
        self.add_call_resolve_with_branch_limit(ctrl, address, u32::MAX, true);
    }

    /// Registers and simulates a call to specific address, resolving immeditaly
    /// instead of add_call which produces Custom(x). Also skips current operation.
    ///
    /// Returns true if was able to simulate the call with given branch limit.
    ///
    /// Note that this mean it clobbers volatile registers, usually Analyzer::operation() wants
    /// to do this after everything else at call operation has been checked.
    pub fn add_call_resolve_with_branch_limit<A: scarf::Analyzer<'e>>(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, A>,
        address: E::VirtualAddress,
        limit: u32,
        always_set_result: bool,
    ) -> bool {
        let ctx = ctrl.ctx();
        let custom = self.func_to_custom(ctx, address, &[]);
        let val = custom.if_custom().and_then(|x| self.resolve_custom(x, limit));
        if let Some(val) = val {
            let val = ctrl.resolve(val);
            ctrl.do_call_with_result(val);
            true
        } else {
            if always_set_result {
                ctrl.do_call_with_result(custom);
            }
            false
        }
    }

    /// Like add_call_resolve, but allows declaring constraint (for arguments)
    /// that is used for determining if jump should always be taken/not.
    pub fn add_call_resolve_with_constraint<A: scarf::Analyzer<'e>>(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, A>,
        address: E::VirtualAddress,
        constraint: Operand<'e>,
    ) {
        let ctx = ctrl.ctx();
        let input = FuncInput {
            address,
            constraint: Some(constraint),
            state: &[],
        };
        let entry = self.func_to_id.entry(input);
        let id_to_func = &mut self.id_to_func;
        let new_id = id_to_func.len() as u32 + self.first_custom;
        let &mut custom = entry.or_insert_with(|| {
            id_to_func.push((input, None));
            ctx.custom(new_id)
        });
        let new_esp = ctrl.get_new_esp_for_call();
        let exec_state = ctrl.exec_state();
        exec_state.set_register(4, new_esp);
        let val = exec_state.resolve(self.resolve_calls(custom));
        ctrl.pop_stack();
        ctrl.do_call_with_result(val)
    }

    /// Like resolve_calls but allows limiting analysis to only for shorter functions.
    pub fn resolve_calls_with_branch_limit(
        &mut self,
        val: Operand<'e>,
        limit: u32,
    ) -> Operand<'e> {
        self.ctx.transform(val, 8, |op| {
            if let Some(idx) = op.if_custom() {
                self.resolve_custom(idx, limit)
            } else {
                None
            }
        })
    }

    pub fn resolve_custom(&mut self, custom_id: u32, limit: u32) -> Option<Operand<'e>> {
        let ctx = self.ctx;
        let binary = self.binary;
        let index = custom_id.checked_sub(self.first_custom)? as usize;
        let &mut (input, ref mut result) = self.id_to_func.get_mut(index)?;
        let addr = input.address;
        let constraint = input.constraint;
        let state = input.state;
        *result.get_or_insert_with(|| {
            analyze_func_return_c::<E>(addr, ctx, binary, constraint, state, limit)
        })
    }

    /// Converts any `Custom` (which are from `add_call()`) in `val` to
    /// **resolved function return value relative to start of the called function**.
    ///
    /// That is, if the function returns anything depending on arguments, to resolve it
    /// in context of the parent function, you'll need to have kept state at point of the
    /// call and resolve on that (After fixing stack to consider offset from call instruction).
    pub fn resolve_calls(&mut self, val: Operand<'e>) -> Operand<'e> {
        self.resolve_calls_with_branch_limit(val, u32::MAX)
    }

    /// If `val` is `Custom(x)` or `Custom(x) & mask`, resolves val (Discarding mask if any),
    /// otherwise just returns `val`.
    ///
    /// Can be used as a faster alternative to resolve_calls that doesn't have to walk through
    /// operand tree, when it is known that the value may be just a return value of a function.
    ///
    /// Also limits branch limit of inner function to be very low.
    pub fn resolve_simple(&mut self, val: Operand<'e>) -> Operand<'e> {
        let inner = Operand::and_masked(val).0;
        if let Some(idx) = inner.if_custom() {
            if let Some(result) = self.resolve_custom(idx, 4) {
                return result;
            }
        }
        val
    }

    pub fn custom_id_to_func(&self, val: u32) -> Option<E::VirtualAddress> {
        let index = val.checked_sub(self.first_custom)?;
        Some(self.id_to_func.get(index as usize)?.0.address)
    }
}

pub(crate) fn analyze_func_return<'e, E: ExecutionState<'e>>(
    func: E::VirtualAddress,
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
) -> Option<Operand<'e>> {
    analyze_func_return_c::<E>(func, ctx, binary, None, &[], u32::MAX)
}

fn analyze_func_return_c<'e, E: ExecutionState<'e>>(
    func: E::VirtualAddress,
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    constraint: Option<Operand<'e>>,
    init_state: &[(DestOperand<'e>, Operand<'e>)],
    branch_limit: u32,
) -> Option<Operand<'e>> {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: Option<Operand<'e>>,
        phantom: std::marker::PhantomData<(*const E, &'e ())>,
        prev_ins_address: E::VirtualAddress,
        constraint: Option<Operand<'e>>,
        branch_limit: u32,
    }

    impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if let Operation::Return(..) = *op {
                let ctx = ctrl.ctx();
                let eax = ctrl.resolve_register(0);
                match self.result {
                    Some(old) => {
                        if old != eax {
                            self.result = Some(ctx.new_undef());
                            ctrl.end_analysis();
                        }
                    }
                    None => {
                        self.result = Some(eax);
                    }
                }
            }
            if let Operation::Call(..) = *op {
                // Avoid security_cookie_check
                // Detect it by prev instruction being xor ecx, ebp
                let prev_ins_len = ctrl.address().as_u64()
                    .wrapping_sub(self.prev_ins_address.as_u64());
                if E::VirtualAddress::SIZE == 4 {
                    if prev_ins_len == 2 {
                        let binary = ctrl.binary();
                        if let Ok(prev_ins_bytes) =
                            binary.slice_from_address(self.prev_ins_address, 2)
                        {
                            if prev_ins_bytes == &[0x33, 0xcd] {
                                ctrl.skip_operation();
                            }
                        }
                    }
                } else {
                    // xor rcx, rsp on 64bit
                    if prev_ins_len == 3 {
                        let binary = ctrl.binary();
                        if let Ok(prev_ins_bytes) =
                            binary.slice_from_address(self.prev_ins_address, 3)
                        {
                            if prev_ins_bytes == &[0x48, 0x33, 0xcc] {
                                ctrl.skip_operation();
                            }
                        }
                    }
                }
            }
            if let Operation::Jump { condition, .. } = *op {
                if let Some(constraint) = self.constraint {
                    let ctx = ctrl.ctx();
                    if condition != ctx.const_1() {
                        let state = ctrl.exec_state();
                        state.add_resolved_constraint(
                            scarf::exec_state::Constraint::new(constraint)
                        );
                    }
                }
            }
            self.prev_ins_address = ctrl.address();
        }

        fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
            if self.branch_limit == 0 {
                ctrl.end_analysis();
                self.result = None;
                return;
            }
            self.branch_limit -= 1;
            self.prev_ins_address = E::VirtualAddress::from_u64(0);
        }
    }
    let mut analyzer = Analyzer::<E> {
        result: None,
        phantom: Default::default(),
        prev_ins_address: E::VirtualAddress::from_u64(0),
        constraint,
        branch_limit,
    };

    let mut state = E::initial_state(ctx, binary);
    for &(ref dest, val) in init_state {
        state.move_to(dest, val);
    }
    let mut analysis = FuncAnalysis::with_state(binary, ctx, func, state);
    analysis.analyze(&mut analyzer);
    analyzer.result
        .filter(|x| !x.is_undefined())
}
