use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::OperandHashByAddress;
use scarf::{BinaryFile, Operand, OperandCtx, Operation};

use crate::{AnalysisCtx, ControlExt, bumpvec_with_capacity};
use crate::hash_map::HashMap;

/// Converts return values of calls to Custom(x) representing the function,
/// and allows converting the Custom(x) to inlined return value of the function.
/// (Assumes no arguments to functions)
pub struct CallTracker<'acx, 'e, E: ExecutionState<'e>> {
    func_to_id: HashMap<(E::VirtualAddress, Option<OperandHashByAddress<'e>>), Operand<'e>>,
    /// (func address, constraint, func return once analyzed)
    id_to_func:
        BumpVec<'acx, (E::VirtualAddress, Option<Operand<'e>>, Option<Option<Operand<'e>>>)>,
    first_custom: u32,
    binary: &'e BinaryFile<E::VirtualAddress>,
    ctx: OperandCtx<'e>,
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
        let entry = self.func_to_id.entry((address, None));
        let id_to_func = &mut self.id_to_func;
        let new_id = id_to_func.len() as u32 + self.first_custom;
        let &mut custom = entry.or_insert_with(|| {
            id_to_func.push((address, None, None));
            ctx.custom(new_id)
        });
        ctrl.do_call_with_result(custom);
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
        let ctx = ctrl.ctx();
        let entry = self.func_to_id.entry((address, None));
        let id_to_func = &mut self.id_to_func;
        let new_id = id_to_func.len() as u32 + self.first_custom;
        let &mut custom = entry.or_insert_with(|| {
            id_to_func.push((address, None, None));
            ctx.custom(new_id)
        });
        let val = ctrl.resolve(self.resolve_calls(custom));
        ctrl.do_call_with_result(val)
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
        let entry = self.func_to_id.entry((address, Some(constraint.hash_by_address())));
        let id_to_func = &mut self.id_to_func;
        let new_id = id_to_func.len() as u32 + self.first_custom;
        let &mut custom = entry.or_insert_with(|| {
            id_to_func.push((address, Some(constraint), None));
            ctx.custom(new_id)
        });
        let exec_state = ctrl.exec_state();
        exec_state.move_to(
            &scarf::DestOperand::Register64(4),
            ctx.sub_const(ctx.register(4), E::VirtualAddress::SIZE.into()),
        );
        let val = exec_state.resolve(self.resolve_calls(custom));
        exec_state.move_to(
            &scarf::DestOperand::Register64(4),
            ctx.add_const(ctx.register(4), E::VirtualAddress::SIZE.into()),
        );
        ctrl.do_call_with_result(val)
    }

    /// Converts any `Custom` (which are from `add_call()`) in `val` to
    /// **resolved function return value relative to start of the called function**.
    ///
    /// That is, if the function returns anything depending on arguments, to resolve it
    /// in context of the parent function, you'll need to have kept state at point of the
    /// call and resolve on that (After fixing stack to consider offset from call instruction).
    pub fn resolve_calls(&mut self, val: Operand<'e>) -> Operand<'e> {
        self.ctx.transform(val, 8, |op| {
            if let Some(idx) = op.if_custom() {
                let ctx = self.ctx;
                let binary = self.binary;
                if let Some((addr, constraint, result)) = idx.checked_sub(self.first_custom)
                    .and_then(|x| self.id_to_func.get_mut(x as usize))
                {
                    *result.get_or_insert_with(|| {
                        analyze_func_return_c::<E>(*addr, ctx, binary, *constraint)
                    })
                } else {
                    None
                }
            } else {
                None
            }
        })
    }

    pub fn custom_id_to_func(&self, val: u32) -> Option<E::VirtualAddress> {
        let index = val.checked_sub(self.first_custom)?;
        Some(self.id_to_func.get(index as usize)?.0)
    }
}

pub(crate) fn analyze_func_return<'e, E: ExecutionState<'e>>(
    func: E::VirtualAddress,
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
) -> Option<Operand<'e>> {
    analyze_func_return_c::<E>(func, ctx, binary, None)
}

fn analyze_func_return_c<'e, E: ExecutionState<'e>>(
    func: E::VirtualAddress,
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    constraint: Option<Operand<'e>>,
) -> Option<Operand<'e>> {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: Option<Operand<'e>>,
        phantom: std::marker::PhantomData<(*const E, &'e ())>,
        prev_ins_address: E::VirtualAddress,
        constraint: Option<Operand<'e>>,
    }

    impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if let Operation::Return(..) = *op {
                let ctx = ctrl.ctx();
                let eax = ctrl.resolve(ctx.register(0));
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

        fn branch_start(&mut self, _ctrl: &mut Control<'e, '_, '_, Self>) {
            self.prev_ins_address = E::VirtualAddress::from_u64(0);
        }
    }
    let mut analyzer = Analyzer::<E> {
        result: None,
        phantom: Default::default(),
        prev_ins_address: E::VirtualAddress::from_u64(0),
        constraint,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, func);
    analysis.analyze(&mut analyzer);
    analyzer.result
        .filter(|x| !x.is_undefined())
}
