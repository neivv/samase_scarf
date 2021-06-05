use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{BinaryFile, Operand, OperandCtx, Operation};

use crate::{AnalysisCtx, ControlExt, bumpvec_with_capacity};
use crate::hash_map::HashMap;

/// Converts return values of calls to Custom(x) representing the function,
/// and allows converting the Custom(x) to inlined return value of the function.
/// (Assumes no arguments to functions)
pub struct CallTracker<'acx, 'e, E: ExecutionState<'e>> {
    func_to_id: HashMap<E::VirtualAddress, Operand<'e>>,
    /// (func address, func return once analyzed)
    id_to_func: BumpVec<'acx, (E::VirtualAddress, Option<Option<Operand<'e>>>)>,
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
        let entry = self.func_to_id.entry(address);
        let id_to_func = &mut self.id_to_func;
        let new_id = id_to_func.len() as u32 + self.first_custom;
        let &mut custom = entry.or_insert_with(|| {
            id_to_func.push((address, None));
            ctx.custom(new_id)
        });
        ctrl.do_call_with_result(custom);
    }

    pub fn resolve_calls(&mut self, val: Operand<'e>) -> Operand<'e> {
        self.ctx.transform(val, 8, |op| {
            if let Some(idx) = op.if_custom() {
                let ctx = self.ctx;
                let binary = self.binary;
                if let Some((addr, result)) = idx.checked_sub(self.first_custom)
                    .and_then(|x| self.id_to_func.get_mut(x as usize))
                {
                    *result.get_or_insert_with(|| {
                        analyze_func_return::<E>(*addr, ctx, binary)
                    })
                } else {
                    None
                }
            } else {
                None
            }
        })
    }
}

pub(crate) fn analyze_func_return<'e, E: ExecutionState<'e>>(
    func: E::VirtualAddress,
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
) -> Option<Operand<'e>> {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: Option<Operand<'e>>,
        phantom: std::marker::PhantomData<(*const E, &'e ())>,
        prev_ins_address: E::VirtualAddress,
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
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, func);
    analysis.analyze(&mut analyzer);
    analyzer.result
        .filter(|x| !x.is_undefined())
}
