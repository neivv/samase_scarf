use bumpalo::collections::Vec as BumpVec;
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{OperandHashByAddress};
use scarf::{DestOperand, Operand, Operation};

use crate::{
    entry_of_until, EntryOf, OptionExt, OperandExt, bumpvec_with_capacity,
};
use crate::hash_map::{HashMap, HashSet};
use super::{DatPatchContext, DatPatch, GrpTexturePatch, reloc_address_of_instruction};

pub(crate) fn grp_index_patches<'a, 'e, E: ExecutionState<'e>>(
    dat_ctx: &mut DatPatchContext<'a, '_, 'e, E>,
) -> Option<()> {
    // Hook any indexing of wirefram/grpwire/tranwire grp/ddsgrps
    // so that they can be indexed by using .dat value instead of plain unit id

    let analysis = dat_ctx.analysis;
    let cache = &mut dat_ctx.cache;
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let functions = cache.functions();
    let text = dat_ctx.text;
    let text_end = text.virtual_address + text.virtual_size;

    let mut checked_refs = HashSet::with_capacity_and_hasher(16, Default::default());
    // Map func -> returned grp type
    let mut functions_returning_grp = HashMap::with_capacity_and_hasher(8, Default::default());
    // Map operand -> grp type
    let grp_op_inputs = [
        (cache.grpwire_grp(analysis)?, GrpType::Grp),
        (cache.grpwire_ddsgrp(analysis)?, GrpType::DdsGrp),
        (cache.tranwire_grp(analysis)?, GrpType::Grp),
        (cache.tranwire_ddsgrp(analysis)?, GrpType::DdsGrp),
        (cache.wirefram_ddsgrp(analysis)?, GrpType::DdsGrpSet),
        // Function returns
        (ctx.custom(0), GrpType::Grp),
        (ctx.custom(1), GrpType::DdsGrp),
        (ctx.custom(2), GrpType::DdsGrpSet),
    ];
    let status_screen = cache.status_screen(analysis)?;
    let init_status_screen = cache.init_status_screen(analysis)?;
    let mut grp_operands = HashMap::with_capacity_and_hasher(16, Default::default());
    let mut refs_to_check = bumpvec_with_capacity(8, bump);
    for &(oper, grp) in &grp_op_inputs {
        grp_operands.insert(oper.hash_by_address(), grp);
        let addr = oper.if_constant()
            .or_else(|| oper.if_memory()?.if_constant_address())
            .map(|x| E::VirtualAddress::from_u64(x));
        if let Some(addr) = addr {
            let function_finder = cache.function_finder();
            for i in 0..2 {
                let addr = addr + i * E::VirtualAddress::SIZE;
                let globals = function_finder.find_functions_using_global(analysis, addr);
                for global in globals {
                    if global.use_address >= text.virtual_address && global.use_address < text_end {
                        refs_to_check.push(global.use_address);
                    }
                }
                // Also add ddsgrp.field1 which may be referenced directly
                if grp != GrpType::DdsGrp {
                    break;
                }
            }
        }
    }
    // Functions that are known to refer the grps but aren't relevant
    let mut bad_functions = bumpvec_with_capacity(4, bump);
    bad_functions.push(init_status_screen);
    while let Some(ref_addr) = refs_to_check.pop() {
        if !checked_refs.insert(ref_addr) {
            continue;
        }
        entry_of_until(binary, &functions, ref_addr, |entry| {
            if bad_functions.contains(&entry) {
                return EntryOf::Ok(());
            }
            let mut analyzer = GrpIndexAnalyzer {
                ref_addr,
                dat_ctx,
                checked_refs: &mut checked_refs,
                functions_returning_grp: &functions_returning_grp,
                grp_operands: &grp_operands,
                returns_grp: None,
                entry_of: EntryOf::Retry,
                first_branch: true,
                bad_functions: &mut bad_functions,
                entry,
                status_screen,
                inlining: false,
                inline_limit: 0,
                inline_fail: false,
                inline_this: ctx.const_0(),
            };
            let mut func_analysis = FuncAnalysis::new(binary, ctx, entry);
            func_analysis.analyze(&mut analyzer);
            let entry_of = analyzer.entry_of;
            if let Some(grp) = analyzer.returns_grp {
                if functions_returning_grp.insert(entry, grp).is_none() {
                    let callers = dat_ctx.cache.function_finder().find_callers(analysis, entry);
                    for address in callers {
                        refs_to_check.push(address);
                    }
                }
            }
            entry_of
        });
    }
    Some(())
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
enum GrpType {
    // Single .grp
    Grp,
    // Single .dds.grp
    DdsGrp,
    // Used by wirefram.ddsgrp, contains both .grp followed by sd/hd ddsgrps
    DdsGrpSet,
}

struct GrpIndexAnalyzer<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> {
    ref_addr: E::VirtualAddress,
    dat_ctx: &'a mut DatPatchContext<'b, 'acx, 'e, E>,
    checked_refs: &'a mut HashSet<E::VirtualAddress>,
    functions_returning_grp: &'a HashMap<E::VirtualAddress, GrpType>,
    grp_operands: &'a HashMap<OperandHashByAddress<'e>, GrpType>,
    returns_grp: Option<GrpType>,
    entry_of: EntryOf<()>,
    first_branch: bool,
    bad_functions: &'a mut BumpVec<'acx, E::VirtualAddress>,
    status_screen: Operand<'e>,
    entry: E::VirtualAddress,
    inlining: bool,
    inline_limit: u8,
    inline_fail: bool,
    inline_this: Operand<'e>,
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    GrpIndexAnalyzer<'a, 'b, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        fn is_stack(op: Operand<'_>) -> bool {
            op.if_arithmetic_sub()
                .filter(|x| x.1.if_constant().is_some())
                .map(|x| Operand::and_masked(x.0).0)
                .and_then(|x| x.if_register())
                .filter(|&x| x == 4)
                .is_some()
        }
        let ctx = ctrl.ctx();
        if self.inlining {
            match *op {
                Operation::Call(_) => {
                    self.inline_fail = true;
                    ctrl.end_analysis();
                }
                Operation::Return(_) => {
                    let eax = ctrl.resolve(ctx.register(0));
                    // Accept deref_this
                    let ok = ctrl.if_mem_word(eax)
                        .and_then(|x| x.if_no_offset())
                        .filter(|&x| x == self.inline_this)
                        .is_some();
                    self.inline_fail = !ok;
                    ctrl.end_analysis();
                }
                _ => (),
            }
            return;
        }
        if ctrl.address() <= self.ref_addr && ctrl.current_instruction_end() > self.ref_addr {
            self.entry_of = EntryOf::Ok(());
        }
        match *op {
            Operation::Jump { condition, .. } => {
                if self.first_branch {
                    // delete_status_screen is a function we don't need to care about;
                    // it starts with a check for status_screen != 0
                    let condition = ctrl.resolve(condition);
                    let checking_status_screen = crate::if_arithmetic_eq_neq(condition)
                        .map(|x| (x.0, x.1))
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0))
                        .filter(|&x| x == self.status_screen)
                        .is_some();
                    if checking_status_screen {
                        self.bad_functions.push(self.entry);
                        self.entry_of = EntryOf::Ok(());
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Call(dest) => {
                let dest = match ctrl.resolve(dest).if_constant() {
                    Some(dest) => E::VirtualAddress::from_u64(dest),
                    None => return,
                };
                if let Some(grp) = self.functions_returning_grp.get(&dest) {
                    let custom = match grp {
                        GrpType::Grp => 0,
                        GrpType::DdsGrp => 1,
                        GrpType::DdsGrpSet => 2,
                    };
                    let custom = ctx.custom(custom);
                    ctrl.skip_operation();
                    let exec_state = ctrl.exec_state();
                    exec_state.move_to(
                        &DestOperand::Register64(0),
                        custom,
                    );
                    self.checked_refs.insert(ctrl.address());
                    return;
                }

                let arg_cache = &self.dat_ctx.analysis.arg_cache;
                // Check for grp_frame_header(grp, frame_id, out1, out2)
                let arg1 = ctrl.resolve(arg_cache.on_call(0));
                let arg_match = self.grp_operands.get(&arg1.hash_by_address())
                    .map(|x| (*x, GrpType::Grp))
                    .or_else(|| {
                        let inner = ctrl.if_mem_word(arg1)?.address_op(ctx);
                        self.grp_operands.get(&inner.hash_by_address())
                            .map(|x| (*x, GrpType::DdsGrpSet))
                    })
                    .filter(|x| x.0 == x.1)
                    .map(|x| x.0);
                if let Some(_grp) = arg_match {
                    let arg3 = ctrl.resolve(arg_cache.on_call(2));
                    let arg4 = ctrl.resolve(arg_cache.on_call(3));
                    if is_stack(arg3) && is_stack(arg4) {
                        let binary = self.dat_ctx.binary;
                        let reloc_addr = arg1.if_memory()
                            .and_then(|x| x.if_constant_address())
                            .map(|x| E::VirtualAddress::from_u64(x))
                            .and_then(|x| reloc_address_of_instruction(ctrl, binary, x));
                        if let Some(addr) = reloc_addr {
                            self.checked_refs.insert(addr);
                        }
                        let address = ctrl.address();
                        if self.dat_ctx.patched_addresses.insert(address) {
                            self.dat_ctx.result.patches.push(DatPatch::GrpIndexHook(address));
                        }
                        return;
                    }
                }
                let ecx = ctrl.resolve(ctx.register(1));
                if let Some(&grp) = self.grp_operands.get(&ecx.hash_by_address()) {
                    if grp == GrpType::DdsGrpSet {
                        self.inlining = true;
                        self.inline_limit = 5;
                        self.inline_fail = false;
                        self.inline_this = ecx;
                        ctrl.inline(self, dest);
                        self.inlining = false;
                        ctrl.skip_operation();
                        if self.inline_fail {
                            // Custom(10) for potentially useful DdsGrpSet deref
                            let custom = ctx.custom(0x10);
                            let exec_state = ctrl.exec_state();
                            exec_state.move_to(
                                &DestOperand::Register64(0),
                                custom,
                            );
                        }
                    }
                }
            }
            Operation::Move(ref dest, val, None) => {
                let val = ctrl.resolve(val);
                let texture_index = val.if_arithmetic_add()
                    .and_either(|x| {
                        ctrl.if_mem_word(x)
                            .and_then(|x| {
                                // DdsGrpSet
                                Some(x.address().0)
                                    .filter(|x| x.if_custom() == Some(0x10))
                            })
                            .or_else(|| {
                                // DdsGrp.textures
                                ctrl.if_mem_word(x)
                                    .map(|x| {
                                        ctx.mem_sub_const_op(x, E::VirtualAddress::SIZE as u64)
                                    })
                                    .filter(|x| {
                                        self.grp_operands.get(&x.hash_by_address())
                                            .filter(|&&y| y == GrpType::DdsGrp)
                                            .is_some()
                                    })
                            })
                    })
                    .filter(|&(_, x)| x.if_arithmetic_mul_const(0x10).is_some());
                if let Some((base, index)) = texture_index {
                    let base = match super::unresolve(ctx, ctrl.exec_state(), base) {
                        Some(s) => s,
                        None => {
                            dat_warn!(self.dat_ctx, "Can't unresolve ddsgrp texture op {}", base);
                            return;
                        }
                    };
                    let index = match super::unresolve(ctx, ctrl.exec_state(), index) {
                        Some(s) => s,
                        None => {
                            dat_warn!(
                                self.dat_ctx, "Can't unresolve ddsgrp texture op {}",
                                index,
                            );
                            return;
                        }
                    };

                    // Move a custom oper instead so that later instructions don't get
                    // caught by this same check
                    ctrl.skip_operation();
                    let custom = ctx.custom(0x11);
                    let exec_state = ctrl.exec_state();
                    exec_state.move_to(dest, custom);
                    let address = ctrl.address();
                    if self.dat_ctx.patched_addresses.insert(address) {
                        let instruction_len = (ctrl.current_instruction_end().as_u64() as u8)
                            .wrapping_sub(address.as_u64() as u8);
                        let patch = GrpTexturePatch {
                            address,
                            instruction_len,
                            dest: dest.as_operand(ctx),
                            base,
                            index_bytes: index,
                        };
                        self.dat_ctx.result.patches.push(DatPatch::GrpTextureHook(patch));
                    }
                    return;
                }
            }
            Operation::Return(..) => {
                let eax = ctrl.resolve(ctx.register(0));
                if let Some(&grp) = self.grp_operands.get(&eax.hash_by_address()) {
                    self.returns_grp = Some(grp);
                    // Assuming that a function returning grp can't be otherwise interesting
                    self.entry_of = EntryOf::Ok(());
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        if self.inlining && self.inline_limit == 0 {
            self.inline_fail = true;
            ctrl.end_analysis();
        }
    }

    fn branch_end(&mut self, _ctrl: &mut Control<'e, '_, '_, Self>) {
        self.first_branch = false;
        self.inline_limit = self.inline_limit.saturating_sub(1);
    }
}
