use bumpalo::collections::Vec as BumpVec;
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{OperandHashByAddress};
use scarf::{Operand, Operation, OperandCtx};

use crate::analysis_find::{entry_of_until, EntryOf};
use crate::hash_map::{HashMap, HashSet};
use crate::unresolve::unresolve;
use crate::util::{ControlExt, ExecStateExt, OptionExt, OperandExt, bumpvec_with_capacity};
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
                after_current_custom_10_call: E::VirtualAddress::from_u64(0),
                current_custom10_register: None,
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
    /// Usually 0, when call results in Custom(10) (Assuming function call that returns
    /// &DdsGrpSet.dds_grps[..]), store the next instruction after that.
    /// Sometimes the function return value ddsgrp is no longer available, e.g
    /// code does `mov rax, [rax + 8]` to access textures, overwriting `rax`, in
    /// which case this will be patched to inject `mov rcx, rax` instruction to have
    /// ddsgrp still available in some register.
    after_current_custom_10_call: E::VirtualAddress,
    /// Register used to store this copy of `rax` on this current branch, when
    /// the `mov rcx, rax` was injected (In that case it would be `rcx`)
    current_custom10_register: Option<Operand<'e>>,
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    GrpIndexAnalyzer<'a, 'b, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        fn is_stack<'e>(op: Operand<'e>, ctx: OperandCtx<'e>) -> bool {
            op.if_sub_with_const()
                .map(|x| Operand::and_masked(x.0).0) == Some(ctx.register(4))
        }

        let ctx = ctrl.ctx();
        if self.inlining {
            match *op {
                Operation::Call(_) => {
                    self.inline_fail = true;
                    ctrl.end_analysis();
                }
                Operation::Return(_) => {
                    let eax = ctrl.resolve_register(0);
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
        let address = ctrl.address();
        if address <= self.ref_addr && ctrl.current_instruction_end() > self.ref_addr {
            self.entry_of = EntryOf::Ok(());
        }
        match *op {
            Operation::Jump { condition, .. } => {
                if self.first_branch {
                    // delete_status_screen is a function we don't need to care about;
                    // it starts with a check for status_screen != 0
                    let condition = ctrl.resolve(condition);
                    let checking_status_screen = condition.if_arithmetic_eq_neq_zero(ctx)
                        .filter(|x| x.0 == self.status_screen)
                        .is_some();
                    if checking_status_screen {
                        self.bad_functions.push(self.entry);
                        self.entry_of = EntryOf::Ok(());
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Call(dest) => {
                let dest = match ctrl.resolve_va(dest) {
                    Some(dest) => dest,
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
                    ctrl.set_register(0, custom);
                    self.checked_refs.insert(address);
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
                    if is_stack(arg3, ctx) && is_stack(arg4, ctx) {
                        let binary = self.dat_ctx.binary;
                        let reloc_addr = arg1.if_memory()
                            .and_then(|x| x.if_constant_address())
                            .map(|x| E::VirtualAddress::from_u64(x))
                            .and_then(|x| reloc_address_of_instruction(ctrl, binary, x));
                        if let Some(addr) = reloc_addr {
                            self.checked_refs.insert(addr);
                        }
                        if self.dat_ctx.patched_addresses.insert(address) {
                            self.dat_ctx.result.patches.push(DatPatch::GrpIndexHook(address));
                        }
                        return;
                    }
                }
                let ecx = ctrl.resolve_register(1);
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
                            ctrl.set_register(0, custom);
                            self.after_current_custom_10_call = ctrl.current_instruction_end();
                            // Set rcx and rdx to custom; if after_current_custom_10_call
                            // is needed since rax is clobbered, rdx or rcx still storing
                            // Custom(12) means that they are safe to use as copy of rax.
                            let custom = ctx.custom(0x12);
                            ctrl.set_register(1, custom);
                            ctrl.set_register(2, custom);
                        }
                    }
                }
            }
            Operation::Move(ref dest, val, None) => {
                let val = ctrl.resolve(val);
                if let Some((base, index)) = self.texture_index_from_op(val, ctrl)
                    .and_then(|(base, index)| self.unresolve_base_index(base, index, ctrl))
                {
                    // Move a custom oper instead so that later instructions don't get
                    // caught by this same check
                    ctrl.skip_operation();
                    let custom = ctx.custom(0x11);
                    ctrl.move_unresolved(dest, custom);
                    if self.dat_ctx.patched_addresses.insert(address) {
                        let instruction_len = (ctrl.current_instruction_end().as_u64() as u8)
                            .wrapping_sub(address.as_u64() as u8);
                        let patch = GrpTexturePatch {
                            address,
                            instruction_len,
                            dest: dest.as_operand(ctx),
                            base,
                            index_bytes: index,
                            mem_offset: 0,
                            mem_size: 0,
                        };
                        self.dat_ctx.result.patches.push(DatPatch::GrpTextureHook(patch));
                    }
                    return;
                }
                if let Some(mem) = val.unwrap_sext().if_memory() {
                    let (base, offset) = mem.address();
                    if let Ok(offset) = u8::try_from(offset) {
                        if let Some((base, index)) = self.texture_index_from_op(base, ctrl)
                            .and_then(|(base, index)| self.unresolve_base_index(base, index, ctrl))
                        {
                            // Move a custom oper instead so that later instructions don't get
                            // caught by this same check
                            // (Maybe should add sign extend if it was in original `val`..)
                            ctrl.skip_operation();
                            let custom = ctx.custom(0x13);
                            ctrl.move_unresolved(dest, custom);
                            if self.dat_ctx.patched_addresses.insert(address) {
                                let instruction_len =
                                    (ctrl.current_instruction_end().as_u64() as u8)
                                        .wrapping_sub(address.as_u64() as u8);
                                let patch = GrpTexturePatch {
                                    address,
                                    instruction_len,
                                    // Assuming that (rax & ffff_ffff) can just use
                                    // rax instead. Makes patching bit simpler.
                                    dest: Operand::and_masked(dest.as_operand(ctx)).0,
                                    base,
                                    index_bytes: index,
                                    mem_offset: offset,
                                    mem_size: mem.size.bytes() as u8,
                                };
                                self.dat_ctx.result.patches.push(DatPatch::GrpTextureHook(patch));
                            }
                        }
                    }
                }
            }
            Operation::Return(..) => {
                let eax = ctrl.resolve_register(0);
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
        self.after_current_custom_10_call = E::VirtualAddress::from_u64(0);
        self.current_custom10_register = None;
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

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> GrpIndexAnalyzer<'a, 'b, 'acx, 'e, E> {
    fn try_add_patch_for_ddsgrp_set_deref(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
    ) -> Option<Operand<'e>> {
        if let Some(op) = self.current_custom10_register {
            return Some(op);
        }
        let patch_addr = self.after_current_custom_10_call;
        if patch_addr == E::VirtualAddress::from_u64(0) {
            return None;
        }
        self.after_current_custom_10_call = E::VirtualAddress::from_u64(0);
        let binary = ctrl.binary();
        let ctx = ctrl.ctx();
        let skip = super::min_instruction_length(binary, patch_addr, 5)?;
        if patch_addr + skip > ctrl.address() {
            return None;
        }
        let extra_reg = (1..2).find(|&i| ctrl.resolve_register(i).if_custom() == Some(0x12))?;
        let code = binary.slice_from_address(patch_addr, skip).ok()?;

        let result = &mut self.dat_ctx.result;
        let code_offset = result.code_bytes.len() as u32;
        // mov extra_reg, rax
        result.code_bytes.extend_from_slice(&[0x48, 0x89, 0xc0 | extra_reg]);
        result.code_bytes.extend_from_slice(code);
        result.patches.push(DatPatch::Hook(patch_addr, code_offset, skip as u8 + 3, skip as u8));
        let reg = ctx.register(extra_reg);
        self.current_custom10_register = Some(reg);
        Some(reg)
    }

    /// Return `base, index` for
    /// `base + index * TEXTURE_SIZE`
    fn texture_index_from_op(
        &self,
        val: Operand<'e>,
        ctrl: &mut Control<'e, '_, '_, Self>,
    ) -> Option<(Operand<'e>, Operand<'e>)> {
        let texture_size = E::struct_layouts().texture_struct_size();
        val.if_arithmetic_add()
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
                                let ctx = ctrl.ctx();
                                ctx.mem_sub_const_op(x, E::VirtualAddress::SIZE as u64)
                            })
                            .filter(|x| {
                                self.grp_operands.get(&x.hash_by_address())
                                    .is_some_and(|&y| y == GrpType::DdsGrp)
                            })
                    })
            })
            .filter(|&(_, x)| x.if_arithmetic_mul_const(texture_size).is_some())
    }

    /// May add the patch for additional ddsgrp deref if needed.
    fn unresolve_base_index(
        &mut self,
        base: Operand<'e>,
        index: Operand<'e>,
        ctrl: &mut Control<'e, '_, '_, Self>,
    ) -> Option<(Operand<'e>, Operand<'e>)> {
        let ctx = ctrl.ctx();
        let base = match unresolve(ctx, ctrl.exec_state(), base)
            .or_else(|| {
                if base.if_custom() == Some(0x10) {
                    self.try_add_patch_for_ddsgrp_set_deref(ctrl)
                } else {
                    None
                }
            })
        {
            Some(s) => s,
            None => {
                dat_warn!(
                    self.dat_ctx, "Can't unresolve ddsgrp texture op {} @ {:?}",
                    base, ctrl.address(),
                );
                return None;
            }
        };
        let index = match unresolve(ctx, ctrl.exec_state(), index) {
            Some(s) => s,
            None => {
                dat_warn!(
                    self.dat_ctx, "Can't unresolve ddsgrp texture op {} @ {:?}",
                    index, ctrl.address(),
                );
                return None;
            }
        };
        Some((base, index))
    }
}
