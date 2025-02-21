use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;

use scarf::{BinaryFile, Operand, OperandCtx, Operation, DestOperand, OperandType, MemAccessSize};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{ArithOpType};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{EntryOf, FunctionFinder, FunctionList, entry_of_until};
use crate::analysis_state::{AnalysisState, StateEnum, EudState};
use crate::util::{ControlExt, bumpvec_with_capacity};

pub struct Eud<'e> {
    pub address: u32,
    pub size: u32,
    pub operand: Operand<'e>,
    pub flags: u32,
}

pub struct EudTable<'e> {
    /// Sorted by address
    pub euds: Vec<Eud<'e>>,
}

static EUD_ADDRS: &[u32] = &[
    0x0068C14C, 0x006C9E20, 0x00655B3C, 0x00665880, 0x0051642C, 0x00656888, 0x00516630,
    0x00517448,
];

fn if_arithmetic_add_or_sub_const<'e>(val: Operand<'e>) -> Option<(Operand<'e>, u64)> {
    match val.ty() {
        OperandType::Arithmetic(a) if a.ty == ArithOpType::Add => {
            if let Some(c) = a.right.if_constant() {
                Some((a.left, c))
            } else {
                None
            }
        }
        OperandType::Arithmetic(a) if a.ty == ArithOpType::Sub => {
            if let Some(c) = a.right.if_constant() {
                Some((a.left, 0u64.wrapping_sub(c)))
            } else {
                None
            }
        }
        _ => None,
    }
}

pub(crate) fn eud_table<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> EudTable<'e> {
    fn finish_euds(result: &mut EudTable) {
        // Note: Euds can have duplicate start adderesses sometimes, for
        // consistent results also sort by size.
        // At least some button sets have copies with different size/flags
        result.euds.sort_unstable_by_key(|x| (x.address, x.size));
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let mut const_refs = bumpvec_with_capacity(EUD_ADDRS.len() * 2, bump);
    for &addr in EUD_ADDRS {
        find_const_refs_in_code(binary, addr, &mut const_refs);
    }
    const_refs.sort_unstable();
    let funcs = functions.functions();
    for &cref in &const_refs {
        let entry = match find_stack_reserve_entry::<E>(ctx, binary, &funcs, cref) {
            Some((e, stack_size)) => {
                if stack_size < 0x1000 {
                    continue;
                } else {
                    e
                }
            }
            None => continue,
        };
        let mut result = analyze_eud_init_fn::<E>(analysis, entry);
        if result.euds.len() > 0x100 {
            finish_euds(&mut result);
            return result;
        }
    }
    // Try an alternate way by looking for parent function which has
    //   cmp reg, 7a99
    //   jb away
    //   call init_eud_table

    find_const_refs_in_code(binary, 0x7a99, &mut const_refs);
    for &cref in &const_refs {
        let func = match find_init_eud_table_from_parent::<E>(ctx, bump, binary, &funcs, cref) {
            Some(s) => s,
            None => continue,
        };
        let func = match find_stack_reserve_entry::<E>(ctx, binary, &funcs, func) {
            Some((e, stack_size)) => {
                if stack_size < 0x1000 {
                    continue;
                } else {
                    e
                }
            }
            None => continue,
        };
        let mut result = analyze_eud_init_fn::<E>(analysis, func);
        if result.euds.len() > 0x100 {
            finish_euds(&mut result);
            return result;
        }
    }

    EudTable {
        euds: Vec::new(),
    }
}

// See comment at call site
fn find_init_eud_table_from_parent<'acx, 'e, E: ExecutionState<'e>>(
    ctx: OperandCtx<'e>,
    bump: &'acx Bump,
    binary: &'e BinaryFile<E::VirtualAddress>,
    funcs: &FunctionList<'_, E::VirtualAddress>,
    addr: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    struct Analyzer<'acx, 'e, E: ExecutionState<'e>> {
        result: EntryOf<E::VirtualAddress>,
        phantom: std::marker::PhantomData<&'acx ()>,
    }

    impl<'acx, 'e: 'acx, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'acx, 'e, E> {
        type State = AnalysisState<'acx, 'e>;
        type Exec = E;
        fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
            let address = ctrl.address();
            let state = ctrl.user_state().get::<EudState>();
            if state.wanted_branch_start == address.as_u64() as u32 {
                state.in_wanted_branch = true;
            }
        }

        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            // True if from jump, false if not jump
            fn branch_from_condition<'e>(
                ctx: OperandCtx<'e>,
                cond: Operand<'e>,
            ) -> Option<bool> {
                match cond.ty() {
                    OperandType::Arithmetic(arith) if arith.ty == ArithOpType::GreaterThan => {
                        if arith.left.if_constant() == Some(0x7a99) {
                            Some(false)
                        } else {
                            None
                        }
                    }
                    OperandType::Arithmetic(arith) if arith.ty == ArithOpType::Equal => {
                        if arith.right == ctx.const_0() {
                            branch_from_condition(ctx, arith.left).map(|x| !x)
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
            match *op {
                Operation::Jump { condition, to } => {
                    let condition = ctrl.resolve(condition);
                    let ctx = ctrl.ctx();
                    if let Some(jump) = branch_from_condition(ctx, condition) {
                        let branch = match jump {
                            true => VirtualAddress::from_u64(
                                ctrl.resolve(to).if_constant().unwrap_or(0)
                            ),
                            false => ctrl.current_instruction_end(),
                        };
                        ctrl.user_state().get::<EudState>().wanted_branch_start =
                            branch.as_u64() as u32;
                    }
                }
                Operation::Call(to) => {
                    if ctrl.user_state().get::<EudState>().in_wanted_branch {
                        if let Some(to) = ctrl.resolve_va(to) {
                            self.result = EntryOf::Ok(to);
                            ctrl.end_analysis();
                        }
                    }
                }
                _ => (),
            };
        }
    }

    entry_of_until(binary, &funcs, addr, |entry| {
        let mut analyzer = Analyzer {
            result: EntryOf::Retry,
            phantom: Default::default(),
        };
        let exec_state = E::initial_state(ctx, binary);
        let state = EudState {
            in_wanted_branch: false,
            wanted_branch_start: 0,
        };
        let state = AnalysisState::new(bump, StateEnum::Eud(state));
        let mut analysis = FuncAnalysis::custom_state(
            binary,
            ctx,
            entry,
            exec_state,
            state,
        );
        analysis.analyze(&mut analyzer);
        analyzer.result
    }).into_option()
}

fn analyze_eud_init_fn<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    addr: E::VirtualAddress,
) -> EudTable<'e> {
    struct Analyzer<'a, 'e, E: ExecutionState<'e>> {
        result: EudTable<'e>,
        arg_cache: &'a ArgCache<'e, E>,
        first_call: bool,
        inlining: bool,
    }
    impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'a, 'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            if self.inlining {
                match op {
                    Operation::Call(..) | Operation::Jump { .. } => {
                        ctrl.end_analysis();
                        self.inlining = false;
                    }
                    _ => (),
                }
                return;
            }
            match *op {
                Operation::Call(dest) => {
                    let ctx = ctrl.ctx();
                    if self.first_call {
                        // The large_stack_alloc call on 64bit (Or maybe recent versions?)
                        // is just a probe with stack sub being done later after the call,
                        // for at least some 32bit versions it does actually move esp.
                        // Don't clobber eax (stack alloc size) on 64bit
                        self.first_call = false;
                        if E::VirtualAddress::SIZE == 8 {
                            if let Some(eax) = ctrl.resolve_register(0).if_constant() {
                                if eax > 0x1000 {
                                    ctrl.skip_operation();
                                    return;
                                }
                            }
                        }
                    }
                    // A1 has to be a1 to this fn
                    // a2 ptr,
                    // a3 length
                    let a1 = ctrl.resolve_arg(0);
                    let a2 = ctrl.resolve_arg(1);
                    let a3 = ctrl.resolve_arg(2);
                    let eud_size = if E::VirtualAddress::SIZE == 4 { 0x10 } else { 0x18 };
                    if a1 == self.arg_cache.on_entry(0) {
                        if let Some(len) = a3.if_constant().and_then(|x| u32::try_from(x).ok()) {
                            if len % eud_size == 0 {
                                let result = (0..(len / eud_size)).map(|i| {
                                    let mem = ctx.mem_access(
                                        a2,
                                        u64::from(i * eud_size),
                                        MemAccessSize::Mem32,
                                    );
                                    let address = ctrl.read_memory(&mem);
                                    let mem = mem.with_offset_size(4, MemAccessSize::Mem32);
                                    let size = ctrl.read_memory(&mem);
                                    let mem = mem.with_offset_size(4, E::WORD_SIZE);
                                    let operand = ctrl.read_memory(&mem);
                                    let mem = mem.with_offset_size(
                                        E::VirtualAddress::SIZE.into(),
                                        MemAccessSize::Mem32,
                                    );
                                    let flags = ctrl.read_memory(&mem);
                                    if let Some(address) = address.if_constant() {
                                        if let Some(size) = size.if_constant() {
                                            if let Some(flags) = flags.if_constant() {
                                                return Ok(Eud {
                                                    address: address as u32,
                                                    size: size as u32,
                                                    operand,
                                                    flags: flags as u32,
                                                });
                                            }
                                        }
                                    }
                                    Err(())
                                }).collect::<Result<Vec<Eud>, ()>>();
                                if let Ok(euds) = result {
                                    self.result.euds = euds;
                                    ctrl.end_analysis();
                                }
                            }
                        }
                    } else {
                        let was_push = self.check_eud_vec_push(ctrl);
                        if !was_push {
                            // Check vec.len_bytes() call that wasn't inlined;
                            // [ecx + 4] should be constant greater than 0x200
                            let this_vec_len_place = ctx.mem_any(
                                E::WORD_SIZE,
                                ctx.register(1),
                                E::VirtualAddress::SIZE.into(),
                            );
                            if let Some(c) = ctrl.resolve(this_vec_len_place).if_constant() {
                                if c > 0x200 {
                                    if let Some(dest) = ctrl.resolve_va(dest) {
                                        self.inlining = true;
                                        ctrl.inline(self, dest);
                                        if self.inlining {
                                            ctrl.skip_operation();
                                            self.inlining = false;
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
    impl<'a, 'e, E: ExecutionState<'e>> Analyzer<'a, 'e, E> {
        fn check_eud_vec_push(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) -> bool {
            // Check for eud_vec_push(&vec, &eud)
            // Eud is 0x10 / 0x18 bytes
            let ctx = ctrl.ctx();
            let arg1 = ctrl.resolve_arg_thiscall(0);
            let eud_size = if E::VirtualAddress::SIZE == 4 { 0x10 } else { 0x18 };
            let offsets_sizes = if E::VirtualAddress::SIZE == 4 {
                &[
                    (0u8, MemAccessSize::Mem32),
                    (0x4, MemAccessSize::Mem32),
                    (0x8, MemAccessSize::Mem32),
                    (0xc, MemAccessSize::Mem32),
                ]
            } else {
                &[
                    (0u8, MemAccessSize::Mem32),
                    (0x4, MemAccessSize::Mem32),
                    (0x8, MemAccessSize::Mem64),
                    (0x10, MemAccessSize::Mem32),
                ]
            };
            let mut arg1_mem = [ctx.const_0(); 4];
            for i in 0..4 {
                let (offset, size) = offsets_sizes[i];
                let field = ctrl.read_memory(&ctx.mem_access(arg1, offset as u64, size));
                arg1_mem[i] = field;
            }
            // Sanity check address/size/flags
            if arg1_mem[0].if_constant().filter(|&x| x >= 0x40_0000).is_none() {
                return false;
            }
            if arg1_mem[1].if_constant().filter(|&x| x < 0x1000_0000).is_none() {
                return false;
            }
            if arg1_mem[3].if_constant().is_none() {
                return false;
            }

            let vec = ctrl.resolve_register(1);
            let vec_buffer_addr = ctx.mem_access(vec, 0, E::WORD_SIZE);
            let vec_buffer = ctrl.read_memory(&vec_buffer_addr);
            let vec_len_addr = ctx.mem_access(vec, E::VirtualAddress::SIZE.into(), E::WORD_SIZE);
            // vec.buffer[vec.len] = eud;
            // vec.len += 1;
            if let Some(len) = ctrl.read_memory(&vec_len_addr).if_constant() {
                let exec_state = ctrl.exec_state();
                for i in 0..4 {
                    let (offset, size) = offsets_sizes[i];
                    let offset = len.wrapping_mul(eud_size).wrapping_add(offset as u64);
                    exec_state.write_memory(
                        &ctx.mem_access(vec_buffer, offset, size),
                        arg1_mem[i],
                    );
                }
                exec_state.write_memory(&vec_len_addr, ctx.constant(len.wrapping_add(1)));
                true
            } else {
                false
            }
        }
    }

    let ctx = actx.ctx;
    let binary = actx.binary;
    let arg_cache = &actx.arg_cache;
    let mut analyzer = Analyzer::<E> {
        result: EudTable {
            euds: Vec::new(),
        },
        arg_cache,
        first_call: true,
        inlining: false,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, addr);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

/// Finds entry of the function containing address `addr`, assuming
/// the entry either does an esp subtraction or a call with eax being an constant
/// (large stack reserve) before anything that doesn't seem to be just pushs/etc
///
/// On success returns (entry, stack_reserve). stack_reserve may not be 100% correct if there
/// are pushes later on in the function, so it should not be relied too much on.
fn find_stack_reserve_entry<'e, E: ExecutionState<'e>>(
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    funcs: &FunctionList<'_, E::VirtualAddress>,
    addr: E::VirtualAddress,
) -> Option<(E::VirtualAddress, u32)> {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: EntryOf<u32>,
        phantom: std::marker::PhantomData<(*const E, &'e ())>,
    }
    impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            let mut call_reserve = 0;
            let ctx = ctrl.ctx();
            let stop = match *op {
                Operation::Move(ref to, from) => {
                    if let Some(mem) = from.if_memory() {
                        // Don't stop on fs:[0] read
                        mem.if_constant_address() != Some(0)
                    } else {
                        if let DestOperand::Memory(mem) = to {
                            let mem = ctrl.resolve_mem(mem);
                            // Offset if this is moving to [esp + offset]
                            let (base, offset) = mem.address();
                            // Accept stores up to [orig_esp - 0x1000] as part
                            // of stack setup
                            let is_stack_store = (-0x1000..0x40).contains(&(offset as i64)) &&
                                base == ctx.register(4);
                            !is_stack_store
                        } else {
                            false
                        }
                    }
                }
                Operation::Return(..) => true,
                Operation::Jump { .. } => true,
                Operation::Call(..) => {
                    let eax = ctrl.resolve_register(0);
                    if let Some(c) = eax.if_constant() {
                        if c & 3 == 0 && c > 0x400 {
                            call_reserve = c;
                        }
                    }
                    true
                }
                _ => true,
            };
            if stop {
                let esp = ctrl.resolve_register(4);
                let off = if_arithmetic_add_or_sub_const(esp)
                    .filter(|(r, _)| r.if_register() == Some(4));
                if let Some((_, off)) = off {
                    let neg_offset = 0u64.wrapping_sub(off);
                    if neg_offset < 0x80000 {
                        if let Some(val) = neg_offset.checked_add(call_reserve) {
                            self.result = EntryOf::Ok(val as u32);
                        }
                    }
                }
                ctrl.end_analysis();
            }
        }
    }

    entry_of_until(binary, funcs, addr, |entry| {
        let mut analyzer = Analyzer::<E> {
            result: EntryOf::Retry,
            phantom: Default::default(),
        };
        let mut analysis = FuncAnalysis::new(binary, ctx, entry);
        analysis.analyze(&mut analyzer);
        analyzer.result
    }).into_option_with_entry()
}

fn find_const_refs_in_code<Va: VirtualAddress>(
    binary: &BinaryFile<Va>,
    value: u32,
    out: &mut BumpVec<'_, Va>,
) {
    use memchr::memmem::{Finder};

    let code_section = binary.code_section();
    let haystack = &code_section.data[..];
    let needle = value.to_le_bytes();
    let finder = Finder::new(&needle[..]);
    for index in finder.find_iter(haystack) {
        out.push(code_section.virtual_address + index as u32);
    }
}
