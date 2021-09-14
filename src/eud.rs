use bumpalo::collections::Vec as BumpVec;

use scarf::{BinaryFile, Operand, OperandCtx, Operation, DestOperand, OperandType, MemAccessSize};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{ArithOpType};

use crate::{AnalysisCtx, EntryOf, bumpvec_with_capacity, FunctionFinder};

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
            Operand::either(a.left, a.right, |x| x.if_constant())
                .map(|(x, y)| (y, x))
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
        result.euds.retain(|x| x.operand.if_constant() != Some(0));
        result.euds.sort_unstable_by_key(|x| x.address);
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
        let mut result = analyze_eud_init_fn::<E>(ctx, binary, entry);
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
        let func = match find_init_eud_table_from_parent::<E>(ctx, binary, &funcs, cref) {
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
        let mut result = analyze_eud_init_fn::<E>(ctx, binary, func);
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
fn find_init_eud_table_from_parent<'e, E: ExecutionState<'e>>(
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    funcs: &[E::VirtualAddress],
    addr: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: EntryOf<E::VirtualAddress>,
    }

    #[derive(Clone)]
    struct State<Va: VirtualAddress> {
        in_wanted_branch: bool,
        wanted_branch_start: Va,
    }
    impl<Va: VirtualAddress> scarf::analysis::AnalysisState for State<Va> {
        fn merge(&mut self, newer: Self) {
            self.in_wanted_branch |= newer.in_wanted_branch;
            if self.wanted_branch_start.as_u64() != 0 {
                self.wanted_branch_start = newer.wanted_branch_start;
            }
        }
    }

    impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, E> {
        type State = State<E::VirtualAddress>;
        type Exec = E;
        fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
            let address = ctrl.address();
            let state = ctrl.user_state();
            if state.wanted_branch_start == address {
                state.in_wanted_branch = true;
            }
        }
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            // True if from jump, false if not jump
            fn branch_from_condition<'e>(cond: Operand<'e>) -> Option<bool> {
                match cond.ty() {
                    OperandType::Arithmetic(arith) if arith.ty == ArithOpType::GreaterThan => {
                        if arith.left.if_constant() == Some(0x7a99) {
                            Some(false)
                        } else {
                            None
                        }
                    }
                    OperandType::Arithmetic(arith) if arith.ty == ArithOpType::Equal => {
                        let const_eq =
                            Operand::either(arith.left, arith.right, |x| x.if_constant());
                        if let Some((c, other)) = const_eq {
                            if c == 0 {
                                return branch_from_condition(other).map(|x| !x);
                            }
                        }
                        None
                    }
                    _ => None,
                }
            }
            match *op {
                Operation::Jump { condition, to } => {
                    let condition = ctrl.resolve(condition);
                    if let Some(jump) = branch_from_condition(condition) {
                        let branch = match jump {
                            true => VirtualAddress::from_u64(
                                ctrl.resolve(to).if_constant().unwrap_or(0)
                            ),
                            false => ctrl.current_instruction_end(),
                        };
                        ctrl.user_state().wanted_branch_start = branch;
                    }
                }
                Operation::Call(to) => {
                    if ctrl.user_state().in_wanted_branch {
                        if let Some(to) = ctrl.resolve(to).if_constant() {
                            self.result = EntryOf::Ok(VirtualAddress::from_u64(to));
                            ctrl.end_analysis();
                        }
                    }
                }
                _ => (),
            };
        }
    }

    crate::entry_of_until(binary, funcs, addr, |entry| {
        let mut analyzer = Analyzer {
            result: EntryOf::Retry,
        };
        let exec_state = E::initial_state(ctx, binary);
        let state = State {
            in_wanted_branch: false,
            wanted_branch_start: E::VirtualAddress::from_u64(0),
        };
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
    ctx: OperandCtx<'e>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    addr: E::VirtualAddress,
) -> EudTable<'e> {
    struct Analyzer<'e, E: ExecutionState<'e>> {
        result: EudTable<'e>,
        phantom: std::marker::PhantomData<(*const E, &'e ())>,
    }
    impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for Analyzer<'e, E> {
        type State = analysis::DefaultState;
        type Exec = E;
        fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
            match op {
                Operation::Call(..) => {
                    let ctx = ctrl.ctx();
                    let esp = ctx.register(4);
                    // A1 has to be a1 to this fn ([esp + 4]),
                    // a2 ptr,
                    // a3 length
                    let a1 = ctrl.resolve(ctx.mem32(esp, 0));
                    // Not resolving a2, it'll be resolved later on -- double resolving
                    // ends up being wrong
                    let a2 = ctx.mem32(esp, 4);
                    let a3 = ctrl.resolve(ctx.mem32(esp, 8));
                    let is_a1 = a1.if_mem32_offset(4)
                        .filter(|&x| x == ctx.register(4))
                        .is_some();
                    if is_a1 {
                        if let Some(len) = a3.if_constant() {
                            if len % 0x10 == 0 {
                                let result = (0..(len / 0x10)).map(|i| {
                                    let address = ctrl.resolve(ctx.mem32(a2, i * 0x10));
                                    let size = ctrl.resolve(ctx.mem32(a2, i * 0x10 + 4));
                                    let operand = ctrl.resolve(ctx.mem32(a2, i * 0x10 + 0x8));
                                    let flags = ctrl.resolve(ctx.mem32(a1, i * 0x10 + 0xc));
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
                        self.check_eud_vec_push(ctrl);
                    }
                }
                _ => (),
            }
        }
    }
    impl<'e, E: ExecutionState<'e>> Analyzer<'e, E> {
        fn check_eud_vec_push(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
            // Check for eud_vec_push(&vec, &eud)
            // Eud is 0x10 bytes
            let ctx = ctrl.ctx();
            let arg1 = ctrl.resolve(ctx.mem32(ctx.register(4), 0));
            let mut arg1_mem = [ctx.const_0(); 4];
            for i in 0..4 {
                let field = ctrl.read_memory(
                    &ctx.mem_access(arg1, (i * 4) as u64, MemAccessSize::Mem32)
                );
                arg1_mem[i] = field;
            }
            // Sanity check address/size/flags
            if arg1_mem[0].if_constant().filter(|&x| x >= 0x40_0000).is_none() {
                return;
            }
            if arg1_mem[1].if_constant().filter(|&x| x < 0x1000_0000).is_none() {
                return;
            }
            if arg1_mem[3].if_constant().is_none() {
                return;
            }

            let vec = ctrl.resolve(ctx.register(1));
            let vec_buffer_addr = ctx.mem_access(vec, 0, E::WORD_SIZE);
            let vec_buffer = ctrl.read_memory(&vec_buffer_addr);
            let vec_len_addr = ctx.mem_access(vec, E::VirtualAddress::SIZE.into(), E::WORD_SIZE);
            // vec.buffer[vec.len] = eud;
            // vec.len += 1;
            if let Some(len) = ctrl.read_memory(&vec_len_addr).if_constant() {
                let exec_state = ctrl.exec_state();
                for i in 0..4 {
                    let offset = len.wrapping_mul(0x10).wrapping_add(i as u64 * 4);
                    exec_state.move_resolved(
                        &DestOperand::Memory(
                            ctx.mem_access(vec_buffer, offset, MemAccessSize::Mem32)
                        ),
                        arg1_mem[i],
                    );
                }
                exec_state.move_resolved(
                    &DestOperand::Memory(vec_len_addr),
                    ctx.constant(len.wrapping_add(1)),
                );
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        result: EudTable {
            euds: Vec::new(),
        },
        phantom: Default::default(),
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
    funcs: &[E::VirtualAddress],
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
            let stop = match op {
                Operation::Move(ref to, from, _) => {
                    if let Some(mem) = from.if_memory() {
                        // Don't stop on fs:[0] read
                        mem.if_constant_address() != Some(0)
                    } else {
                        if let DestOperand::Memory(mem) = to {
                            let mem = ctrl.resolve_mem(mem);
                            // Offset if this is moving to [esp + offset]
                            let (base, offset) = mem.address();
                            // Accept stores up to [orig_esp - 0x10000] as part
                            // of stack setup
                            let is_stack_store = 0u64.wrapping_sub(offset) <= 0x1000 &&
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
                    let eax = ctrl.resolve(ctx.register(0));
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
                let esp = ctrl.resolve(ctx.register(4));
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

    crate::entry_of_until(binary, funcs, addr, |entry| {
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
    use memmem::{TwoWaySearcher, Searcher};

    let code_section = binary.code_section();
    let mut haystack = &code_section.data[..];
    let mut pos = 0;
    let needle = value.to_le_bytes();
    let searcher = TwoWaySearcher::new(&needle[..]);
    while let Some(index) = searcher.search_in(haystack) {
        pos += index as u32;
        out.push(code_section.virtual_address + pos);
        haystack = &haystack[index + 4..];
    }
}
