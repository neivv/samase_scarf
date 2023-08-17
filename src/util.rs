//! Miscellaneous helper functions and extension traits.
//!
//! Almost everything is reimported at crate root for backwards compat, though probably
//! should now prefer importing directly from this module.

use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;
use byteorder::{ByteOrder, LittleEndian};

use scarf::analysis::{self, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{
    ArithOpType, BinaryFile, BinarySection, MemAccessSize, Operand, OperandCtx, OperandType, Rva
};

use crate::analysis::ArgCache;

// When not testing, immediatly end once a value is found, for tests require all values
// to be same.
#[cfg(not(feature = "test_assertions"))]
pub fn single_result_assign<T: Eq>(new: Option<T>, old: &mut Option<T>) -> bool
where T: std::fmt::Debug + PartialEq,
{
    if new.is_some() {
        *old = new;
        true
    } else {
        false
    }
}

#[cfg(feature = "test_assertions")]
pub fn single_result_assign<T>(new: Option<T>, old: &mut Option<T>) -> bool
where T: std::fmt::Debug + PartialEq,
{
    if let Some(new) = new {
        if let Some(ref old) = *old {
            assert_eq!(*old, new, "Received different results:\nOLD: {:#?}\nNEW: {:#?}", old, new);
        }
        *old = Some(new);
    }
    false
}

pub fn if_callable_const<'e, A: analysis::Analyzer<'e>>(
    binary: &BinaryFile<<A::Exec as ExecutionState<'e>>::VirtualAddress>,
    dest: Operand<'e>,
    ctrl: &mut Control<'e, '_, '_, A>
) -> Option<<A::Exec as ExecutionState<'e>>::VirtualAddress> {
    ctrl.resolve(dest).if_constant()
        .and_then(|dest| {
            let dest = <A::Exec as ExecutionState<'_>>::VirtualAddress::from_u64(dest);
            let code_section = binary.code_section();
            let code_section_end = code_section.virtual_address + code_section.virtual_size;
            if dest > code_section.virtual_address && dest < code_section_end {
                Some(dest)
            } else {
                None
            }
        })
}

/// Helper extension functions for Option<(Operand<'e>, Operand<'e>)>.
pub trait OptionExt<'e> {
    /// `opt.and_either(x)` is equivalent to
    /// ```
    ///     # use scarf::Operand;
    ///     # let opt = None;
    ///     # fn x(op: Operand<'_>) -> Option<u64> { op.if_constant() }
    ///     let either_opt = opt.and_then(|(l, r)| Operand::either(l, r, x));
    /// ```
    fn and_either<F, T>(self, cb: F) -> Option<(T, Operand<'e>)>
    where F: FnMut(Operand<'e>) -> Option<T>;
    /// `opt.and_either_other(x)` is equivalent to
    /// ```
    ///     # use scarf::Operand;
    ///     # let opt = None;
    ///     # fn x(op: Operand<'_>) -> Option<u64> { op.if_constant() }
    ///     let other_opt = opt.and_then(|(l, r)| Operand::either(l, r, x))
    ///         .map(|(_, other)| other);
    /// ```
    fn and_either_other<F, T>(self, cb: F) -> Option<Operand<'e>>
    where F: FnMut(Operand<'e>) -> Option<T>;
    /// `opt.and_if_either_other(x)` is equivalent to
    /// ```
    ///     # use scarf::Operand;
    ///     # let opt = None;
    ///     # fn x(op: Operand<'_>) -> bool { op.if_constant() == Some(4) }
    ///     let other_opt = opt.and_then(|(l, r)| Operand::either(l, r, |op| x(op).then(|| ())))
    ///         .map(|(_, other)| other);
    /// ```
    fn and_if_either_other<F>(self, cb: F) -> Option<Operand<'e>>
    where F: FnMut(Operand<'e>) -> bool;
}

impl<'e> OptionExt<'e> for Option<(Operand<'e>, Operand<'e>)> {
    fn and_either<F, T>(self, cb: F) -> Option<(T, Operand<'e>)>
    where F: FnMut(Operand<'e>) -> Option<T>
    {
        self.and_then(|(l, r)| Operand::either(l, r, cb))
    }

    fn and_either_other<F, T>(self, cb: F) -> Option<Operand<'e>>
    where F: FnMut(Operand<'e>) -> Option<T>
    {
        self.and_either(cb).map(|(_, other)| other)
    }

    fn and_if_either_other<F>(self, mut cb: F) -> Option<Operand<'e>>
    where F: FnMut(Operand<'e>) -> bool
    {
        self.and_either(|x| cb(x).then(|| ())).map(|((), other)| other)
    }
}

/// Returns true if the stack is setup for a call that seems to be reporting an assertion
/// error
pub fn seems_assertion_call<'exec, A: analysis::Analyzer<'exec>>(
    ctrl: &mut Control<'exec, '_, '_, A>,
    arg_cache: &ArgCache<'exec, A::Exec>,
) -> bool {
    let arg1 = match ctrl.resolve(arg_cache.on_call(0)).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg2 = match ctrl.resolve(arg_cache.on_call(1)).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg3 = match ctrl.resolve(arg_cache.on_call(2)).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg4 = match ctrl.resolve(arg_cache.on_call(3)).if_constant() {
        Some(s) => s,
        None => return false,
    };
    if arg4 == 0 || arg4 > 12000 {
        return false;
    }
    // Could check that these are strings
    let binary = ctrl.binary();
    for arg in [arg1, arg2, arg3] {
        let addr = <A::Exec as ExecutionState<'_>>::VirtualAddress::from_u64(arg);
        if binary.section_by_addr(addr).is_none() {
            return false;
        }
    }
    true
}

// bool true => eq, bool false => not eq
pub fn if_arithmetic_eq_neq<'e>(op: Operand<'e>) -> Option<(Operand<'e>, Operand<'e>, bool)> {
    op.if_arithmetic_eq_neq()
}

pub trait OperandExt<'e> {
    fn if_arithmetic_add_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_sub_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_mul_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_and_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_lsh_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_rsh_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_eq_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_gt_const(self, offset: u64) -> Option<Operand<'e>>;
    fn if_arithmetic_float(self, ty: ArithOpType) -> Option<(Operand<'e>, Operand<'e>)>;
    /// Returns `(x, const_off)` if `self` is `x + const_off`, else returns `(self, 0)`
    /// Meant for going from struct offset to struct base, when the offset is unknown
    /// and may be 0.
    /// If the offset is known `op.if_arithmetic_add_const(offset)` is better.
    fn struct_offset(self) -> (Operand<'e>, u32);
    /// Returns `(x, const_off)` if `self` is `x +/- const_off`, else returns `(self, 0)`
    fn add_sub_offset(self) -> (Operand<'e>, u64);
    /// If `self` is SignExtend(x), returns `x`. Otherwise resturns `self`
    fn unwrap_sext(self) -> Operand<'e>;
    fn if_constant_or_read_binary<Va: VirtualAddress>(
        self,
        binary: &BinaryFile<Va>,
    ) -> Option<u64>;
    /// bool true => eq, bool false => not eq
    fn if_arithmetic_eq_neq(self) -> Option<(Operand<'e>, Operand<'e>, bool)>;
    /// bool true => eq, bool false => not eq
    fn if_arithmetic_eq_neq_zero(self, ctx: OperandCtx<'e>) -> Option<(Operand<'e>, bool)>;
}

impl<'e> OperandExt<'e> for Operand<'e> {
    fn if_arithmetic_add_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic_add()?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_sub_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic_sub()?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_mul_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic_mul()?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_and_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic_and()?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_lsh_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic(ArithOpType::Lsh)?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_rsh_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic(ArithOpType::Rsh)?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_eq_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic(ArithOpType::Equal)?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_gt_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_arithmetic(ArithOpType::GreaterThan)?;
        let r = r.if_constant()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_float(self, ty: ArithOpType) -> Option<(Operand<'e>, Operand<'e>)> {
        match self.ty() {
            OperandType::ArithmeticFloat(arith, _size)
                if arith.ty == ty => Some((arith.left, arith.right)),
            _ => None,
        }
    }

    fn struct_offset(self) -> (Operand<'e>, u32) {
        self.if_arithmetic_add()
            .and_then(|x| {
                let off = u32::try_from(x.1.if_constant()?).ok()?;
                Some((x.0, off))
            })
            .unwrap_or((self, 0))
    }

    fn add_sub_offset(self) -> (Operand<'e>, u64) {
        match self.if_arithmetic_any() {
            Some(x) if matches!(x.ty, ArithOpType::Add | ArithOpType::Sub) => {
                if let Some(c) = x.right.if_constant() {
                    let c = if x.ty == ArithOpType::Add {
                        c
                    } else {
                        0u64.wrapping_sub(c)
                    };
                    (x.left, c)
                } else {
                    (self, 0)
                }
            }
            _ => (self, 0),
        }
    }

    fn unwrap_sext(self) -> Operand<'e> {
        match *self.ty() {
            OperandType::SignExtend(val, ..) => val,
            _ => self,
        }
    }

    fn if_constant_or_read_binary<Va: VirtualAddress>(
        self,
        binary: &BinaryFile<Va>,
    ) -> Option<u64> {
        self.if_constant()
            .or_else(|| {
                let mem = self.if_memory()?;
                let addr = Va::from_u64(mem.if_constant_address()?);
                Some(binary.read_u64(addr).ok()? & mem.size.mask())
            })
    }

    fn if_arithmetic_eq_neq(self) -> Option<(Operand<'e>, Operand<'e>, bool)> {
        let arith = self.if_arithmetic_any()?;
        if arith.ty == ArithOpType::Equal {
            Some(
                Operand::either(arith.left, arith.right, |x| x.if_constant().filter(|&c| c == 0))
                    .and_then(|(_, other)| other.if_arithmetic_eq())
                    .map(|(l, r)| (l, r, false))
                    .unwrap_or_else(|| (arith.left, arith.right, true))
            )
        } else if arith.ty == ArithOpType::Xor && self.relevant_bits().end == 1 {
            // 1bit x ^ y is x != y
            Some((arith.left, arith.right, false))
        } else {
            None
        }
    }

    fn if_arithmetic_eq_neq_zero(self, ctx: OperandCtx<'e>) -> Option<(Operand<'e>, bool)> {
        let (l, r) = self.if_arithmetic_eq()?;
        let zero = ctx.const_0();
        if r != zero {
            return None;
        }
        if let Some((l, r)) = l.if_arithmetic_eq() {
            if r == zero {
                return Some((l, false));
            }
        }
        Some((l, true))
    }
}

pub trait MemAccessExt {
    fn is_global(&self) -> bool;
}

impl<'e> MemAccessExt for scarf::MemAccess<'e> {
    fn is_global(&self) -> bool {
        if let Some(c) = self.if_constant_address() {
            c > 0x1000
        } else {
            is_global_rec(self.address().0)
        }
    }
}

// This is slightly better for binary size than BumpVec::with_capcity_in,
// as bumpalo is otherwise pretty bad with monomorphizing
pub fn bumpvec_with_capacity<T>(cap: usize, bump: &Bump) -> BumpVec<'_, T> {
    let mut vec = BumpVec::new_in(bump);
    vec.reserve(cap);
    vec
}

/// Return true if all parts of operand are constants/arith
/// And op is not a single small constant
pub fn is_global(op: Operand<'_>) -> bool {
    if let Some(c) = op.if_constant() {
        c > 0x1000
    } else {
        is_global_rec(op)
    }
}

/// Like is_global, but also filters out smaller-than-word Memory operands.
pub fn is_global_struct<'e, E: ExecutionState<'e>>(op: Operand<'_>) -> bool {
    if let Some(mem) = op.if_memory() {
        if mem.size.bytes() < E::WORD_SIZE.bytes() {
            false
        } else {
            is_global_rec(mem.address().0)
        }
    } else {
        is_global(op)
    }
}

fn is_global_rec(op: Operand<'_>) -> bool {
    let mut op = op;
    loop {
        if let OperandType::Arithmetic(arith) = op.ty() {
            // Nicer for tail calls to check right first as it doesn't recurse in operand chains
            if !is_global_rec(arith.right) {
                return false;
            }
            op = arith.left;
            continue;
        } else if let OperandType::Memory(ref mem) = op.ty() {
            op = mem.address().0;
            continue;
        } else if op.if_constant().is_some() {
            return true;
        } else {
            return false;
        }
    }
}

pub fn is_stack_address(addr: Operand<'_>) -> bool {
    if let Some((l, r)) = addr.if_arithmetic_sub() {
        r.if_constant().is_some() && l.if_register() == Some(4)
    } else {
        addr.if_register() == Some(4)
    }
}

pub trait ControlExt<'e, E: ExecutionState<'e>> {
    fn resolve_va(&mut self, operand: Operand<'e>) -> Option<E::VirtualAddress>;
    /// Skips current operation, assigns undef to other volatile registers except esp.
    fn skip_call_preserve_esp(&mut self);
    /// Skips current operation, assigns undef to other volatile registers except esp,
    /// and assigns `result` to eax. `result` has to be resolved.
    fn do_call_with_result(&mut self, result: Operand<'e>);
    /// Workaround for sometimes occuring memory reads which scarf isn't
    /// able to detect as aliasing another memory location.
    fn aliasing_memory_fix(&mut self, operation: &scarf::Operation<'e>);
    /// Returns esp - E::VirtualAddress::SIZE.
    /// That is, value of call entry stack pointer supposing we're right
    /// before ctrl.inline() and want the child function to know what the stack
    /// pointer was on entry.
    fn get_new_esp_for_call(&mut self) -> Operand<'e>;
    /// Adds word size to esp (Does not actually return the operand at [esp])
    fn pop_stack(&mut self);
    /// If this looks like a stack probe call (may be first call in 64bit), skip clobbering
    /// rax which will keep it's value of stack alloc size after call.
    /// Return true if the operation was skipped.
    fn check_stack_probe(&mut self) -> bool;
    /// If condition is `register == constant`, assign constant to register
    /// on the branch that the condition is true on.
    ///
    /// (Assumed to be called on Operation::Jump; args must be resolved)
    ///
    /// Useful for cases where codegen follows `reg == 0` jump by using `reg` as zero value
    /// afterwards.
    fn assign_to_unresolved_on_eq_branch(
        &mut self,
        condition: Operand<'e>,
        to: E::VirtualAddress,
    );
    /// Version of above which resolves the args
    fn update_jump_register_to_const(
        &mut self,
        condition: Operand<'e>,
        to: Operand<'e>,
    );
    fn instruction_contains_address(&mut self, address: E::VirtualAddress) -> bool;
    /// Calls self.continue_at_address()
    /// for either jump_dest if eq_zero is false
    /// or self.current_instruction_end() if eq_zero is true.
    ///
    /// eq_zero is same bool as returned from if_arithmetic_eq_neq_zero.
    fn continue_at_neq_address(&mut self, eq_zero: bool, jump_dest: Operand<'e>);
    fn continue_at_eq_address(&mut self, eq_zero: bool, jump_dest: Operand<'e>) {
        self.continue_at_neq_address(!eq_zero, jump_dest);
    }
}

impl<'a, 'b, 'e, A: scarf::analysis::Analyzer<'e>> ControlExt<'e, A::Exec> for
    scarf::analysis::Control<'e, 'a, 'b, A>
{
    fn resolve_va(&mut self, operand: Operand<'e>) ->
        Option<<A::Exec as ExecutionState<'e>>::VirtualAddress>
    {
        self.resolve(operand).if_constant()
            .filter(|&va| va >= self.binary().base().as_u64())
            .map(|x| <A::Exec as ExecutionState<'e>>::VirtualAddress::from_u64(x))
    }

    fn skip_call_preserve_esp(&mut self) {
        self.skip_operation();
        let ctx = self.ctx();
        let state = self.exec_state();
        for i in 0..3 {
            state.set_register(i, ctx.new_undef());
        }
        if A::Exec::WORD_SIZE == MemAccessSize::Mem64 {
            for i in 8..10 {
                state.set_register(i, ctx.new_undef());
            }
        }
    }

    fn do_call_with_result(&mut self, result: Operand<'e>) {
        self.skip_operation();
        let ctx = self.ctx();
        let state = self.exec_state();
        state.set_register(0, result);
        for i in 1..3 {
            state.set_register(i, ctx.new_undef());
        }
        if A::Exec::WORD_SIZE == MemAccessSize::Mem32 {
            state.set_register(4, ctx.new_undef());
        } else {
            for i in 8..10 {
                state.set_register(i, ctx.new_undef());
            }
        }
    }

    fn aliasing_memory_fix(&mut self, op: &scarf::Operation<'e>) {
        if let scarf::Operation::Move(ref dest, value, None) = *op {
            if let Some(mem) = value.if_memory() {
                if mem.size == MemAccessSize::Mem8 {
                    let value = self.resolve(value);
                    if let Some(mem) = value.if_mem8() {
                        let skip = aliasing_mem8_check(mem);
                        if skip {
                            self.skip_operation();
                            let ctx = self.ctx();
                            let state = self.exec_state();
                            state.move_to(dest, ctx.new_undef());
                        }
                    }
                } else if mem.size == MemAccessSize::Mem32 {
                    if self.resolve_mem(mem).if_constant_address() == Some(0x7ffe026c) {
                        self.skip_operation();
                        let ctx = self.ctx();
                        let state = self.exec_state();
                        state.move_to(dest, ctx.constant(0xa));
                    }
                }
            }
        }
    }

    fn get_new_esp_for_call(&mut self) -> Operand<'e> {
        let ctx = self.ctx();
        self.resolve(ctx.sub_const(
            ctx.register(4),
            <A::Exec as ExecutionState<'e>>::VirtualAddress::SIZE.into(),
        ))
    }

    fn pop_stack(&mut self) {
        let ctx = self.ctx();
        let state = self.exec_state();
        state.move_to(
            &scarf::DestOperand::Register64(4),
            ctx.add_const(
                ctx.register(4),
                <A::Exec as ExecutionState<'e>>::VirtualAddress::SIZE.into(),
            ),
        );
    }

    fn check_stack_probe(&mut self) -> bool {
        if A::Exec::WORD_SIZE == MemAccessSize::Mem64 {
            let state = self.exec_state();
            if let Some(c) = state.resolve_register(0).if_constant() {
                if c >= 0x4000 {
                    self.skip_operation();
                    return true;
                }
            }
        }
        false
    }

    fn assign_to_unresolved_on_eq_branch(
        &mut self,
        condition: Operand<'e>,
        jump_dest: <A::Exec as ExecutionState<'e>>::VirtualAddress,
    ) {
        if_arithmetic_eq_neq(condition)
            .filter(|x| x.1.if_constant().is_some())
            .and_then(|(l, r, is_eq)| {
                let no_jump_dest = self.current_instruction_end();
                let (assign_branch, other_branch) = match is_eq {
                    true => (jump_dest, no_jump_dest),
                    false => (no_jump_dest, jump_dest),
                };
                let register_count = match
                    <A::Exec as ExecutionState<'e>>::VirtualAddress::SIZE
                {
                    4 => 8,
                    8 | _ => 16,
                };
                let mut registers = [false; 16];
                let exec_state = self.exec_state();
                let mut any_moved = false;
                let (l, mask) = Operand::and_masked(l);
                for register in 0..register_count {
                    let val = remove_32bit_and::<A::Exec>(exec_state.resolve_register(register));
                    if val == l {
                        registers[register as usize] = true;
                        any_moved = true;
                    }
                }
                if any_moved {
                    self.add_branch_with_current_state(other_branch);
                    let ctx = self.ctx();
                    let exec_state = self.exec_state();
                    for register in 0..register_count {
                        if registers[register as usize] {
                            let new = if mask >= A::Exec::WORD_SIZE.mask() {
                                r
                            } else {
                                ctx.or(
                                    ctx.and_const(
                                        exec_state.resolve_register(register),
                                        !mask,
                                    ),
                                    r,
                                )
                            };
                            exec_state.move_resolved(
                                &scarf::DestOperand::Register64(register),
                                new,
                            );
                        }
                    }
                    self.continue_at_address(assign_branch);
                }
                Some(())
            });
    }

    fn update_jump_register_to_const(
        &mut self,
        condition: Operand<'e>,
        to: Operand<'e>,
    ) {
        if let Some(to) = self.resolve_va(to) {
            let condition = self.resolve(condition);
            self.assign_to_unresolved_on_eq_branch(condition, to);
        }
    }

    fn instruction_contains_address(
        &mut self,
        addr: <A::Exec as ExecutionState<'e>>::VirtualAddress,
    ) -> bool {
        self.address() <= addr && self.current_instruction_end() > addr
    }

    fn continue_at_neq_address(&mut self, eq_zero: bool, jump_dest: Operand<'e>) {
        let dest = match eq_zero {
            true => self.current_instruction_end(),
            false => match self.resolve_va(jump_dest) {
                Some(s) => s,
                None => return,
            }
        };
        self.continue_at_address(dest);
    }
}

fn aliasing_mem8_check(mem: &scarf::MemAccess<'_>) -> bool {
    let (base, offset) = mem.address();
    fn check(op: Operand<'_>) -> bool {
        op.if_arithmetic(ArithOpType::Modulo)
            .or_else(|| op.if_arithmetic(ArithOpType::And))
            .and_then(|x| x.1.if_constant())
            .filter(|&c| c > 0x400)
            .is_some()
    }
    fn check_add_pair<'e>(a: Operand<'e>, b: Operand<'e>) -> bool {
        check(a) && Operand::and_masked(b).0.if_arithmetic_xor().is_some()
    }
    offset == 0xfff ||
        base.if_arithmetic_add().filter(|&(l, r)| {
            check_add_pair(l, r) || check_add_pair(r, l)
        }).is_some()
}

// Hackyish fix for accounting scarf sometimes removing `& ffff_ffff` in 32bit mode
// (Maybe that scarf behaviour can be removed?)
#[inline]
fn remove_32bit_and<'e, E: ExecutionState<'e>>(op: Operand<'e>) -> Operand<'e> {
    if E::VirtualAddress::SIZE == 4 {
        op.if_arithmetic_and_const(0xffff_ffff).unwrap_or(op)
    } else {
        op
    }
}

pub fn read_u32_at<Va: VirtualAddress>(section: &BinarySection<Va>, offset: Rva) -> Option<u32> {
    section.data.get(offset.0 as usize..)
        .and_then(|x| x.get(..4))
        .map(|x| LittleEndian::read_u32(x))
}

pub fn resolve_rdata_const<'e, Va: VirtualAddress>(
    value: Operand<'e>,
    rdata: &BinarySection<Va>,
) -> Option<u64> {
    if let Some(c) = value.if_constant() {
        Some(c)
    } else {
        let mem = value.if_memory()?;
        let addr = Va::from_u64(mem.if_constant_address()?);
        let rdata_start = rdata.virtual_address;
        let rdata_end = rdata_start + rdata.virtual_size;
        if addr >= rdata_start && addr < rdata_end {
            let offset = (addr.as_u64() - rdata_start.as_u64()) as usize;
            let bytes = rdata.data.get(offset..)?.get(..8)?;
            Some(LittleEndian::read_u64(bytes) & mem.size.mask())
        } else {
            None
        }
    }
}

#[inline]
pub fn test_assertions() -> bool {
    cfg!(feature = "test_assertions")
}

#[test]
fn test_mem8_alias() {
    let ctx = &scarf::OperandContext::new();

    // Relatively simple mem accesses shouldn't pass the check
    // global_u8_arr[u16_index]
    let mem = ctx.mem_access(
        ctx.and_const(
            ctx.register(0),
            0xffff,
        ),
        0x1000_0000,
        MemAccessSize::Mem8,
    );
    assert!(aliasing_mem8_check(&mem) == false);
    // global_u8_arr[u32_index]
    let mem = ctx.mem_access(
        ctx.and_const(
            ctx.register(0),
            0xffff_fffff,
        ),
        0x1000_0000,
        MemAccessSize::Mem8,
    );
    assert!(aliasing_mem8_check(&mem) == false);
}
