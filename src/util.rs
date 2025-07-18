//! Miscellaneous helper functions and extension traits.
//!
//! Almost everything is reimported at crate root for backwards compat, though probably
//! should now prefer importing directly from this module.

use arrayvec::ArrayVec;
use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;
use byteorder::{ByteOrder, LittleEndian};

use scarf::analysis::{self, Control};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{
    ArithOpType, BinaryFile, BinarySection, MemAccessSize, Operand, OperandCtx, OperandType, Rva
};

use crate::struct_layouts::{StructLayouts};

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
) -> bool {
    let binary = ctrl.binary();
    let state = ctrl.exec_state();
    seems_assertion_call_less_generic(state, binary)
}

pub fn seems_assertion_call_less_generic<'e, E: ExecutionState<'e>>(
    state: &mut E,
    binary: &BinaryFile<E::VirtualAddress>,
) -> bool {
    // Could check that these are strings
    let arg1 = match state.resolve_arg(0).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg2 = match state.resolve_arg(1).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg3 = match state.resolve_arg(2).if_constant() {
        Some(s) => s,
        None => return false,
    };
    let arg4 = match state.resolve_arg(3).if_constant() {
        Some(s) => s,
        None => return false,
    };
    if arg4 == 0 || arg4 > 12000 {
        return false;
    }
    for arg in [arg1, arg2, arg3] {
        let addr = E::VirtualAddress::from_u64(arg);
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
    /// If `self` is x & C, returns `x`. Otherwise resturns `self`
    fn unwrap_and_mask(self) -> Operand<'e>;
    fn if_constant_or_read_binary<Va: VirtualAddress>(
        self,
        binary: &BinaryFile<Va>,
    ) -> Option<u64>;
    /// bool true => eq, bool false => not eq
    fn if_arithmetic_eq_neq(self) -> Option<(Operand<'e>, Operand<'e>, bool)>;
    /// bool true => eq, bool false => not eq
    fn if_arithmetic_eq_neq_zero(self, ctx: OperandCtx<'e>) -> Option<(Operand<'e>, bool)>;
    /// Matches x & mask => (x, true)
    ///     (x & mask) == 0 => (x, false)
    /// "eq" in this case "jump if zero" / "bit clear"
    /// Which may be confusing?
    fn if_and_mask_eq_neq(self, mask: u64) -> Option<(Operand<'e>, bool)>;
}

impl<'e> OperandExt<'e> for Operand<'e> {
    fn if_arithmetic_add_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_add_with_const()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_sub_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_sub_with_const()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_mul_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_mul_with_const()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_and_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_and_with_const()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_lsh_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_lsh_with_const()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_rsh_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_rsh_with_const()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_eq_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_eq_with_const()?;
        if r != offset {
            None
        } else {
            Some(l)
        }
    }

    fn if_arithmetic_gt_const(self, offset: u64) -> Option<Operand<'e>> {
        let (l, r) = self.if_gt_with_const()?;
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
        self.if_sign_extend().map(|x| x.0).unwrap_or(self)
    }

    fn unwrap_and_mask(self) -> Operand<'e> {
        Operand::and_masked(self).0
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
        if let Some((left, right)) = self.if_arithmetic_eq() {
            if let Some((l, r)) = left.if_arithmetic_eq() {
                if right.if_constant() == Some(0) {
                    return Some((l, r, false));
                }
            }
            Some((left, right, true))
        } else if let Some((left, right)) = self.if_arithmetic_xor() {
            if self.relevant_bits().end == 1 {
                // 1bit x ^ y is x != y
                Some((left, right, false))
            } else {
                None
            }
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

    fn if_and_mask_eq_neq(self, mask: u64) -> Option<(Operand<'e>, bool)> {
        let eq;
        let val;
        if mask == 1 {
            // x & 1 == 0 or just x & 1
            if let Some(a) = self.if_arithmetic_eq_const(0) {
                eq = true;
                val = a;
            } else {
                eq = false;
                val = self;
            }
        } else {
            // x & 10 == 0 or (x & 10 == 0) == 0
            let inner = self.if_arithmetic_eq_const(0)?;
            if let Some(a) = inner.if_arithmetic_eq_const(0) {
                eq = false;
                val = a;
            } else {
                eq = true;
                val = inner;
            }
        }
        Some((val.if_arithmetic_and_const(mask)?, eq))
    }
}

pub trait ExecStateExt<'e> {
    fn struct_layouts() -> StructLayouts;
    fn resolve_arg(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_u8(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_u16(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_u32(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_thiscall(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_thiscall_u8(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_thiscall_u16(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_thiscall_u32(&mut self, i: u8) -> Operand<'e>;
    fn read_stack_memory(&mut self, offset: u64, size: MemAccessSize) -> Operand<'e>;
}

impl<'e, E: ExecutionState<'e>> ExecStateExt<'e> for E {
    #[inline]
    fn struct_layouts() -> StructLayouts {
        StructLayouts {
            is_64bit: E::WORD_SIZE == MemAccessSize::Mem64
        }
    }

    fn resolve_arg(&mut self, i: u8) -> Operand<'e> {
        if E::WORD_SIZE == MemAccessSize::Mem64 {
            if i < 4 {
                let reg = match i {
                    0 => 1,
                    1 => 2,
                    2 => 8,
                    3 | _ => 9,
                };
                self.resolve_register(reg)
            } else {
                self.read_stack_memory(i as u64 * 8, E::WORD_SIZE)
            }
        } else {
            self.read_stack_memory(i as u64 * 4, E::WORD_SIZE)
        }
    }
    fn resolve_arg_u8(&mut self, i: u8) -> Operand<'e> {
        let arg = self.resolve_arg(i);
        self.ctx().and_const(arg, 0xff)
    }
    fn resolve_arg_u16(&mut self, i: u8) -> Operand<'e> {
        let arg = self.resolve_arg(i);
        self.ctx().and_const(arg, 0xffff)
    }
    fn resolve_arg_u32(&mut self, i: u8) -> Operand<'e> {
        let arg = self.resolve_arg(i);
        self.ctx().and_const(arg, 0xffff_ffff)
    }
    #[inline]
    fn resolve_arg_thiscall(&mut self, i: u8) -> Operand<'e> {
        if E::WORD_SIZE == MemAccessSize::Mem64 {
            self.resolve_arg(i.wrapping_add(1))
        } else {
            self.resolve_arg(i)
        }
    }
    #[inline]
    fn resolve_arg_thiscall_u8(&mut self, i: u8) -> Operand<'e> {
        if E::WORD_SIZE == MemAccessSize::Mem64 {
            self.resolve_arg_u8(i.wrapping_add(1))
        } else {
            self.resolve_arg_u8(i)
        }
    }
    #[inline]
    fn resolve_arg_thiscall_u16(&mut self, i: u8) -> Operand<'e> {
        if E::WORD_SIZE == MemAccessSize::Mem64 {
            self.resolve_arg_u16(i.wrapping_add(1))
        } else {
            self.resolve_arg_u16(i)
        }
    }
    #[inline]
    fn resolve_arg_thiscall_u32(&mut self, i: u8) -> Operand<'e> {
        if E::WORD_SIZE == MemAccessSize::Mem64 {
            self.resolve_arg_u32(i.wrapping_add(1))
        } else {
            self.resolve_arg_u32(i)
        }
    }
    fn read_stack_memory(&mut self, offset: u64, size: MemAccessSize) -> Operand<'e> {
        let ctx = self.ctx();
        let rsp = self.resolve_register(4);
        let mem = ctx.mem_access(rsp, offset, size);
        self.read_memory(&mem)
    }
}

pub trait MemAccessExt<'e> {
    fn is_global(&self) -> bool;
}

impl<'e> MemAccessExt<'e> for scarf::MemAccess<'e> {
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
        if let OperandType::Arithmetic(ref arith) = *op.ty() {
            // Nicer for tail calls to check right first as it doesn't recurse in operand chains
            if !is_global_rec(arith.right) {
                return false;
            }
            op = arith.left;
            continue;
        } else if let OperandType::Memory(ref mem) = *op.ty() {
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

pub trait ControlExt<'e, E: ExecutionState<'e>, User: analysis::AnalysisState> {
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
    /// Does just (self.state.clone(), addr) where
    /// addr is either jump_dest if eq_zero is false
    /// or self.current_instruction_end() if eq_zero is true.
    ///
    /// eq_zero is same bool as returned from if_arithmetic_eq_neq_zero.
    ///
    /// Can only fail if jump_dest is not constant.
    fn state_for_neq_address(
        &mut self,
        eq_zero: bool,
        jump_dest: Operand<'e>,
    ) -> Option<(E, User, E::VirtualAddress)>;
    fn state_for_eq_address(
        &mut self,
        eq_zero: bool,
        jump_dest: Operand<'e>,
    ) -> Option<(E, User, E::VirtualAddress)> {
        self.state_for_neq_address(!eq_zero, jump_dest)
    }
    /// Continues with state and address, *clearing all unchecked branches*, and ending current
    /// branch.
    fn continue_with_state(&mut self, state: (E, User, E::VirtualAddress));

    /// Return true => tail_call, false => call.
    /// Also does resolve_va() for call dest.
    fn call_or_tail_call(
        &mut self,
        operation: &scarf::Operation<'e>,
        entry_esp: Operand<'e>,
    ) -> Option<(E::VirtualAddress, bool)>;

    fn resolve_arg(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_u8(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_u16(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_u32(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_thiscall(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_thiscall_u8(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_thiscall_u16(&mut self, i: u8) -> Operand<'e>;
    fn resolve_arg_thiscall_u32(&mut self, i: u8) -> Operand<'e>;
}

impl<'a, 'b, 'e, A: scarf::analysis::Analyzer<'e>> ControlExt<'e, A::Exec, A::State> for
    scarf::analysis::Control<'e, 'a, 'b, A>
{
    fn resolve_va(&mut self, operand: Operand<'e>) ->
        Option<<A::Exec as ExecutionState<'e>>::VirtualAddress>
    {
        // Try just if_constant without resolving first as that is almost always the case
        operand.if_constant().or_else(|| self.resolve(operand).if_constant())
            .filter(|&va| va >= self.binary().base().as_u64())
            .map(|x| <A::Exec as ExecutionState<'e>>::VirtualAddress::from_u64(x))
    }

    fn skip_call_preserve_esp(&mut self) {
        self.skip_operation();
        let state = self.exec_state();
        skip_call_preserve_esp_less_generic(state);
    }

    fn do_call_with_result(&mut self, result: Operand<'e>) {
        self.skip_operation();
        let state = self.exec_state();
        do_call_with_result_less_generic(state, result);
    }

    fn aliasing_memory_fix(&mut self, op: &scarf::Operation<'e>) {
        let state = self.exec_state();
        let skip = aliasing_memory_fix_less_generic(state, op);
        if skip {
            self.skip_operation();
        }
    }

    fn get_new_esp_for_call(&mut self) -> Operand<'e> {
        let ctx = self.ctx();
        ctx.sub_const(
            self.resolve_register(4),
            <A::Exec as ExecutionState<'e>>::VirtualAddress::SIZE.into(),
        )
    }

    fn pop_stack(&mut self) {
        let state = self.exec_state();
        pop_stack_less_generic(state);
    }

    fn check_stack_probe(&mut self) -> bool {
        let state = self.exec_state();
        if let Some(c) = state.resolve_register(0).if_constant() {
            let va_size = <A::Exec as ExecutionState<'e>>::VirtualAddress::SIZE;
            if c >= 0x1000 && (c as u32) & (va_size - 1) == 0 {
                self.skip_operation();
                return true;
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
                // TODO make less generic
                let no_jump_dest = self.current_instruction_end();
                let exec_state = self.exec_state();
                let ctx = exec_state.ctx();
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
                            exec_state.set_register(register, new);
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

    fn state_for_neq_address(
        &mut self,
        eq_zero: bool,
        jump_dest: Operand<'e>,
    ) -> Option<(A::Exec, A::State, <A::Exec as ExecutionState<'e>>::VirtualAddress)> {
        let dest = match eq_zero {
            true => self.current_instruction_end(),
            false => match self.resolve_va(jump_dest) {
                Some(s) => s,
                None => return None,
            }
        };
        let user = self.user_state().clone();
        let state = self.exec_state().clone();
        Some((state, user, dest))
    }

    fn continue_with_state(
        &mut self,
        state: (A::Exec, A::State, <A::Exec as ExecutionState<'e>>::VirtualAddress),
    ) {
        self.end_branch();
        self.clear_unchecked_branches();
        self.add_branch_with_state(state.2, state.0, state.1);
    }

    fn call_or_tail_call(
        &mut self,
        operation: &scarf::Operation<'e>,
        entry_esp: Operand<'e>,
    ) -> Option<(<A::Exec as ExecutionState<'e>>::VirtualAddress, bool)> {
        match *operation {
            scarf::Operation::Call(dest) => {
                Some((self.resolve_va(dest)?, false))
            }
            scarf::Operation::Jump { condition, to } => {
                if self.resolve_register(4) == entry_esp && condition == self.ctx().const_1() {
                    Some((self.resolve_va(to)?, true))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    #[inline]
    fn resolve_arg(&mut self, i: u8) -> Operand<'e> {
        self.exec_state().resolve_arg(i)
    }
    #[inline]
    fn resolve_arg_u8(&mut self, i: u8) -> Operand<'e> {
        self.exec_state().resolve_arg_u8(i)
    }
    #[inline]
    fn resolve_arg_u16(&mut self, i: u8) -> Operand<'e> {
        self.exec_state().resolve_arg_u16(i)
    }
    #[inline]
    fn resolve_arg_u32(&mut self, i: u8) -> Operand<'e> {
        self.exec_state().resolve_arg_u32(i)
    }
    #[inline]
    fn resolve_arg_thiscall(&mut self, i: u8) -> Operand<'e> {
        self.exec_state().resolve_arg_thiscall(i)
    }
    #[inline]
    fn resolve_arg_thiscall_u8(&mut self, i: u8) -> Operand<'e> {
        self.exec_state().resolve_arg_thiscall_u8(i)
    }
    #[inline]
    fn resolve_arg_thiscall_u16(&mut self, i: u8) -> Operand<'e> {
        self.exec_state().resolve_arg_thiscall_u16(i)
    }
    #[inline]
    fn resolve_arg_thiscall_u32(&mut self, i: u8) -> Operand<'e> {
        self.exec_state().resolve_arg_thiscall_u32(i)
    }
}

fn skip_call_preserve_esp_less_generic<'e, E: ExecutionState<'e>>(state: &mut E) {
    let ctx = state.ctx();
    for i in 0..3 {
        state.set_register(i, ctx.new_undef());
    }
    if E::WORD_SIZE == MemAccessSize::Mem64 {
        for i in 8..10 {
            state.set_register(i, ctx.new_undef());
        }
    }
}

fn do_call_with_result_less_generic<'e, E: ExecutionState<'e>>(
    state: &mut E,
    result: Operand<'e>,
) {
    let ctx = state.ctx();
    state.set_register(0, result);
    for i in 1..3 {
        state.set_register(i, ctx.new_undef());
    }
    if E::WORD_SIZE == MemAccessSize::Mem32 {
        state.set_register(4, ctx.new_undef());
    } else {
        for i in 8..10 {
            state.set_register(i, ctx.new_undef());
        }
    }
}

fn pop_stack_less_generic<'e, E: ExecutionState<'e>>(state: &mut E) {
    let ctx = state.ctx();
    let old_esp = state.resolve_register(4);
    let new_esp = ctx.add_const(old_esp, E::VirtualAddress::SIZE.into());
    state.set_register(4, new_esp);
}

fn aliasing_memory_fix_less_generic<'e, E: ExecutionState<'e>>(
    state: &mut E,
    op: &scarf::Operation<'e>,
) -> bool {
    if let scarf::Operation::Move(ref dest, value) = *op {
        if let Some(mem) = value.if_memory() {
            if mem.size == MemAccessSize::Mem8 {
                let value = state.resolve(value);
                if let Some(mem) = value.if_mem8() {
                    let skip = aliasing_mem8_check(mem);
                    if skip {
                        let ctx = state.ctx();
                        state.move_to(dest, ctx.new_undef());
                        return true;
                    }
                }
            } else if mem.size == MemAccessSize::Mem32 {
                if state.resolve_mem(mem).if_constant_address() == Some(0x7ffe026c) {
                    let ctx = state.ctx();
                    state.move_to(dest, ctx.constant(0xa));
                    return true;
                }
            }
        }
    }
    false
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

pub fn make_jump_unconditional<Va: VirtualAddress>(
    binary: &BinaryFile<Va>,
    address: Va,
) -> Option<ArrayVec<u8, 0x8>> {
    let bytes = binary.slice_from_address(address, 0x10).ok()?;
    assert!(bytes.len() == 0x10);

    let mut out = ArrayVec::new();
    if bytes[0] == 0x0f && matches!(bytes[1], 0x80 ..= 0x8f) {
        let _ = out.try_extend_from_slice(&[0x90, 0xe9, bytes[2], bytes[3], bytes[4], bytes[5]]);
        Some(out)
    } else if matches!(bytes[0], 0x70 ..= 0x7f) {
        let _ = out.try_extend_from_slice(&[0xeb, bytes[1]]);
        Some(out)
    } else {
        None
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
