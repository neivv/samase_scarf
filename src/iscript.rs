use scarf::{
    MemAccessSize, Operand, Operation, DestOperand,
};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::ExecutionState;
use scarf::exec_state::VirtualAddress;

use crate::{AnalysisCtx, ArgCache, ControlExt, OptionExt, OperandExt, single_result_assign};
use crate::struct_layouts::{self, if_unit_sprite};

pub(crate) struct StepIscript<'e, Va: VirtualAddress> {
    pub switch_table: Option<Va>,
    pub iscript_bin: Option<Operand<'e>>,
    pub hook: Option<StepIscriptHook<'e, Va>>,
}

#[derive(Debug, Copy, Clone)]
pub struct StepIscriptHook<'e, Va: VirtualAddress> {
    pub script_operand_at_switch: Operand<'e>,
    pub opcode_check: (Va, u32),
}

pub(crate) fn step_iscript<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    finish_unit_pre: E::VirtualAddress,
    sprite_size: u32,
) -> Option<E::VirtualAddress> {
    // Find step_iscript from finish_unit_pre calling set_iscript_animation(0x10)
    // Inline if arg1 == 0x10 and this == ecx or ecx.sprite or ecx.sprite_first_overlay
    // Recognize step_iscript from
    // this = ecx.sprite.first_overlay, a1 = ecx.sprite.first_overlay.iscript, a2 = 0, a3 = 0

    let ctx = actx.ctx;
    let binary = actx.binary;

    let mut analyzer = FindStepIscript {
        result: None,
        inline_limit: 0,
        arg_cache: &actx.arg_cache,
        sprite_first_overlay:
            struct_layouts::sprite_first_overlay::<E::VirtualAddress>(sprite_size)?,
        entry_esp: ctx.register(4),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, finish_unit_pre);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindStepIscript<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_limit: u8,
    sprite_first_overlay: u32,
    entry_esp: Operand<'e>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindStepIscript<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if let Operation::Call(dest) = *op {
            if self.inline_limit != 0 {
                self.inline_limit -= 1;
                if self.inline_limit == 0 {
                    ctrl.end_analysis();
                    return;
                }
            }
            if let Some(dest) = ctrl.resolve_va(dest) {
                self.check_function_call(ctrl, dest, true);
            }
        } else if let Operation::Jump { to, condition } = *op {
            // step_iscript may be a tail call
            let ctx = ctrl.ctx();
            if condition == ctx.const_1() && ctrl.resolve(ctx.register(4)) == self.entry_esp {
                if let Some(to) = ctrl.resolve_va(to) {
                    self.check_function_call(ctrl, to, false);
                }
            }
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> FindStepIscript<'a, 'e, E> {
    fn check_function_call(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dest: E::VirtualAddress,
        consider_inline: bool,
    ) {
        let ctx = ctrl.ctx();
        let arg_cache = self.arg_cache;
        let this = ctrl.resolve(ctx.register(1));
        let arg1 = ctrl.resolve(arg_cache.on_thiscall_call(0));
        let is_first_overlay = ctrl.if_mem_word(this)
            .and_then(|x| x.if_arithmetic_add_const(self.sprite_first_overlay.into()))
            .and_then(if_unit_sprite::<E::VirtualAddress>) == Some(ctx.register(1));
        if is_first_overlay {
            let zero = ctx.const_0();
            let ok = ctrl.resolve(arg_cache.on_thiscall_call(1)) == zero &&
                ctrl.resolve(arg_cache.on_thiscall_call(2)) == zero &&
                arg1.if_arithmetic_add_const(
                    struct_layouts::image_iscript::<E::VirtualAddress>()
                ).filter(|&x| x == this).is_some();
            if ok {
                self.result = Some(dest);
                ctrl.end_analysis();
                return;
            }
        }
        let inline = consider_inline && (
            is_first_overlay ||
            this == ctx.register(1) ||
            if_unit_sprite::<E::VirtualAddress>(this) == Some(ctx.register(1))
        ) && ctx.and_const(arg1, 0xff).if_constant() == Some(0x10);

        if inline {
            let is_depth0 = self.inline_limit == 0;
            if is_depth0 {
                self.inline_limit = 16;
            }
            let old_esp = self.entry_esp;
            self.entry_esp = ctx.sub_const(
                ctrl.resolve(ctx.register(4)),
                E::VirtualAddress::SIZE.into(),
            );
            ctrl.analyze_with_current_state(self, dest);
            self.entry_esp = old_esp;
            if is_depth0 {
                self.inline_limit = 0;
            } else if self.inline_limit == 0 {
                ctrl.end_analysis();
            }
            if self.result.is_some() {
                ctrl.end_analysis();
            }
        }
    }
}

pub(crate) fn analyze_step_iscript<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_iscript: E::VirtualAddress,
) -> StepIscript<'e, E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;

    let mut result = StepIscript {
        switch_table: None,
        iscript_bin: None,
        hook: None,
    };
    let arg_cache = &analysis.arg_cache;
    let mut analyzer = StepIscriptAnalyzer {
        result: &mut result,
        wait_check_seen: false,
        opcode_check: None,
        arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, step_iscript);
    analysis.analyze(&mut analyzer);
    result
}

struct StepIscriptAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut StepIscript<'e, E::VirtualAddress>,
    wait_check_seen: bool,
    opcode_check: Option<(E::VirtualAddress, u32)>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for StepIscriptAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Move(_, val, None) => {
                if self.result.iscript_bin.is_none() {
                    let val = ctrl.resolve(val);
                    let iscript_bin = val.if_mem8()
                        .and_then(|addr| addr.if_arithmetic_add())
                        .and_either_other(|x| {
                            x.if_mem16().filter(|x| x.if_arithmetic_add().is_some())
                        });
                    if let Some(iscript_bin) = iscript_bin {
                        self.result.iscript_bin = Some(iscript_bin);
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let to = ctrl.resolve(to);
                let switch_jump = ctrl.if_mem_word(to)
                    .and_then(|x| {
                        let (l, r) = x.if_arithmetic_add()?;
                        let switch_table = r.if_constant()?;
                        let (switch_op, r) = l.if_arithmetic_mul()?;
                        r.if_constant()?;
                        let iscript_pos = switch_op.if_mem8()?;
                        Some((E::VirtualAddress::from_u64(switch_table), iscript_pos))
                    });
                if let Some((switch_table, iscript_pos)) = switch_jump {
                    if self.wait_check_seen {
                        self.result.switch_table = Some(switch_table);
                        if let Some(opcode_check) = self.opcode_check {
                            let ctx = ctrl.ctx();
                            let register_count =
                                if E::VirtualAddress::SIZE == 4 { 8 } else { 16 };
                            if let Some(script_operand_at_switch) = (0..register_count)
                                .map(|i| ctx.register(i))
                                .find(|&x| {
                                    let val = ctrl.resolve(x);
                                    let unwrap_increment = val.if_arithmetic_add_const(1)
                                        .map(|x| {
                                            x.if_arithmetic_and_const(0xffff_ffff)
                                                .unwrap_or(x)
                                        })
                                        .unwrap_or(val);
                                    unwrap_increment == iscript_pos
                                })
                            {
                                self.result.hook = Some(StepIscriptHook {
                                    script_operand_at_switch,
                                    opcode_check,
                                });
                            }
                        }
                    }
                    ctrl.end_analysis();
                    return;
                }
                let condition = ctrl.resolve(condition);
                let has_wait_check = condition.iter_no_mem_addr()
                    .filter_map(|x| x.if_mem8()?.if_arithmetic_add_const(7))
                    .filter(|&other| other == self.arg_cache.on_thiscall_entry(0))
                    .next()
                    .is_some();
                if has_wait_check {
                    self.wait_check_seen = true;
                }
                if self.wait_check_seen {
                    let has_opcode_limit_constant = condition.iter_no_mem_addr()
                        .any(|x| x.if_constant().filter(|&c| c == 0x44 || c == 0x45).is_some());
                    let has_mem8 = condition.iter_no_mem_addr()
                        .any(|x| x.if_mem8().is_some());
                    if has_opcode_limit_constant && has_mem8 {
                        let len =
                            ctrl.current_instruction_end().as_u64() - ctrl.address().as_u64();
                        self.opcode_check = Some((ctrl.address(), len as u32));
                        // Skip opcode limit check to prevent making switch op undef;
                        // should not assume the check fail is always branch but it probably
                        // always will be.
                        ctrl.skip_operation();
                        ctrl.add_branch_with_current_state(ctrl.current_instruction_end());
                    }
                }
            }
            _ => ()
        }
    }
}

pub(crate) fn add_overlay_iscript<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    step_iscript_switch: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    // Search for a 5-argument fn(img, sprite (Mem32[x + 3c]), x, y, 1) from
    // iscript opcode 8 (imgol)
    // Sprite is actually unused, but checking for it anyway as the function signature
    // changing isn't anticipated.
    let word_size = <E::VirtualAddress as VirtualAddress>::SIZE;
    let case_8 = binary.read_address(step_iscript_switch + word_size * 8).ok()?;

    let mut analyzer = AddOverlayAnalyzer::<E> {
        result: None,
        args: &analysis.arg_cache,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, case_8);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct AddOverlayAnalyzer<'exec, 'b, Exec: ExecutionState<'exec>> {
    result: Option<Exec::VirtualAddress>,
    args: &'b ArgCache<'exec, Exec>,
}

impl<'e, 'b, Exec: ExecutionState<'e>> scarf::Analyzer<'e> for AddOverlayAnalyzer<'e, 'b, Exec> {
    type State = analysis::DefaultState;
    type Exec = Exec;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let word_size = <Exec::VirtualAddress as VirtualAddress>::SIZE;
        match *op {
            Operation::Jump { to, .. } => {
                let to = ctrl.resolve(to);
                let is_switch_jump = to.if_memory().is_some();
                if is_switch_jump {
                    ctrl.end_branch();
                    return;
                }
            }
            Operation::Call(to) => {
                let to = ctrl.resolve(to);
                if let Some(dest) = to.if_constant() {
                    let arg5 = ctrl.resolve(self.args.on_call(4));
                    let arg5_ok = arg5
                        .if_constant()
                        .filter(|&c| c == 1)
                        .is_some();
                    if !arg5_ok {
                        return;
                    }
                    let arg2 = ctrl.resolve(self.args.on_call(1));
                    // TODO not 64-bit since not sure about image->parent pointer
                    let arg2_ok = if word_size == 4 {
                        arg2
                            .if_mem32()
                            .and_then(|x| x.if_arithmetic_add())
                            .and_either(|x| x.if_constant().filter(|&c| c == 0x3c))
                            .is_some()
                    } else {
                        unimplemented!();
                    };
                    if !arg2_ok {
                        return;
                    }

                    let result = Some(Exec::VirtualAddress::from_u64(dest));
                    if single_result_assign(result, &mut self.result) {
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn draw_cursor_marker<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    iscript_switch_table: E::VirtualAddress,
) -> Option<Operand<'e>> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    // hide_cursor_marker is iscript opcode 0x2d
    let case = binary.read_address(
        iscript_switch_table + 0x2d * <E::VirtualAddress as VirtualAddress>::SIZE
    ).ok()?;

    let mut analyzer = FindDrawCursorMarker::<E> {
        result: None,
        inlining: false,
        phantom: Default::default(),
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, case);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindDrawCursorMarker<'e, E: ExecutionState<'e>> {
    result: Option<Operand<'e>>,
    inlining: bool,
    phantom: std::marker::PhantomData<(*const E, &'e ())>,
}

impl<'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindDrawCursorMarker<'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { to, .. } => {
                if to.if_constant().is_none() {
                    // Skip switch branch
                    ctrl.end_branch();
                }
            }
            Operation::Call(dest) => {
                if !self.inlining {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        self.inlining = true;
                        ctrl.analyze_with_current_state(self, E::VirtualAddress::from_u64(dest));
                        self.inlining = false;
                        if self.result.is_some() {
                            ctrl.end_analysis();
                        }
                    }
                } else {
                    ctrl.end_analysis();
                }
            }
            Operation::Move(ref dest, val, None) => {
                if let DestOperand::Memory(mem) = dest {
                    if mem.size == MemAccessSize::Mem8 {
                        let val = ctrl.resolve(val);
                        if val.if_constant() == Some(0) {
                            let ctx = ctrl.ctx();
                            self.result = Some(ctx.mem_variable_rc(mem.size, mem.address));
                            ctrl.end_analysis();
                        }
                    }
                }
                if self.inlining {
                    ctrl.end_analysis();
                }
            }
            _ => (),
        }
    }
}
