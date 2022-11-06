use bumpalo::collections::Vec as BumpVec;

use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, Operand, BinaryFile, BinarySection, Operation};

use crate::analysis::{AnalysisCtx, ArgCache};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until, find_bytes};
use crate::analysis_state::{
    AnalysisState, StateEnum, FindCacheRenderAsciiState, IsCacheRenderAsciiState,
};
use crate::struct_layouts;
use crate::util::{OptionExt, OperandExt, single_result_assign, bumpvec_with_capacity, ControlExt};

#[derive(Clone)]
pub struct FontRender<Va: VirtualAddress> {
    pub font_cache_render_ascii: Option<Va>,
    pub ttf_cache_character: Option<Va>,
    pub ttf_render_sdf: Option<Va>,
}

pub(crate) fn fonts<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let funcs = functions.functions();

    let rdata = analysis.binary_sections.rdata;
    let font_string_rvas = find_bytes(bump, &rdata.data, b"font16x");

    let candidates = font_string_rvas.iter().flat_map(|&font| {
        functions.find_functions_using_global(analysis, rdata.virtual_address + font.0)
    });
    let candidates = BumpVec::from_iter_in(candidates, bump);

    // Search for code that does
    // fonts[0] = Func("font8")
    // fonts[1] = Func("font10")
    // fonts[2] = Func("font16")
    // fonts[3] = Func("font16x")
    // Uses Custom(x) to store what offset in array the result is stored to
    let mut result = None;
    let arg_cache = &analysis.arg_cache;
    for cand in candidates {
        let use_address = cand.use_address;
        let val = entry_of_until(binary, funcs, use_address, |entry| {
            let mut analyzer = FontsAnalyzer::<E> {
                result: EntryOf::Retry,
                use_address,
                candidates: BumpVec::new_in(bump),
                arg_cache,
                rdata,
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option();
        if single_result_assign(val, &mut result) {
            break;
        }
    }
    result
}

struct FontsAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: EntryOf<Operand<'e>>,
    use_address: E::VirtualAddress,
    candidates: BumpVec<'a, FontsCandidate<'e>>,
    arg_cache: &'a ArgCache<'e, E>,
    rdata: &'e BinarySection<E::VirtualAddress>,
}

struct FontsCandidate<'e> {
    base: Operand<'e>,
    seen_bits: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FontsAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() <= self.use_address &&
            ctrl.current_instruction_end() > self.use_address
        {
            self.result = EntryOf::Stop;
        }
        match *op {
            Operation::Call(_) => {
                if let Some(arg1) = ctrl.resolve(self.arg_cache.on_call(0)).if_constant() {
                    let rdata = &self.rdata;
                    if arg1 >= rdata.virtual_address.as_u64() {
                        let offset = arg1 - rdata.virtual_address.as_u64();
                        let offset = rdata.data.get((offset as usize)..)
                            .and_then(|slice| {
                                let slice_len = slice.iter().take(8).position(|&x| x == 0)?;
                                Some(&slice[..slice_len])
                            })
                            .and_then(|string| {
                                match string {
                                    b"font8" => Some(0),
                                    b"font10" => Some(1),
                                    b"font16" => Some(2),
                                    b"font16x" => Some(3),
                                    _ => None,
                                }
                            });
                        if let Some(offset) = offset {
                            let ctx = ctrl.ctx();
                            ctrl.skip_operation();
                            let exec_state = ctrl.exec_state();
                            exec_state.move_to(
                                &DestOperand::Register64(0),
                                ctx.custom(offset),
                            );
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(ref mem), val, None) => {
                let val = ctrl.resolve(val);
                if let Some(offset) = val.if_custom() {
                    let mem = ctrl.resolve_mem(mem);
                    let ctx = ctrl.ctx();
                    let base = ctx.mem_sub_const_op(
                        &mem,
                        (offset * E::VirtualAddress::SIZE) as u64
                    );
                    let index = match self.candidates.iter().position(|x| x.base == base) {
                        Some(s) => s,
                        None => {
                            self.candidates.push(FontsCandidate {
                                base,
                                seen_bits: 0,
                            });
                            self.candidates.len() - 1
                        }
                    };
                    let cand = &mut self.candidates[index];
                    cand.seen_bits |= 1 << offset;
                    if cand.seen_bits == 0xf {
                        self.result = EntryOf::Ok(cand.base);
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}

pub(crate) fn font_render<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    fonts: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> FontRender<E::VirtualAddress> {
    let mut result = FontRender {
        font_cache_render_ascii: None,
        ttf_cache_character: None,
        ttf_render_sdf: None,
    };
    // Find ttf init func, which reads config for "shadowOffset" and calls font_cache_render_ascii
    // (arg 1 = `fonts[i]`, or `fonts[i] + 14` since 1238d)
    // font_cache_render_ascii is identified by it doing a 0x20 ..= 0x7e loop
    // Last function font_cache_render_ascii calls in the loop is ttf_cache_character
    // (arg2 = char)
    // that function's child function calls ttf_render_sdf, with certain known args.
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let funcs = functions.functions();

    let rdata = analysis.binary_sections.rdata;
    let font_string_rvas = find_bytes(bump, &rdata.data, b"shadowOffset");

    let ttf_init_candidates = font_string_rvas.iter().flat_map(|&font| {
        functions.find_functions_using_global(analysis, rdata.virtual_address + font.0)
    });
    let ttf_init_candidates = BumpVec::from_iter_in(ttf_init_candidates, bump);
    let arg_cache = &analysis.arg_cache;
    for ttf_init in ttf_init_candidates {
        let use_address = ttf_init.use_address;
        entry_of_until(binary, funcs, use_address, |entry| {
            let mut analyzer = FindCacheRenderAscii::<E> {
                result: &mut result,
                use_address,
                arg_cache,
                entry_of: EntryOf::Retry,
                binary,
                fonts,
                checked_functions: bumpvec_with_capacity(16, bump),
                bump,
            };
            let exec = E::initial_state(ctx, binary);
            let state = FindCacheRenderAsciiState {
                shadow_offset_seen: false,
            };
            let state = AnalysisState::new(bump, StateEnum::FontCacheRenderAscii(state));
            let mut analysis = FuncAnalysis::custom_state(binary, ctx, entry, exec, state);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of
        });
        if result.font_cache_render_ascii.is_some() {
            break;
        }
    }
    result
}

struct FindCacheRenderAscii<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut FontRender<E::VirtualAddress>,
    entry_of: EntryOf<()>,
    use_address: E::VirtualAddress,
    arg_cache: &'acx ArgCache<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    fonts: Operand<'e>,
    checked_functions: BumpVec<'acx, E::VirtualAddress>,
    bump: &'acx bumpalo::Bump,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    FindCacheRenderAscii<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() <= self.use_address &&
            ctrl.current_instruction_end() > self.use_address
        {
            self.entry_of = EntryOf::Stop;
            ctrl.user_state().set(FindCacheRenderAsciiState {
                shadow_offset_seen: true,
            });
        }
        match *op {
            Operation::Call(dest) => {
                if ctrl.user_state().get::<FindCacheRenderAsciiState>().shadow_offset_seen {
                    if let Some(dest) = ctrl.resolve_va(dest) {
                        let ctx = ctrl.ctx();
                        let ecx = ctrl.resolve(ctx.register(1));
                        let ok = ecx.if_arithmetic_add()
                            .and_then(|(l, r)| {
                                r.if_constant()?;
                                Some(l)
                            })
                            .or_else(|| Some(ecx))
                            .and_then(|x| ctrl.if_mem_word(x))
                            .filter(|&mem| {
                                let (base, offset) = mem.address();
                                base == self.fonts || Some(offset) == self.fonts.if_constant()
                            })
                            .filter(|_| {
                                self.checked_functions.iter().any(|&x| x == dest) == false
                            })
                            .is_some();
                        if ok {
                            self.checked_functions.push(dest);
                            let binary = self.binary;
                            let mut analyzer = IsCacheRenderAscii::<E> {
                                result: self.result,
                                arg_cache: self.arg_cache,
                                ok_calls: BumpVec::new_in(self.bump),
                                binary,
                            };
                            let exec = E::initial_state(ctx, binary);
                            let state = IsCacheRenderAsciiState {
                                last_ok_call: None,
                            };
                            let state = AnalysisState::new(
                                self.bump,
                                StateEnum::IsFontCacheRenderAscii(state),
                            );
                            let mut analysis =
                                FuncAnalysis::custom_state(binary, ctx, dest, exec, state);
                            analysis.analyze(&mut analyzer);
                            if self.result.ttf_cache_character.is_some() {
                                self.entry_of = EntryOf::Stop;
                                self.result.font_cache_render_ascii = Some(dest);
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

struct IsCacheRenderAscii<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut FontRender<E::VirtualAddress>,
    arg_cache: &'acx ArgCache<'e, E>,
    ok_calls: BumpVec<'acx, E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    IsCacheRenderAscii<'a, 'acx, 'e, E>
{
    type State = AnalysisState<'acx, 'e>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                let state = ctrl.user_state().get::<IsCacheRenderAsciiState>();
                if let Some(call) = state.last_ok_call {
                    let call = E::VirtualAddress::from_u64(call);
                    let condition = ctrl.resolve(condition);
                    // Check for while (character < 0x7f) (signed)
                    let is_loop = condition.if_arithmetic_gt()
                        .and_then(|(l, _)| l.if_constant())
                        .filter(|&c| c == 0x8000_007f)
                        .is_some();
                    if is_loop {
                        let ctx = ctrl.ctx();
                        let mut analyzer = TtfCacheCharacterAnalyzer::<E> {
                            result: self.result,
                            arg_cache: self.arg_cache,
                            inline_depth: 0,
                        };
                        let mut analysis = FuncAnalysis::new(self.binary, ctx, call);
                        analysis.analyze(&mut analyzer);
                        if self.result.ttf_render_sdf.is_some() {
                            self.result.ttf_cache_character = Some(call);
                        }
                        ctrl.end_analysis();
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if self.ok_calls.iter().any(|&x| x == dest) {
                        ctrl.user_state().set(IsCacheRenderAsciiState {
                            last_ok_call: Some(dest.as_u64()),
                        });
                    } else {
                        let arg1 = ctrl.resolve(self.arg_cache.on_thiscall_call(0));
                        let arg2 = ctrl.resolve(self.arg_cache.on_thiscall_call(1));
                        let ctx = ctrl.ctx();
                        if arg1 == ctx.const_0() && arg2.if_constant() == Some(0x20) {
                            self.ok_calls.push(dest);
                            ctrl.user_state().set(IsCacheRenderAsciiState {
                                last_ok_call: Some(dest.as_u64()),
                            });
                        }
                    }
                }
            }
            _ => (),
        }
    }
}

struct TtfCacheCharacterAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut FontRender<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    inline_depth: u8,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for TtfCacheCharacterAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                let ctx = ctrl.ctx();
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let ecx = ctrl.resolve(ctx.register(1));
                    // Args 4, 5, 6 are hardcoded constants. Either
                    //  0xd, 0xb4, 13.84615 (newer)
                    //  0xd, 0xb4, 13.0 (new)
                    //  0xa, 0xb4, 18.0 (old)
                    let args_ok = Some(())
                        .map(|_| ctrl.resolve(self.arg_cache.on_call(0)))
                        .filter(|&a1| self.is_glyph_set_ptr(a1))
                        .and_then(|_| {
                            let arg4 = ctx.and_const(
                                ctrl.resolve(self.arg_cache.on_call(3)),
                                0xff,
                            ).if_constant()?;
                            let arg5 = ctx.and_const(
                                ctrl.resolve(self.arg_cache.on_call(4)),
                                0xff,
                            ).if_constant()?;
                            let arg6 = ctx.and_const(
                                ctrl.resolve(self.arg_cache.on_call(5)),
                                0xffff_ffff,
                            );
                            let arg6 = arg6.if_constant()
                                .or_else(|| {
                                    // Read from memory if data/rdata value,
                                    // which it may be due to being a float
                                    let mem = arg6.if_memory()?;
                                    let addr = E::VirtualAddress::from_u64(
                                        mem.if_constant_address()?
                                    );
                                    let binary = ctrl.binary();
                                    Some(binary.read_u64(addr).ok()? & mem.size.mask())
                                })?;
                            let arg6_masked = arg6 & 0xfff0_0000;
                            let ok =
                                (arg4 == 0xd && arg5 == 0xb4 && arg6_masked == 0x41500000) ||
                                (arg4 == 0xa && arg5 == 0xb4 && arg6_masked == 0x41900000);
                            if ok {
                                Some(())
                            } else {
                                None
                            }
                        })
                        .is_some();
                    if args_ok {
                        self.result.ttf_render_sdf = Some(dest);
                        ctrl.end_analysis();
                    } else if self.is_glyph_set_ptr(ecx) {
                        if self.inline_depth < 2 {
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if self.result.ttf_render_sdf.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                ctrl.skip_call_preserve_esp();
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> TtfCacheCharacterAnalyzer<'a, 'e, E> {
    /// Checks for ecx + arg1 * 0xa0
    fn is_glyph_set_ptr(&self, op: Operand<'e>) -> bool {
        op.if_arithmetic_add()
            .and_either_other(|x| x.if_register().filter(|&r| r == 1))
            .and_then(|x| {
                x.if_arithmetic_mul_const(
                    struct_layouts::glyph_set_size::<E::VirtualAddress>(),
                )
            })
            .filter(|&x| Operand::and_masked(x).0 == self.arg_cache.on_thiscall_entry(0))
            .is_some()
    }
}

pub(crate) fn ttf_malloc<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    ttf_render_sdf: E::VirtualAddress,
) -> Option<E::VirtualAddress> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut analyzer = FindTtfMalloc::<E> {
        arg_cache: &analysis.arg_cache,
        result: None,
    };
    let mut analysis = FuncAnalysis::new(binary, ctx, ttf_render_sdf);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

struct FindTtfMalloc<'a, 'e, E: ExecutionState<'e>> {
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindTtfMalloc<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                    // Malloc is called with (a4 + right - left) * (a4 + bottom - top)
                    // (a4 is border width)
                    let arg4 = self.arg_cache.on_entry(3);
                    let arg1_ok = Operand::and_masked(arg1.unwrap_sext()).0
                        .if_arithmetic_mul()
                        .filter(|(l, r)| {
                            l.iter_no_mem_addr().any(|op| op == arg4) &&
                                r.iter_no_mem_addr().any(|op| op == arg4)
                        })
                        .is_some();
                    if arg1_ok {
                        self.result = Some(dest);
                        ctrl.end_analysis();
                    }
                }
                ctrl.skip_call_preserve_esp();
            }
            _ => (),
        }
    }
}
