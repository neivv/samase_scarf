use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, Operand, BinaryFile, BinarySection, Operation};

use crate::{Analysis, ArgCache, entry_of_until, EntryOf, OptionExt, single_result_assign};

#[derive(Clone)]
pub struct FontRender<Va: VirtualAddress> {
    pub font_cache_render_ascii: Option<Va>,
    pub ttf_cache_character: Option<Va>,
    pub ttf_render_sdf: Option<Va>,
}

pub fn fonts<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> Option<Operand<'e>> {
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = analysis.functions();
    let funcs = &funcs[..];

    let rdata = binary.section(b".rdata\0\0").unwrap();
    let font_string_rvas = crate::find_bytes(&rdata.data, b"font16x");

    let candidates = font_string_rvas.iter().flat_map(|&font| {
        crate::find_functions_using_global(analysis, rdata.virtual_address + font.0)
    }).collect::<Vec<_>>();

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
                candidates: Vec::new(),
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
    candidates: Vec<FontsCandidate<'e>>,
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
                                &DestOperand::Register64(scarf::operand::Register(0)),
                                ctx.custom(offset),
                            );
                        }
                    }
                }
            }
            Operation::Move(DestOperand::Memory(mem), val, None) => {
                let val = ctrl.resolve(val);
                if let Some(offset) = val.if_custom() {
                    let addr = ctrl.resolve(mem.address);
                    let ctx = ctrl.ctx();
                    let base = ctx.sub_const(addr, (offset * E::VirtualAddress::SIZE) as u64);
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

pub fn font_render<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> FontRender<E::VirtualAddress> {
    let mut result = FontRender {
        font_cache_render_ascii: None,
        ttf_cache_character: None,
        ttf_render_sdf: None,
    };
    let fonts = match analysis.fonts() {
        Some(s) => s,
        None => return result,
    };
    // Find ttf init func, which reads config for "shadowOffset" and calls font_cache_render_ascii
    // (arg 1 = fonts[i])
    // font_cache_render_ascii is identified by it doing a 0x20 ..= 0x7e loop
    // Last function font_cache_render_ascii calls in the loop is ttf_cache_character
    // (arg2 = char)
    // that function's child function calls ttf_render_sdf, with certain known args.
    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let funcs = analysis.functions();
    let funcs = &funcs[..];

    let rdata = binary.section(b".rdata\0\0").unwrap();
    let font_string_rvas = crate::find_bytes(&rdata.data, b"shadowOffset");

    let ttf_init_candidates = font_string_rvas.iter().flat_map(|&font| {
        crate::find_functions_using_global(analysis, rdata.virtual_address + font.0)
    }).collect::<Vec<_>>();
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
                checked_functions: Vec::with_capacity(16),
            };
            let exec = E::initial_state(ctx, binary);
            let state = FindCacheRenderAsciiState {
                shadow_offset_seen: false,
            };
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

struct FindCacheRenderAscii<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut FontRender<E::VirtualAddress>,
    entry_of: EntryOf<()>,
    use_address: E::VirtualAddress,
    arg_cache: &'a ArgCache<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    fonts: Operand<'e>,
    checked_functions: Vec<E::VirtualAddress>,
}

#[derive(Copy, Clone)]
struct FindCacheRenderAsciiState {
    shadow_offset_seen: bool,
}

impl analysis::AnalysisState for FindCacheRenderAsciiState {
    fn merge(&mut self, newer: Self) {
        self.shadow_offset_seen |= newer.shadow_offset_seen;
    }
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for FindCacheRenderAscii<'a, 'e, E> {
    type State = FindCacheRenderAsciiState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() <= self.use_address &&
            ctrl.current_instruction_end() > self.use_address
        {
            self.entry_of = EntryOf::Stop;
            ctrl.user_state().shadow_offset_seen = true;
        }
        match *op {
            Operation::Call(dest) => {
                if ctrl.user_state().shadow_offset_seen {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        let ctx = ctrl.ctx();
                        let ecx = ctrl.resolve(ctx.register(1));
                        let ok = ctrl.if_mem_word(ecx)
                            .filter(|&addr| {
                                addr == self.fonts &&
                                    self.checked_functions.iter().any(|&x| x == dest) == false
                            })
                            .is_some();
                        if ok {
                            self.checked_functions.push(dest);
                            let binary = self.binary;
                            let mut analyzer = IsCacheRenderAscii::<E> {
                                result: self.result,
                                arg_cache: self.arg_cache,
                                ok_calls: Vec::new(),
                                binary,
                            };
                            let exec = E::initial_state(ctx, binary);
                            let state = IsCacheRenderAsciiState {
                                last_ok_call: None,
                            };
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

struct IsCacheRenderAscii<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut FontRender<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    ok_calls: Vec<E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

#[derive(Clone)]
struct IsCacheRenderAsciiState<Va: VirtualAddress> {
    last_ok_call: Option<Va>,
}

impl<Va: VirtualAddress> analysis::AnalysisState for IsCacheRenderAsciiState<Va> {
    fn merge(&mut self, newer: Self) {
        if self.last_ok_call != newer.last_ok_call {
            self.last_ok_call = None;
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for IsCacheRenderAscii<'a, 'e, E> {
    type State = IsCacheRenderAsciiState<E::VirtualAddress>;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        match *op {
            Operation::Jump { condition, .. } => {
                if let Some(call) = ctrl.user_state().last_ok_call {
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
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.ok_calls.iter().any(|&x| x == dest) {
                        ctrl.user_state().last_ok_call = Some(dest);
                    } else {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        let arg2 = ctrl.resolve(self.arg_cache.on_call(1));
                        if arg1.if_constant() == Some(0) && arg2.if_constant() == Some(0x20) {
                            self.ok_calls.push(dest);
                            ctrl.user_state().last_ok_call = Some(dest);
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
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    let ecx = ctrl.resolve(ctx.register(1));
                    if self.is_glyph_set_ptr(ecx) {
                        if self.inline_depth < 2 {
                            self.inline_depth += 1;
                            ctrl.analyze_with_current_state(self, dest);
                            self.inline_depth -= 1;
                            if self.result.ttf_render_sdf.is_some() {
                                ctrl.end_analysis();
                            }
                        }
                    } else {
                        // Args 4, 5, 6 are hardcoded constants. Either
                        //  0xd, 0xb4, 13.0 (new)
                        //  0xa, 0xb4, 18.0 (old)
                        let args_ok = Some(())
                            .map(|_| ctrl.resolve(self.arg_cache.on_call(0)))
                            .filter(|&a1| self.is_glyph_set_ptr(a1))
                            .and_then(|_| {
                                let arg4 = ctrl.resolve(self.arg_cache.on_call(3)).if_constant()?;
                                let arg5 = ctrl.resolve(self.arg_cache.on_call(4)).if_constant()?;
                                let arg6 = ctrl.resolve(self.arg_cache.on_call(5)).if_constant()?;
                                let ok =
                                    (arg4 == 0xd && arg5 == 0xb4 && arg6 == 0x41500000) ||
                                    (arg4 == 0xa && arg5 == 0xb4 && arg6 == 0x41900000);
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
                        }
                    }
                }
                // Assume esp is left as is (cdecl)
                ctrl.skip_operation();
                let exec_state = ctrl.exec_state();
                for i in 0..2 {
                    exec_state.move_to(
                        &DestOperand::Register64(scarf::operand::Register(i)),
                        ctx.new_undef(),
                    );
                }
            }
            _ => (),
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> TtfCacheCharacterAnalyzer<'a, 'e, E> {
    /// Checks for ecx + arg1 * 0xa0
    fn is_glyph_set_ptr(&self, op: Operand<'e>) -> bool {
        op.if_arithmetic_add()
            .and_either_other(|x| x.if_register().filter(|r| r.0 == 1))
            .and_then(|x| x.if_arithmetic_mul())
            .filter(|(_, r)| r.if_constant().filter(|&c| c == 0xa0).is_some())
            .filter(|&(l, _)| l == self.arg_cache.on_entry(0))
            .is_some()
    }
}
