use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::{DestOperand, Operand, BinarySection, Operation};

use crate::{Analysis, ArgCache, entry_of_until, EntryOf, single_result_assign};

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
