use scarf::{Operand, OperandCtx, Operation, DestOperand, Rva};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::add_terms::collect_arith_add_terms;
use crate::{
    ArgCache, AnalysisCtx, single_result_assign, entry_of_until, EntryOf, FunctionFinder,
    bumpvec_with_capacity, OperandExt,
};

#[derive(Clone)]
pub struct SpriteSerialization<Va: VirtualAddress> {
    pub serialize_sprites: Option<Va>,
    pub deserialize_sprites: Option<Va>,
}

pub(crate) fn sprite_serialization<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    sprite_hlines_end: Operand<'e>,
    (sprite_array, sprite_size): (Operand<'e>, u32),
    init_sprites: E::VirtualAddress,
    game: Operand<'e>,
    function_finder: &FunctionFinder<'_, 'e, E>,
) -> SpriteSerialization<E::VirtualAddress> {
    // Find de/serialization functions by checking for
    // sprite_hlines_end[x] = deserialize_sprite_ptr(sprite_hlines_end[x])
    // => sprite_hlines_end[x] = sprite_array + (sprite_hlines_end[x] - 1) * struct_size
    // (Serialization converts them back and forth in place)
    let mut result = SpriteSerialization {
        serialize_sprites: None,
        deserialize_sprites: None,
    };

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let bump = &analysis.bump;
    let functions = function_finder.functions();

    let sprite_array_address = sprite_array.if_constant()
        .or_else(|| sprite_array.if_memory()?.address.if_constant());
    let sprite_array_address = match sprite_array_address {
        Some(s) => E::VirtualAddress::from_u64(s),
        None => return result,
    };
    let globals = function_finder.find_functions_using_global(analysis, sprite_array_address);
    // Note: Globals were sorted and deduped by func_entry, but
    // it turned out to miss something sometimes, so rely on the checked
    // vec instead to avoid duplicate work.
    let mut checked = bumpvec_with_capacity(globals.len(), bump);
    checked.push(Rva((init_sprites.as_u64() - binary.base.as_u64()) as u32));
    let map_height_tiles = ctx.mem16(game, 0xe6);
    let last_y_hline = ctx.add(
        ctx.mul_const(
            ctx.sub_const(map_height_tiles, 1),
            E::VirtualAddress::SIZE as u64,
        ),
        sprite_hlines_end,
    );
    let arg_cache = &analysis.arg_cache;
    for global_ref in globals {
        let val = entry_of_until(binary, &functions, global_ref.func_entry, |entry| {
            let rva = Rva((entry.as_u64() - binary.base.as_u64()) as u32);
            if checked.iter().any(|&e| e == rva) {
                return EntryOf::Stop;
            }
            checked.push(rva);
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            let mut analyzer = SpriteSerializationAnalysis::<E> {
                use_address: global_ref.use_address,
                result: EntryOf::Retry,
                last_y_hline,
                map_height_tiles,
                sprite_size,
                arg_cache,
                bump,
                first_branch: true,
                had_file_call: false,
            };
            analysis.analyze(&mut analyzer);
            analyzer.result
        }).into_option_with_entry();
        if let Some((addr, func_type)) = val {
            match func_type {
                SpriteSerializationFunc::Serialize => {
                    single_result_assign(Some(addr), &mut result.serialize_sprites);
                }
                SpriteSerializationFunc::Deserialize => {
                    single_result_assign(Some(addr), &mut result.deserialize_sprites);
                }
            }
        }
        if crate::test_assertions() == false &&
            result.serialize_sprites.is_some() &&
            result.deserialize_sprites.is_some()
        {
            break;
        }
    }

    result
}

enum SpriteSerializationFunc {
    Serialize,
    Deserialize,
}

struct SpriteSerializationAnalysis<'a, 'e, E: ExecutionState<'e>> {
    use_address: E::VirtualAddress,
    result: EntryOf<SpriteSerializationFunc>,
    last_y_hline: Operand<'e>,
    map_height_tiles: Operand<'e>,
    sprite_size: u32,
    arg_cache: &'a ArgCache<'e, E>,
    bump: &'a bumpalo::Bump,
    first_branch: bool,
    had_file_call: bool,
}

impl<'a, 'e, E: ExecutionState<'e>> scarf::Analyzer<'e> for
    SpriteSerializationAnalysis<'a, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.use_address >= ctrl.address() &&
            self.use_address < ctrl.current_instruction_end()
        {
            self.result = EntryOf::Stop;
        }
        match *op {
            Operation::Jump { .. } => {
                self.first_branch = false;
            }
            Operation::Call(_) => {
                if self.first_branch {
                    let arg3 = ctrl.resolve(self.arg_cache.on_call(2));
                    if arg3.if_constant() == Some(2) {
                        let arg1 = ctrl.resolve(self.arg_cache.on_call(0));
                        if arg1 == self.arg_cache.on_entry(0) {
                            self.had_file_call = true;
                        }
                    }
                }
                self.first_branch = false;
            }
            Operation::Move(DestOperand::Memory(ref mem), value, None) => {
                let value = ctrl.resolve(value);
                let ctx = ctrl.ctx();
                let dest = ctrl.resolve_mem(mem).address_op(ctx);
                if dest == self.last_y_hline {
                    if let Some(mut terms) = collect_arith_add_terms(value, self.bump) {
                        let ok = terms.remove_one(|op, _neg| {
                            op.if_arithmetic_mul_const(self.sprite_size as u64)
                                .filter(|&x| {
                                    // addr == self.last_y_hline or undefined; convert in place
                                    // in older patches,
                                    // [esp - x + game.map_height_tiles] in newer.
                                    x.is_undefined() ||
                                        x.if_mem32()
                                            .filter(|&addr| {
                                                self.is_stack_temp_hlines(ctx, addr) ||
                                                    addr == self.last_y_hline
                                            })
                                            .is_some()
                                })
                                .is_some()
                        });
                        if ok {
                            if self.had_file_call {
                                self.result = EntryOf::Ok(SpriteSerializationFunc::Deserialize);
                            } else {
                                self.result = EntryOf::Ok(SpriteSerializationFunc::Serialize);
                            }
                            ctrl.end_analysis();
                        }
                    }
                } else if !self.had_file_call && self.is_stack_temp_hlines(ctx, dest) {
                    if value.iter().any(|x| x == self.last_y_hline) {
                        self.result = EntryOf::Ok(SpriteSerializationFunc::Serialize);
                        ctrl.end_analysis();
                    }
                }
            }
            _ => (),
        }
    }
}
impl<'a, 'e, E: ExecutionState<'e>> SpriteSerializationAnalysis<'a, 'e, E>
{
    fn is_stack_temp_hlines(&self, ctx: OperandCtx<'e>, addr: Operand<'e>) -> bool {
        collect_arith_add_terms(addr, self.bump)
            .as_mut()
            .map(|terms| {
                let ok = terms.remove_one(|op, _neg| op == ctx.register(4));
                if !ok {
                    return false;
                }
                terms.remove_one(|op, _neg| {
                    op.if_arithmetic_mul_const(4) == Some(self.map_height_tiles)
                })
            })
            .unwrap_or(false)
    }
}
