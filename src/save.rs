use scarf::{Operand, Operation, DestOperand, Rva};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::add_terms::collect_arith_add_terms;
use crate::{
    ArgCache, Analysis, single_result_assign, entry_of_until, EntryOf,
    find_functions_using_global,
};

#[derive(Clone)]
pub struct SpriteSerialization<Va: VirtualAddress> {
    pub serialize_sprites: Option<Va>,
    pub deserialize_sprites: Option<Va>,
}

pub fn sprite_serialization<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> SpriteSerialization<E::VirtualAddress> {
    // Find de/serialization functions by checking for
    // sprite_hlines_end[x] = deserialize_sprite_ptr(sprite_hlines_end[x])
    // => sprite_hlines_end[x] = sprite_array + (sprite_hlines_end[x] - 1) * struct_size
    // (Serialization converts them back and forth in place)
    let mut result = SpriteSerialization {
        serialize_sprites: None,
        deserialize_sprites: None,
    };
    let sprites = analysis.sprites();
    let sprite_hlines_end = match sprites.sprite_hlines_end {
        Some(s) => s,
        None => return result,
    };
    let (sprite_array, sprite_size) = match analysis.sprite_array() {
        Some(s) => s,
        None => return result,
    };
    let init_sprites = match analysis.init_sprites() {
        Some(s) => s,
        None => return result,
    };
    let game = match analysis.game() {
        Some(s) => s,
        None => return result,
    };

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let functions = analysis.functions();

    let sprite_array_address = sprite_array.if_constant()
        .or_else(|| sprite_array.if_memory()?.address.if_constant());
    let sprite_array_address = match sprite_array_address {
        Some(s) => E::VirtualAddress::from_u64(s),
        None => return result,
    };
    let mut globals = find_functions_using_global(analysis, sprite_array_address);
    globals.sort_by_key(|x| x.func_entry);
    globals.dedup_by_key(|x| x.func_entry);
    let mut checked = Vec::with_capacity(globals.len());
    checked.push(Rva((init_sprites.as_u64() - binary.base.as_u64()) as u32));
    let map_height_tiles = ctx.mem16(ctx.add_const(game, 0xe6));
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
            Operation::Move(DestOperand::Memory(mem), value, None) => {
                let value = ctrl.resolve(value);
                let dest = ctrl.resolve(mem.address);
                if dest == self.last_y_hline {
                    if let Some(mut terms) = collect_arith_add_terms(value) {
                        let ok = terms.remove_one(|op, _neg| {
                            op.if_arithmetic_mul()
                                .filter(|(_, r)| {
                                    r.if_constant().filter(|&c| c == self.sprite_size as u64)
                                        .is_some()
                                })
                                .filter(|&(l, _)| {
                                    // addr == self.last_y_hline or undefined; convert in place
                                    // in older patches,
                                    // [esp - x + game.map_height_tiles] in newer.
                                    l.is_undefined() ||
                                        ctrl.if_mem_word(l)
                                            .filter(|&addr| {
                                                self.is_stack_temp_hlines(addr) ||
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
                } else if !self.had_file_call && self.is_stack_temp_hlines(dest) {
                    if value.iter().any(|x| x == self.last_y_hline) {
                        self.result = EntryOf::Ok(SpriteSerializationFunc::Serialize);
                    }
                }
            }
            _ => (),
        }
    }
}
impl<'a, 'e, E: ExecutionState<'e>> SpriteSerializationAnalysis<'a, 'e, E>
{
    fn is_stack_temp_hlines(&self, addr: Operand<'e>) -> bool {
        collect_arith_add_terms(addr)
            .as_mut()
            .map(|terms| {
                let ok = terms.remove_one(|op, _neg| {
                    // rsp
                    op.if_register()
                        .filter(|x| x.0 == 4)
                        .is_some()
                });
                if !ok {
                    return false;
                }
                terms.remove_one(|op, _neg| {
                    op.if_arithmetic_mul()
                        .filter(|x| x.1.if_constant() == Some(4))
                        .filter(|x| x.0 == self.map_height_tiles)
                        .is_some()
                })
            })
            .unwrap_or(false)
    }
}
