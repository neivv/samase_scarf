use std::rc::Rc;

use scarf::{DestOperand, Operand, Operation};
use scarf::analysis::{self, Control, FuncAnalysis};

use scarf::exec_state::{ExecutionState, VirtualAddress};

use crate::{Analysis, OptionExt};

pub struct MapTileFlags<Va: VirtualAddress> {
    pub map_tile_flags: Option<Rc<Operand>>,
    pub update_visibility_point: Option<Va>,
}

pub fn map_tile_flags<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
) -> MapTileFlags<E::VirtualAddress> {
    struct Analyzer<'a, 'b, 'c, F: ExecutionState<'b>> {
        result: &'c mut MapTileFlags<F::VirtualAddress>,
        analysis: &'a mut Analysis<'b, F>,
    }
    impl<'a, 'b, 'c, F: ExecutionState<'b>> scarf::Analyzer<'b> for Analyzer<'a, 'b, 'c, F> {
        type State = analysis::DefaultState;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'b, '_, '_, Self>, op: &Operation) {
            match op {
                Operation::Call(dest) => {
                    // order_nuke_track calls update_visibility_point([unit + 0xd0])
                    // But it also calls set_sprite_elevation, so the first match
                    // isn't necessarily correct
                    let ctx = ctrl.ctx();
                    let arg_this = ctrl.resolve(ctx.register_ref(1));
                    let ok = arg_this.if_mem32()
                        .and_then(|x| x.if_arithmetic_add())
                        .and_either(|x| x.if_constant().filter(|&c| c == 0xd0))
                        .is_some();
                    if ok {
                        if let Some(dest) = ctrl.resolve(&dest).if_constant() {
                            let result = tile_flags_from_update_visibility_point(
                                self.analysis,
                                F::VirtualAddress::from_u64(dest),
                            );
                            if let Some(result) = result {
                                self.result.map_tile_flags = Some(result);
                                self.result.update_visibility_point =
                                    Some(F::VirtualAddress::from_u64(dest));
                                ctrl.end_analysis();
                            }
                        }
                    }
                }
                Operation::Move(dest, _, _) => {
                    // Ignore moves to [unit + 0xd0]
                    if let DestOperand::Memory(mem) = dest {
                        let addr = ctrl.resolve(&mem.address);
                        let skip = addr.if_arithmetic_add()
                            .and_either(|x| x.if_constant().filter(|&c| c == 0xd0))
                            .is_some();
                        if skip {
                            ctrl.skip_operation();
                        }
                    }
                }
                _ => (),
            }
        }
    }

    let binary = analysis.binary;
    let ctx = analysis.ctx;
    let mut result = MapTileFlags {
        map_tile_flags: None,
        update_visibility_point: None,
    };
    let order_nuke_track = match crate::step_order::find_order_nuke_track(analysis) {
        Some(s) => s,
        None => return result,
    };

    let mut analyzer = Analyzer {
        result: &mut result,
        analysis,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, order_nuke_track);
    analysis.analyze(&mut analyzer);
    result
}

fn tile_flags_from_update_visibility_point<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    addr: E::VirtualAddress,
) -> Option<Rc<Operand>> {
    struct Analyzer<'f, F: ExecutionState<'f>> {
        result: Option<Rc<Operand>>,
        phantom: std::marker::PhantomData<(*const F, &'f ())>,
    }
    impl<'f, F: ExecutionState<'f>> scarf::Analyzer<'f> for Analyzer<'f, F> {
        type State = analysis::DefaultState;
        type Exec = F;
        fn operation(&mut self, ctrl: &mut Control<'f, '_, '_, Self>, op: &Operation) {
            match op {
                Operation::Move(_, from, None) => {
                    let from = ctrl.resolve(from);
                    // Check for mem_any[map_tile_flags + 4 * (x + y * map_width)]
                    let result = from.if_memory()
                        .and_then(|x| x.address.if_arithmetic_add())
                        .and_then(|(l, r)| Operand::either(l, r, |x| {
                            x.if_arithmetic_mul()
                                .and_then(|(l, r)| Operand::either(l, r, |x| x.if_constant()))
                                .filter(|&(c, _)| c == 4)
                                .and_then(|(_, other)| other.if_arithmetic_add())
                        }))
                        .map(|(_, map_tile_flags)| map_tile_flags);
                    if let Some(result) = result {
                        self.result = Some(result.clone());
                        ctrl.end_analysis();
                    }
                }
                _ => (),
            }
        }
    }

    let mut analyzer = Analyzer::<E> {
        result: None,
        phantom: Default::default(),
    };

    let mut analysis = FuncAnalysis::new(analysis.binary, analysis.ctx, addr);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

