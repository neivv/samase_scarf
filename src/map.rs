use std::rc::Rc;

use scarf::{DestOperand, Operand, OperandContext, Operation, VirtualAddress, ExecutionStateX86};
use scarf::analysis::{self, Control, FuncAnalysis};

use scarf::exec_state::{VirtualAddress as VirtualAddressTrait};

use crate::{Analysis, OptionExt};

#[derive(Default)]
pub struct MapTileFlags {
    pub map_tile_flags: Option<Rc<Operand>>,
    pub update_visibility_point: Option<VirtualAddress>,
}

pub fn map_tile_flags<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
    ctx: &OperandContext,
) -> MapTileFlags {
    struct Analyzer<'a, 'b, 'c> {
        result: &'c mut MapTileFlags,
        ctx: &'a OperandContext,
        analysis: &'a mut Analysis<'b, ExecutionStateX86<'b>>,
    }
    impl<'a, 'b, 'c> scarf::Analyzer<'a> for Analyzer<'a, 'b, 'c> {
        type State = analysis::DefaultState;
        type Exec = ExecutionStateX86<'a>;
        fn operation(&mut self, ctrl: &mut Control<'a, '_, '_, Self>, op: &Operation) {
            match op {
                Operation::Call(dest) => {
                    // order_nuke_track calls update_visibility_point([unit + 0xd0])
                    // But it also calls set_sprite_elevation, so the first match
                    // isn't necessarily correct
                    let arg_this = ctrl.resolve(&self.ctx.register(1));
                    let ok = arg_this.if_mem32()
                        .and_then(|x| x.if_arithmetic_add())
                        .and_either(|x| x.if_constant().filter(|&c| c == 0xd0))
                        .is_some();
                    if ok {
                        if let Some(dest) = ctrl.resolve(&dest).if_constant() {
                            let result = tile_flags_from_update_visibility_point(
                                self.analysis,
                                self.ctx,
                                VirtualAddress::from_u64(dest),
                            );
                            if let Some(result) = result {
                                self.result.map_tile_flags = Some(result);
                                self.result.update_visibility_point =
                                    Some(VirtualAddress::from_u64(dest));
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

    let mut result = MapTileFlags::default();
    let order_nuke_track = match crate::step_order::find_order_nuke_track(analysis, ctx) {
        Some(s) => s,
        None => return result,
    };

    let binary = analysis.binary;
    let mut analyzer = Analyzer {
        result: &mut result,
        ctx,
        analysis,
    };

    let mut analysis = FuncAnalysis::new(binary, ctx, order_nuke_track);
    analysis.analyze(&mut analyzer);
    result
}

fn tile_flags_from_update_visibility_point<'exec>(
    analysis: &mut Analysis<'exec, ExecutionStateX86<'exec>>,
    ctx: &OperandContext,
    addr: VirtualAddress,
) -> Option<Rc<Operand>> {
    struct Analyzer {
        result: Option<Rc<Operand>>,
    }
    impl<'exec> scarf::Analyzer<'exec> for Analyzer {
        type State = analysis::DefaultState;
        type Exec = ExecutionStateX86<'exec>;
        fn operation(&mut self, ctrl: &mut Control<'exec, '_, '_, Self>, op: &Operation) {
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

    let mut analyzer = Analyzer {
        result: None,
    };

    let mut analysis = FuncAnalysis::new(analysis.binary, ctx, addr);
    analysis.analyze(&mut analyzer);
    analyzer.result
}

