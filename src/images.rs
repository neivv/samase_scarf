use scarf::{DestOperand, Operand, Operation, MemAccess};
use scarf::analysis::{self, Control, FuncAnalysis};
use scarf::exec_state::{ExecutionState};

use scarf::exec_state::VirtualAddress as VirtualAddressTrait;

use crate::analysis::{AnalysisCtx};
use crate::analysis_find::{EntryOf, FunctionFinder, entry_of_until};
use crate::util::{
    MemAccessExt, single_result_assign, ControlExt, is_global, ExecStateExt,
};

pub(crate) struct InitImages<'e, Va: VirtualAddressTrait> {
    pub init_images: Option<Va>,
    pub images: Option<Operand<'e>>,
    pub hp_bar_images: Option<Operand<'e>>,
    pub hp_bar_state: Option<Operand<'e>>,
    pub selection_circles: Option<Operand<'e>>,
    pub placement_images: Option<Operand<'e>>,
    pub placement_rects: Option<Operand<'e>>,
    pub first_free_hp_bar: Option<Operand<'e>>,
    pub last_free_hp_bar: Option<Operand<'e>>,
    pub first_free_placement_image: Option<Operand<'e>>,
    pub last_free_placement_image: Option<Operand<'e>>,
    pub first_free_placement_rect: Option<Operand<'e>>,
    pub last_free_placement_rect: Option<Operand<'e>>,
}

pub(crate) fn init_images<'e, E: ExecutionState<'e>>(
    actx: &AnalysisCtx<'e, E>,
    first_free_selection_circle: Operand<'e>,
    functions: &FunctionFinder<'_, 'e, E>,
) -> InitImages<'e, E::VirtualAddress> {
    let binary = actx.binary;
    let ctx = actx.ctx;

    let mut result = InitImages {
        init_images: None,
        images: None,
        hp_bar_images: None,
        hp_bar_state: None,
        selection_circles: None,
        placement_images: None,
        placement_rects: None,
        first_free_hp_bar: None,
        last_free_hp_bar: None,
        first_free_placement_image: None,
        last_free_placement_image: None,
        first_free_placement_rect: None,
        last_free_placement_rect: None,
    };

    let selection_circle_addr = first_free_selection_circle.if_memory()
        .and_then(|x| x.if_constant_address())
        .map(|x| E::VirtualAddress::from_u64(x));
    let selection_circle_addr = match selection_circle_addr {
        Some(s) => s,
        None => return result,
    };
    let funcs = functions.functions();
    let mut global_refs = functions.find_functions_using_global(actx, selection_circle_addr);
    global_refs.sort_unstable_by_key(|x| x.func_entry);
    global_refs.dedup_by_key(|x| x.func_entry);

    for global in global_refs {
        let ok = entry_of_until(binary, funcs, global.use_address, |entry| {
            let mut analyzer = InitImagesAnalyzer::<E> {
                result: &mut result,
                inline_depth: 0,
                state: InitImagesState::Arrays,
                list_stores: [[None; 2]; 3],
            };
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            if result.images.is_some() {
                result.init_images = Some(entry);
                EntryOf::Ok(())
            } else {
                EntryOf::Retry
            }
        }).is_ok();
        if ok {
            break;
        }
    }

    result
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum InitImagesState {
    /// Find memsets to arrays. Since placement image arrays are same size,
    /// assume first to be placement images.
    Arrays,
    /// Find write of hp_bar_images[0].sprite = &hp_bar_state[0]
    /// Inline once if function takes thiscall arg1 = 0
    HpBarState,
    /// Linked lists are initialized by first setting first/last to index 0,
    /// and then looping through rest of them using a function different from
    /// usual linked list adds
    /// insert_2nd(this = &array[0], a1 = entry, a2 = &last_ptr)
    LinkedLists,
}

struct InitImagesAnalyzer<'a, 'e, E: ExecutionState<'e>> {
    result: &'a mut InitImages<'e, E::VirtualAddress>,
    inline_depth: u8,
    state: InitImagesState,
    /// Store list head/tail until able to determine which one is which
    /// for hp bars / placement images / placement rects
    list_stores: [[Option<MemAccess<'e>>; 2]; 3],
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for InitImagesAnalyzer<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        match self.state {
            InitImagesState::Arrays => {
                match *op {
                    Operation::Jump { .. } => {
                        ctrl.end_analysis();
                    }
                    Operation::Call(..) => {
                        let arg1 = ctrl.resolve_arg(0);
                        let arg2 = ctrl.resolve_arg(1);
                        let arg3 = ctrl.resolve_arg(2);
                        if arg2 != ctx.const_0() || !is_global(arg1) {
                            return;
                        }
                        let result = if let Some(c) = arg3.if_constant() {
                            let image_size = E::struct_layouts().image_size();
                            if c == image_size * 0xc {
                                &mut self.result.hp_bar_images
                            } else if c == image_size * 0x50 {
                                &mut self.result.selection_circles
                            } else if c == image_size * 0x40 {
                                if self.result.placement_images.is_none() {
                                    &mut self.result.placement_images
                                } else {
                                    &mut self.result.placement_rects
                                }
                            } else if c == image_size * 5000 {
                                // image array before ext limits
                                &mut self.result.images
                            } else {
                                return;
                            }
                        } else if E::struct_layouts().if_mul_image_size(arg3).is_some() {
                            &mut self.result.images
                        } else {
                            return;
                        };
                        single_result_assign(Some(arg1), result);
                        if self.result.placement_rects.is_some() {
                            self.state = InitImagesState::HpBarState;
                        }
                    }
                    _ => (),
                }
            }
            InitImagesState::HpBarState => {
                if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if mem.size == E::WORD_SIZE {
                        let mem = ctrl.resolve_mem(mem);
                        if mem.is_global() {
                            let value = ctrl.resolve(value);
                            let grp_offset = E::struct_layouts().image_grp();
                            if let Some(hp_bars) = self.result.hp_bar_images {
                                let cmp_mem = ctx.mem_access(hp_bars, grp_offset, E::WORD_SIZE);
                                if mem == cmp_mem {
                                    self.result.hp_bar_state = Some(value);
                                    self.state = InitImagesState::LinkedLists;
                                    if self.inline_depth != 0 {
                                        ctrl.end_analysis();
                                    }
                                } else {
                                    self.check_list_store(ctrl, &mem, value);
                                }
                            }
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if self.inline_depth == 0 {
                        let arg0 = ctrl.resolve_arg_thiscall_u8(0);
                        if arg0 == ctx.const_0() {
                            if let Some(dest) = ctrl.resolve_va(dest) {
                                self.inline_depth = 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth = 0;
                            }
                        }
                    }
                }
            }
            InitImagesState::LinkedLists => {
                if let Operation::Move(DestOperand::Memory(ref mem), value) = *op {
                    if mem.size == E::WORD_SIZE {
                        let mem = ctrl.resolve_mem(mem);
                        if mem.is_global() {
                            let value = ctrl.resolve(value);
                            self.check_list_store(ctrl, &mem, value);
                        }
                    }
                } else if let Operation::Call(dest) = *op {
                    if self.inline_depth == 0 {
                        let this = ctrl.resolve_register(1);
                        let inline = (Some(this) == self.result.hp_bar_images &&
                            self.result.first_free_hp_bar.is_none()) ||
                                (Some(this) == self.result.placement_images &&
                                self.result.first_free_placement_image.is_none()) ||
                                (Some(this) == self.result.placement_rects &&
                                self.result.first_free_placement_rect.is_none());
                        if inline {
                            if let Some(dest) = ctrl.resolve_va(dest) {
                                self.inline_depth = 1;
                                ctrl.analyze_with_current_state(self, dest);
                                self.inline_depth = 0;
                            }
                        }
                    }
                }
            }
        }
    }
}

impl<'a, 'e, E: ExecutionState<'e>> InitImagesAnalyzer<'a, 'e, E> {
    fn check_list_store(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        mem: &MemAccess<'e>,
        value: Operand<'e>,
    ) {
        'init_head_tail: {
            let result = &mut self.result;
            let index = match () {
                () if Some(value) == result.hp_bar_images => 0,
                () if Some(value) == result.placement_images => 1,
                () if Some(value) == result.placement_rects => 2,
                _ => break 'init_head_tail,
            };
            let store = &mut self.list_stores[index];
            if store[0].is_none() {
                store[0] = Some(*mem);
            } else if store[0] != Some(*mem) {
                store[1] = Some(*mem);
            }
            return;
        }
        'entry1_to_tail: {
            let ctx = ctrl.ctx();
            let value_prev = ctx.sub_const(value, E::struct_layouts().image_size());
            let result = &mut self.result;
            let (index, result_first, result_last) = match () {
                () if Some(value_prev) == result.hp_bar_images => {
                    (0, &mut result.first_free_hp_bar, &mut result.last_free_hp_bar)
                }
                () if Some(value_prev) == result.placement_images => {
                    (1, &mut result.first_free_placement_image,
                        &mut result.last_free_placement_image)
                }
                () if Some(value_prev) == result.placement_rects => {
                    (2, &mut result.first_free_placement_rect,
                        &mut result.last_free_placement_rect)
                }
                _ => break 'entry1_to_tail,
            };
            if let [Some(a), Some(b)] = self.list_stores[index] {
                let (first, last) = if a == *mem {
                    (b, a)
                } else if b == *mem {
                    (a, b)
                } else {
                    break 'entry1_to_tail;
                };
                *result_first = Some(ctx.memory(&first));
                *result_last = Some(ctx.memory(&last));
                if self.inline_depth != 0 {
                    ctrl.end_analysis();
                }
            }
            return;
        }
    }
}
