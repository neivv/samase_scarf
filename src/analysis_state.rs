//! Using only single custom `scarf::analysis::AnalysisState` across all analyzers of
//! this library to keep monomorphization duplication lower.
//!
//! Single analysis is only supposed to use single state in `StateEnum`.

use bumpalo::Bump;
use bumpalo::boxed::Box as BumpBox;
use scarf::Operand;

pub struct AnalysisState<'acx, 'e: 'acx> {
    state: BumpBox<'acx, StateEnum<'e>>,
    bump: &'acx Bump,
}

// Hopefully this can be kept Copy for memcpy-only copying and not having to be concerned
// with destructors.
#[derive(Copy, Clone)]
pub enum StateEnum<'e> {
    AiTown(AiTownState),
    GiveAi(GiveAiState),
    TrainMilitary(TrainMilitaryState),
    ScMain(ScMainAnalyzerState),
    InitMapFromPath(IsInitMapFromPathState),
    FindChooseSnp(FindChooseSnpState<'e>),
    SpStart(SinglePlayerStartState),
    SelectMapEntry(MapEntryState),
    LoadImages(LoadImagesAnalysisState),
    MiscClientSide(MiscClientSideAnalyzerState),
    Eud(EudState),
    CreateBullet(FindCreateBulletState),
    Tooltip(TooltipState<'e>),
    GluCmpgn(GluCmpgnState),
    LocalPlayerId(LocalPlayerState),
    StepOrder(StepOrderState),
    ReplayVisions(ReplayVisionsState),
    IsReplay(IsReplayState<'e>),
    StepNetwork(StepNetworkState),
    FontCacheRenderAscii(FindCacheRenderAsciiState),
    IsFontCacheRenderAscii(IsCacheRenderAsciiState),
    HandleTargetedClick(HandleTargetedClickState),
}

impl<'acx, 'e: 'acx> AnalysisState<'acx, 'e> {
    pub fn new(bump: &'acx Bump, state: StateEnum<'e>) -> AnalysisState<'acx, 'e> {
        AnalysisState {
            state: BumpBox::new_in(state, bump),
            bump,
        }
    }

    pub fn get<S: SubState<'e>>(&mut self) -> &mut S {
        match S::get_sub(&mut self.state) {
            Some(s) => s,
            None => panic!("Inconsistent AnalysisState use"),
        }
    }

    #[inline]
    pub fn set<S: SubState<'e>>(&mut self, value: S) {
        S::set_sub(&mut self.state, value)
    }
}

impl<'acx, 'e> Clone for AnalysisState<'acx, 'e> {
    fn clone(&self) -> Self {
        Self {
            state: BumpBox::new_in(self.state.clone(), self.bump),
            bump: self.bump,
        }
    }
}

pub trait SubState<'e> {
    fn get_sub<'a>(state: &'a mut StateEnum<'e>) -> Option<&'a mut Self>;
    fn set_sub(state: &mut StateEnum<'e>, value: Self);
}

macro_rules! states {
    ($($var:ident($t:ty),)*) => {
        $(
            impl<'e> SubState<'e> for $t {
                fn get_sub<'a>(state: &'a mut StateEnum<'e>) -> Option<&'a mut Self> {
                    match state {
                        StateEnum::$var(x) => Some(x),
                        _ => None,
                    }
                }

                #[inline]
                fn set_sub(state: &mut StateEnum<'e>, value: Self) {
                    *state = StateEnum::$var(value);
                }
            }
        )*

        impl<'acx, 'e> scarf::analysis::AnalysisState for AnalysisState<'acx, 'e> {
            fn merge(&mut self, mut new: Self) {
                let new = &mut *new.state;
                match *self.state {
                    $(
                        StateEnum::$var(ref mut old) => {
                            if let StateEnum::$var(new) = new {
                                old.merge(new);
                            }
                        }
                    )*
                }
            }
        }
    };
}

states! {
    AiTown(AiTownState),
    GiveAi(GiveAiState),
    TrainMilitary(TrainMilitaryState),
    ScMain(ScMainAnalyzerState),
    InitMapFromPath(IsInitMapFromPathState),
    FindChooseSnp(FindChooseSnpState<'e>),
    SpStart(SinglePlayerStartState),
    SelectMapEntry(MapEntryState),
    LoadImages(LoadImagesAnalysisState),
    MiscClientSide(MiscClientSideAnalyzerState),
    Eud(EudState),
    CreateBullet(FindCreateBulletState),
    Tooltip(TooltipState<'e>),
    GluCmpgn(GluCmpgnState),
    LocalPlayerId(LocalPlayerState),
    StepOrder(StepOrderState),
    ReplayVisions(ReplayVisionsState),
    IsReplay(IsReplayState<'e>),
    StepNetwork(StepNetworkState),
    FontCacheRenderAscii(FindCacheRenderAsciiState),
    IsFontCacheRenderAscii(IsCacheRenderAsciiState),
    HandleTargetedClick(HandleTargetedClickState),
}

#[derive(Clone, Copy)]
pub struct AiTownState {
    pub jump_count: u32,
}

impl AiTownState {
    fn merge(&mut self, new: &AiTownState) {
        self.jump_count = self.jump_count.max(new.jump_count);
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum GiveAiState {
    // At inline depth 0 or 1, there's a switch jump checking trigegr.current_player.
    // Follow default case.
    SearchingSwitchJump,
    // Search for call to map_create_unit
    SearchingMapCreateUnit,
    // Wait for check against units_dat_group_flags[id]
    SearchingRaceCheck,
    // Search for GiveAi
    RaceCheckSeen,
    Stop,
}

impl GiveAiState {
    fn merge(&mut self, new: &GiveAiState) {
        if *self != *new {
            if matches!(*self, GiveAiState::SearchingRaceCheck | GiveAiState::RaceCheckSeen) &&
                matches!(*new, GiveAiState::SearchingRaceCheck | GiveAiState::RaceCheckSeen)
            {
                *self = GiveAiState::RaceCheckSeen;
            } else {
                *self = GiveAiState::Stop;
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct TrainMilitaryState {
    pub seconds_checked: bool,
}

impl TrainMilitaryState {
    fn merge(&mut self, new: &Self) {
        self.seconds_checked = new.seconds_checked && self.seconds_checked;
    }
}

#[allow(bad_style)]
#[derive(Copy, Clone, Eq, PartialEq, Debug, Ord, PartialOrd)]
pub enum ScMainAnalyzerState {
    SearchingEntryHook,
    SearchingGameLoop,
    SwitchJumped(u8),
}

impl ScMainAnalyzerState {
    fn merge(&mut self, newer: &Self) {
        if *self < *newer {
            *self = *newer;
        }
    }
}

#[derive(Default, Copy, Clone)]
pub struct IsInitMapFromPathState {
    pub jump_count: u8,
    pub is_after_arg3_check: bool,
}

impl IsInitMapFromPathState {
    fn merge(&mut self, newer: &Self) {
        self.jump_count = newer.jump_count.min(self.jump_count);
        self.is_after_arg3_check = self.is_after_arg3_check & newer.is_after_arg3_check;
    }
}

#[derive(Copy, Clone)]
pub struct FindChooseSnpState<'e> {
    pub provider_id_offset: Option<Operand<'e>>,
}

impl<'e> FindChooseSnpState<'e> {
    fn merge(&mut self, newer: &Self) {
        if self.provider_id_offset != newer.provider_id_offset {
            self.provider_id_offset = None;
        }
    }
}

/// These are ordered from first step to last
#[derive(Ord, Eq, PartialEq, PartialOrd, Copy, Clone)]
pub enum SinglePlayerStartState {
    // calls Storm#101(addr, "", "", 0, 0, 0, u8[x], "", &mut local_storm_player_id)
    SearchingStorm101,
    // Does
    //  net_player_to_game(*)[local_storm_player_id] = local_player_id
    //  net_player_to_unique(*)[local_storm_player_id] = local_unique_player_id(*)
    //  memcpy(&mut game_data(*), arg1)
    // finds ones marked(*), inlining is necessary.
    AssigningPlayerMappings,
    // Does memcpy(&mut player_skins[local_storm_player_id], &skins.active_skins)
    FindingSkins,
}

impl SinglePlayerStartState {
    fn merge(&mut self, newer: &Self) {
        if *self < *newer {
            *self = *newer;
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum MapEntryState {
    Unknown,
    Map,
    Save,
    Replay,
}

impl MapEntryState {
    fn merge(&mut self, newer: &Self) {
        if *self != *newer {
            *self = MapEntryState::Unknown;
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum LoadImagesAnalysisState {
    // Move forward until past load_dat call
    BeforeLoadDat,
    // Finds open_anim_single_file(this = &base_anim_set[1], 0, 1, 1)
    // open_anim_multi_file(this = &base_anim_set[0], 0, 999, 1, 2, 1)
    // Inline to 1 depth load_images_aux, stop inlining if first there call
    // isn't func(_, "arr\\images.tbl", _, _, _)
    // + Start keeping track of func return values, don't inline other than load_images_aux
    FindOpenAnims,
    // Expected to be first call after open_anim_multi_file, recognized from "/skins" const str
    // access
    FindInitSkins,
    // add_asset_change_cb(&mut out_handle, func (0x14 bytes by value))
    // func.x4 (arg3) is anim_asset_change_cb
    FindAssetChangeCb,
    // load_grps(image_grps, images_dat_grp, &mut out, 999)
    // Single caller so some build may inline this??
    // Currently not handling that.
    FindImageGrps,
    // load_lo_set(&image_overlays[0], images_dat_attack_overlay, &mut out, 999)
    FindImageOverlays,
    // Stop inlining if inline depth == 1 (since FindOpenAnims)
    // Find move Mem8[x + undef] = x * 2
    FindFireOverlayMax,
}

impl LoadImagesAnalysisState {
    fn merge(&mut self, newer: &Self) {
        let newer = *newer;
        // Merge most to smallest state possible,
        // but there's code that skips past add_asset_change_cb so have an exception
        // to merge that to a higher state.
        if *self == LoadImagesAnalysisState::FindImageGrps &&
            newer == LoadImagesAnalysisState::FindAssetChangeCb
        {
            // Nothing
        } else if newer == LoadImagesAnalysisState::FindImageGrps &&
            *self == LoadImagesAnalysisState::FindAssetChangeCb
        {
            *self = newer;
        } else if *self > newer {
            *self = newer;
        }
    }
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum MiscClientSideAnalyzerState {
    // Checking for this.vtable_fn() == 0
    Begin,
    // Checking for multiplayer == 0
    OnVtableFnZeroBranch,
    // Checking for is_paused if not found yet, once it is checking
    // for scmain_state == 3
    MultiplayerZeroBranch,
    // Checking for is_placing_building == 0
    ScMainStateThreeBranch,
    // Checking for is_targeting == 0
    IsPlacingBuildingFound,
    End,
}

impl MiscClientSideAnalyzerState {
    fn merge(&mut self, newer: &Self) {
        use MiscClientSideAnalyzerState::*;
        let (low, high) = match *self < *newer {
            true => (*self, *newer),
            false => (*newer, *self),
        };
        match (low, high) {
            (a, b) if a == b => (),
            // When leaving the `this.vtable_fn() == 0` branch and
            // merging with `Begin`, merge to `End` (Nothing important to be found
            // after that)
            (Begin, _) => *self = End,
            // scmain_state == 3 branch is after `Multiplayer == 0` branch (searching pause game)
            // and its else branch join, so they merge to MultiplayerZeroBranch to
            // keep analysis
            (OnVtableFnZeroBranch, MultiplayerZeroBranch) => *self = high,
            // Otherwise merge to `End`
            (OnVtableFnZeroBranch, _) => *self = End,
            // However, rest of the checks are all inside scmain_state == 3, so
            // MultiplayerZeroBranch joining with higher state means end
            (MultiplayerZeroBranch, _) => *self = End,
            // is_placing_building == 0 also joins with else branch before is_targeting == 0
            // check.
            (ScMainStateThreeBranch, IsPlacingBuildingFound) => *self = high,
            (ScMainStateThreeBranch, _) => *self = End,
            (IsPlacingBuildingFound, _) => *self = End,
            (End, _) => *self = End,
        }
    }
}

#[derive(Clone, Copy)]
pub struct EudState {
    pub in_wanted_branch: bool,
    pub wanted_branch_start: u32,
}

impl EudState {
    fn merge(&mut self, newer: &Self) {
        self.in_wanted_branch |= newer.in_wanted_branch;
        if self.wanted_branch_start != 0 {
            self.wanted_branch_start = newer.wanted_branch_start;
        }
    }
}

#[derive(Copy, Clone)]
pub struct FindCreateBulletState {
    pub calls_seen: u32,
}

impl FindCreateBulletState {
    fn merge(&mut self, newer: &FindCreateBulletState) {
        self.calls_seen = self.calls_seen.max(newer.calls_seen);
    }
}

#[derive(Clone, Copy)]
pub enum TooltipState<'e> {
    FindEventHandler,
    FindTooltipCtrl(FindTooltipCtrlState<'e>),
    FindLayoutText,
}

// set_tooltip function writes the following variables:
//   current_tooltip_ctrl = ctrl (undef for this analysis)
//   tooltip_draw_func = func
//   graphic_layers[1].enable = 1
//   graphic_layers[1].func = func
//   (And some zeroes and width/height to layer 1 as well)
#[derive(Clone, Eq, PartialEq, Copy)]
pub struct FindTooltipCtrlState<'e> {
    pub tooltip_ctrl: Option<Operand<'e>>,
    pub one: Option<Operand<'e>>,
    pub func1: Option<(Operand<'e>, u64)>,
    pub func2: Option<(Operand<'e>, u64)>,
}

impl<'e> TooltipState<'e> {
    fn merge(&mut self, newer: &Self) {
        use self::TooltipState::*;
        match (self, newer) {
            (&mut FindTooltipCtrl(ref mut a), &FindTooltipCtrl(ref b)) => {
                if a != b {
                    *a = FindTooltipCtrlState {
                        tooltip_ctrl: None,
                        one: None,
                        func1: None,
                        func2: None,
                    }
                }
            }
            (_, _) => (),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct GluCmpgnState {
    pub dialog_return_stored: bool,
}

impl GluCmpgnState {
    fn merge(&mut self, newer: &Self) {
        self.dialog_return_stored |= newer.dialog_return_stored;
    }
}

#[derive(Copy, Clone)]
pub enum LocalPlayerState {
    Start,
    PlayerFieldAccessSeen,
}

impl LocalPlayerState {
    fn merge(&mut self, newer: &Self) {
        if let LocalPlayerState::PlayerFieldAccessSeen = *newer {
            *self = *newer;
        }
    }
}

#[derive(Eq, Copy, Clone, PartialEq)]
pub enum StepOrderState {
    HasSwitchJumped,
    NotSwitchJumped,
}

impl StepOrderState {
    fn merge(&mut self, newer: &Self) {
        if *newer == StepOrderState::NotSwitchJumped {
            *self = *newer;
        }
    }
}

#[derive(Copy, Clone)]
pub struct ReplayVisionsState {
    pub visibility_mask_comparision: u8,
}

impl ReplayVisionsState {
    fn merge(&mut self, newer: &Self) {
        self.visibility_mask_comparision = newer.visibility_mask_comparision
            .min(self.visibility_mask_comparision);
    }
}

#[derive(Copy, Clone)]
pub struct IsReplayState<'e> {
    pub possible_result: Option<Operand<'e>>,
}

impl<'e> IsReplayState<'e> {
    fn merge(&mut self, newer: &Self) {
        if self.possible_result != newer.possible_result {
            self.possible_result = None;
        }
    }
}

#[derive(Copy, Clone)]
pub struct StepNetworkState {
    pub after_receive_storm_turns: bool,
}

impl StepNetworkState {
    fn merge(&mut self, newer: &Self) {
        self.after_receive_storm_turns |= newer.after_receive_storm_turns;
    }
}

#[derive(Copy, Clone)]
pub struct FindCacheRenderAsciiState {
    pub shadow_offset_seen: bool,
}

impl FindCacheRenderAsciiState {
    fn merge(&mut self, newer: &Self) {
        self.shadow_offset_seen |= newer.shadow_offset_seen;
    }
}

#[derive(Copy, Clone)]
pub struct IsCacheRenderAsciiState {
    pub last_ok_call: Option<u64>,
}

impl IsCacheRenderAsciiState {
    fn merge(&mut self, newer: &Self) {
        if self.last_ok_call != newer.last_ok_call {
            self.last_ok_call = None;
        }
    }
}

#[derive(Copy, Clone)]
pub struct HandleTargetedClickState {
    pub order_weapon_branch: Option<bool>,
    pub order_tech_branch: Option<bool>,
}

impl HandleTargetedClickState {
    fn merge(&mut self, newer: &Self) {
        if self.order_tech_branch != newer.order_tech_branch {
            self.order_tech_branch = None;
        }
        if self.order_weapon_branch != newer.order_weapon_branch {
            self.order_weapon_branch = None;
        }
    }
}
