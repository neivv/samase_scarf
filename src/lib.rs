#![allow(clippy::style, clippy::filter_next, clippy::identity_op,
    clippy::trivially_copy_pass_by_ref, clippy::nonminimal_bool)]

#[macro_use] extern crate log;

#[cfg(not(feature = "test_assertions"))]
macro_rules! test_assert_eq {
    ($($toks:tt)*) => {}
}

#[cfg(feature = "test_assertions")]
macro_rules! test_assert_eq {
    ($($toks:tt)*) => {
        assert_eq!($($toks)*)
    }
}

mod add_terms;
mod ai;
mod analysis;
mod analysis_find;
mod analysis_state;
mod bullets;
mod call_tracker;
mod campaign;
mod clientside;
mod commands;
mod crt;
mod detect_tail_call;
mod dialog;
mod eud;
mod file;
mod firegraft;
mod float_cmp;
mod game;
mod game_init;
mod hash_map;
mod inline_hook;
mod iscript;
mod linked_list;
mod map;
mod minimap;
mod network;
mod pathing;
mod players;
mod range_list;
mod renderer;
mod requirements;
mod rng;
mod save;
mod sound;
mod step_order;
mod storm;
mod struct_layouts;
mod sprites;
mod switch;
mod text;
mod units;
mod unresolve;
mod util;
mod vtables;
mod x86_64_globals;
mod x86_64_instruction_info;
mod x86_64_unwind;

pub mod dat;

#[cfg(any(feature = "test_assertions", feature = "binaries_32", feature = "binaries_64"))]
pub mod dump;

pub use scarf;
pub use scarf::{BinarySection};

pub use crate::analysis::{
    AddressAnalysis, Analysis, DatType, DatPatchesDebug, FiregraftAddresses, OperandAnalysis,
    Patch,
};

pub use crate::ai::AiScriptHook;
pub use crate::dat::{
    DatTablePtr, DatPatch, DatPatches, DatArrayPatch, DatEntryCountPatch, DatReplaceFunc,
};
pub use crate::eud::{Eud, EudTable};
pub use crate::firegraft::RequirementTables;
pub use crate::game::{Limits};
pub use crate::inline_hook::InlineHookState;
pub use crate::iscript::StepIscriptHook;
pub use crate::network::{SnpDefinitions};
pub use crate::renderer::{PrismShaders};
pub use crate::step_order::{SecondaryOrderHook, StepOrderHiddenHook};
pub use crate::util::test_assertions;
