// Compile warnings out in release, but leave them for debug.
// Tests will also use them at some point to verify they don't regress.
//
// When enabled, warnings get to written to a DatWarnings struct that is stored
// in TLS for the current thread, valid for dat_patches call.
#[cfg(any(debug_assertions, feature = "test_assertions", feature = "binaries"))]
macro_rules! dat_warn {
    ($self:expr, $($rest:tt)*) => {
        crate::dat::add_warning_tls(
            file!(),
            line!(),
            format!($($rest)*),
        )
    }
}

#[cfg(not(any(debug_assertions, feature = "test_assertions", feature = "binaries")))]
macro_rules! dat_warn {
    ($self:expr, $($rest:tt)*) => {
        if false {
            let _ = format_args!($($rest)*);
        }
    }
}

mod campaign;
mod cmdbtns;
mod game;
mod partial_register_moves;
mod units;
mod stack_analysis;
mod sprites;
mod triggers;
mod util;
mod wireframe;

use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::hash::Hash;
use std::mem;
use std::rc::Rc;

use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump;
use byteorder::{ByteOrder, LittleEndian};
use lde::Isa;

use scarf::analysis::{self, Cfg, Control, FuncAnalysis, RelocValues};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{ArithOperand, ArithOpType, MemAccessSize, OperandType, OperandHashByAddress};
use scarf::{
    BinaryFile, BinarySection, DestOperand, FlagArith, FlagUpdate, Operand, OperandCtx,
    MemAccess, Operation, Rva
};

use crate::analysis::{AnalysisCache, AnalysisCtx, ArgCache, DatType};
use crate::analysis_find::{EntryOf, FunctionFinder, StringRefs, entry_of_until};
use crate::detect_tail_call::DetectTailCall;
use crate::hash_map::{HashMap, HashSet};
use crate::range_list::RangeList;
use crate::util::{
    bumpvec_with_capacity, single_result_assign, if_callable_const, ControlExt, OperandExt,
    ExecStateExt,
};
use crate::x86_64_unwind;

use partial_register_moves::PartialRegisterMoves;

static UNIT_ARRAY_WIDTHS: &[u8] = &[
    1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 2,
    2, 2, 2, 2, 4, 4, 8, 2, 2, 2, 2, 2, 1, 1, 1, 1,
    1, 2, 2, 2, 1, 2,
];

static WEAPON_ARRAY_WIDTHS: &[u8] = &[
    2, 4, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2,
    1, 1, 1, 1, 1, 1, 2, 2,
];

static FLINGY_ARRAY_WIDTHS: &[u8] = &[
    2, 4, 2, 4, 1, 1, 1,
];

static SPRITE_ARRAY_WIDTHS: &[u8] = &[
    2, 1, 1, 1, 1, 1,
];

static UPGRADE_ARRAY_WIDTHS: &[u8] = &[
    2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1,
];

static TECHDATA_ARRAY_WIDTHS: &[u8] = &[
    2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1,
];

static ORDER_ARRAY_WIDTHS: &[u8] = &[
    2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    2, 2, 1,
];

// Portdata label ints get converted to char * after loading
static PORTDATA_ARRAY_WIDTHS_32: &[u8] = &[
    4, 4, 1, 1, 1, 1,
];

static PORTDATA_ARRAY_WIDTHS_64: &[u8] = &[
    8, 8, 1, 1, 1, 1,
];

// Don't think mapdata labels do that, but same size changes
static MAPDATA_ARRAY_WIDTHS_32: &[u8] = &[
    4,
];

static MAPDATA_ARRAY_WIDTHS_64: &[u8] = &[
    8,
];

const RDTSC_CUSTOM: u32 = 0x2000_0000;
// One for each register 0x2000_0010 .. 0x2000_0020
const PARTIAL_REGISTER_CLEAR_CUSTOM: u32 = 0x2000_0010;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct DatTablePtr<'e> {
    pub address: Operand<'e>,
    pub entry_size: u32,
}

pub struct DatPatches<'e, Va: VirtualAddress> {
    pub patches: Vec<DatPatch<'e, Va>>,
    /// Bytes refered by hook/replace patches
    pub code_bytes: Vec<u8>,
    /// Offsets to `code_bytes` code which contain dat array constants.
    /// (offset, dat, field)
    /// On 64bit the constant is u32 are relative to exe base.
    /// (No instruction-changing patches will need to be applied to RIP-relative instructions,
    /// as they can't have a register index, so RIP-relative constants aren't relevant here)
    ///
    /// Guaranteed to be sorted by `offset`
    pub arrays_in_code_bytes: Vec<(usize, DatType, u8)>,
    pub set_status_screen_tooltip: Option<Va>,
    pub unit_wireframe_type: Option<Operand<'e>>,
    /// Vector<String> and point where it should be resized to have entries > 0x41
    pub campaign_map_names: Option<(Operand<'e>, Va)>,
    pub warnings: DatWarnings,
}

/// Type that contains any warnings found during dat analysis.
/// No-op in release builds when used as library.
/// The warnings get added to test compares (--dump-test-compares)
/// so they need to be active with feature = "test_assertions" and feature = "binaries"
#[cfg(not(any(debug_assertions, feature = "test_assertions", feature = "binaries")))]
pub struct DatWarnings;

#[cfg(not(any(debug_assertions, feature = "test_assertions", feature = "binaries")))]
impl DatWarnings {
    fn new() -> DatWarnings {
        DatWarnings
    }

    pub fn get_all(&self) -> &[(&'static str, u32, String)] {
        &[]
    }
}

#[cfg(any(debug_assertions, feature = "test_assertions", feature = "binaries"))]
pub struct DatWarnings(Vec<(&'static str, u32, String)>);

#[cfg(any(debug_assertions, feature = "test_assertions", feature = "binaries"))]
impl DatWarnings {
    fn new() -> DatWarnings {
        DatWarnings(vec![])
    }

    fn push(&mut self, file: &'static str, line: u32, msg: String) {
        // When used as library in debug mode, output to logger
        // Dump binary prints the warning to stdout (or file) anyway so don't duplicate it here.
        #[cfg(not(any(feature = "test_assertions", feature = "binaries")))]
        warn!("{}:{} {}", file, line, msg);
        self.0.push((file, line, msg));
    }

    pub fn get_all(&self) -> &[(&'static str, u32, String)] {
        &self.0
    }
}

#[cfg(not(any(debug_assertions, feature = "test_assertions", feature = "binaries")))]
#[inline(always)]
fn init_warnings_tls() {
}

#[cfg(not(any(debug_assertions, feature = "test_assertions", feature = "binaries")))]
#[inline(always)]
fn get_warnings_tls() -> DatWarnings {
    DatWarnings
}

#[cfg(any(debug_assertions, feature = "test_assertions", feature = "binaries"))]
fn init_warnings_tls() {
    WARNINGS.with(|w| *w.borrow_mut() = DatWarnings::new());
}

#[cfg(any(debug_assertions, feature = "test_assertions", feature = "binaries"))]
thread_local!(static WARNINGS: std::cell::RefCell<DatWarnings> =
    std::cell::RefCell::new(DatWarnings::new()));

#[cfg(any(debug_assertions, feature = "test_assertions", feature = "binaries"))]
fn get_warnings_tls() -> DatWarnings {
    WARNINGS.with(|w| {
        let mut w = w.borrow_mut();
        mem::replace(&mut *w, DatWarnings::new())
    })
}

#[cfg(any(debug_assertions, feature = "test_assertions", feature = "binaries"))]
fn add_warning_tls(file: &'static str, line: u32, msg: String) {
    WARNINGS.with(|w| w.borrow_mut().push(file, line, msg));
}

#[cfg(not(any(debug_assertions, feature = "test_assertions", feature = "binaries")))]
#[inline(always)]
fn format_stable_undef(_: Operand<'_>) -> String {
    String::new()
}

/// Replaces Undefined_num with just Undefined to make test compare outputs be stable.
/// (There is no guarantee that repeated runs result in same Undefined ids during memory
/// merge, as it iterates hashmaps using memory address as a hash key)
#[cfg(any(debug_assertions, feature = "test_assertions", feature = "binaries"))]
fn format_stable_undef(op: Operand<'_>) -> String {
    let mut text = op.to_string();
    if op.contains_undefined() {
        let mut pos = 0;
        let match_string = "Undefined";
        while let Some(undef_pos) = text[pos..].find(match_string) {
            let undef_pos = pos + undef_pos;
            let remove_start = undef_pos + match_string.len();
            let mut remove_end = remove_start + 1;
            while text[remove_end..].starts_with(|c: char| c.is_digit(16)) {
                remove_end += 1;
            }
            text.replace_range(remove_start..remove_end, "");
            pos = remove_start;
        }
    }
    text
}

impl<'e, Va: VirtualAddress> DatPatches<'e, Va> {
    fn empty() -> DatPatches<'e, Va> {
        DatPatches {
            patches: Vec::new(),
            code_bytes: Vec::new(),
            arrays_in_code_bytes: Vec::new(),
            set_status_screen_tooltip: None,
            unit_wireframe_type: None,
            campaign_map_names: None,
            warnings: DatWarnings::new(),
        }
    }
}

pub enum DatPatch<'e, Va: VirtualAddress> {
    Array(DatArrayPatch<Va>),
    EntryCount(DatEntryCountPatch<Va>),
    /// Address, index to code_bytes, patch length
    Replace(Va, u32, u8),
    /// Address to hook, index to code_bytes, hook length, bytes to skip over
    Hook(Va, u32, u8, u8),
    /// "Two step hooks" are used when an normal hook would break other jumps that jump
    /// to instructions that get overwritten by the long jump.
    /// These ones first do a short jump to a space which can contain the long jump
    /// instruction.
    /// The free space is some other point in the function (near enough for a short jump)
    /// which can contain two long jumps (Without any code jumping to that free space).
    /// The first long jump exists just to redirect execution that would normally execute
    /// those bytes, and the second one is the "second step" of the hook.
    ///
    /// Hook address, free space start, index to code_bytes, hook len, bytes to skip over
    TwoStepHook(Va, Va, u32, u8, u8),
    ReplaceFunc(Va, DatReplaceFunc),
    ExtendedArray(ExtArrayPatch<'e, Va>),
    /// Address, array ids (1-based)
    /// Expected to be on call instruction.
    ExtendedArrayArg(Va, [u8; 4]),
    GrpIndexHook(Va),
    GrpTextureHook(GrpTexturePatch<'e, Va>),
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum DatReplaceFunc {
    UnitGroundWeapon,
    SelfOrSubunitGroundWeapon,
    SelfOrSubunitAirWeapon,
    UnitOrderWeapon,
    UpdateStatusScreenTooltip,
    UnitCloakTech,
    UnitCurrentUpgrade,
    UnitCurrentTech,
}

pub struct DatArrayPatch<Va: VirtualAddress> {
    pub dat: DatType,
    /// Also using some of the ids for non-dat fields that are limited by entry count
    /// Units:
    ///     0xff: Status screen funcs
    ///     0xfe: Unit buttons
    /// Sprites:
    ///     0xff: Include in vision sync
    pub field_id: u8,
    /// Unaligned address of a pointer in .text (Or .data/.rdata, whynot)
    /// (e.g. casting it to *const usize and reading it would give pointer to the orig
    /// field array until overwritten)
    pub address: Va,
    /// Offset from start of the array in entries.
    /// i32::MIN for special value of end of array.
    /// (General array analysis does not try to add end-of-array values since they
    /// have high chance of overlapping with another array's start)
    pub entry: i32,
    /// What entry the BW code referred to.
    /// Almost always same as entry, but differs for one sprite hp array use
    /// (Special cased in sprites::patch_hp_bar_init), as well as has just the
    /// original array length when `entry == i32::MIN`
    /// Though this could also just store RVA of the value instead of having
    /// patcher calculate it.
    pub orig_entry: i32,
    /// Offset within the specified entry in bytes.
    pub byte_offset: u32,
}

pub struct DatEntryCountPatch<Va: VirtualAddress> {
    pub dat: DatType,
    // 1/2/4
    pub size_bytes: u8,
    // If the entry count to be written should be multiplied by a constant
    pub multiply: u32,
    pub address: Va,
}

pub struct ExtArrayPatch<'e, Va: VirtualAddress> {
    pub address: Va,
    pub instruction_len: u8,
    pub ext_array_id: u32,
    pub index: Operand<'e>,
    pub two_step: Option<Va>,
}

/// Fixes access to `grp_texture + unit_id` to
/// `grp_texture + extdat_frame[unit_id]`.
pub struct GrpTexturePatch<'e, Va: VirtualAddress> {
    pub address: Va,
    pub instruction_len: u8,
    pub dest: Operand<'e>,
    pub base: Operand<'e>,
    pub index_bytes: Operand<'e>,
    /// If zero, this is a mov/lea -like instruction
    /// `dest = base + index_bytes`
    /// If nonzero (1/2/4/8), this is a memory read
    /// `dest = Mem[base + index_bytes + mem_offset]`.
    pub mem_size: u8,
    pub mem_offset: u8,
}

pub(crate) fn dat_table<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    filename: &'static str,
    functions: &FunctionFinder<'_, 'e, E>,
) -> Option<DatTablePtr<'e>> {
    let binary = analysis.binary;
    let str_refs = functions.string_refs(analysis, filename.as_bytes());

    let functions = functions.functions();
    let mut result = None;
    'outer: for str_ref in &str_refs {
        let addr = entry_of_until(binary, &functions, str_ref.use_address, |entry| {
            find_dat_root(analysis, entry, str_ref)
        }).into_option();
        if let Some(addr) = addr {
            // Check distance between 2 pointers.
            // TODO Could check that they must be relocs?
            if let Ok(first) = binary.read_address(addr) {
                if first.as_u64() > 0x10000 {
                    let size = (2..10).filter_map(|offset| {
                        match binary.read_address(addr + offset * E::VirtualAddress::SIZE) {
                            Ok(x) if x.as_u64() > 0x10000 =>
                                Some(offset * E::VirtualAddress::SIZE),
                            _ => None,
                        }
                    }).next();
                    if let Some(size) = size {
                        let val = DatTablePtr {
                            address: analysis.ctx.constant(addr.as_u64()),
                            entry_size: size,
                        };
                        if single_result_assign(Some(val), &mut result) {
                            break 'outer;
                        }
                    }
                }
            }
        }
    }
    result
}

fn find_dat_root<'e, E: ExecutionState<'e>>(
    analysis: &AnalysisCtx<'e, E>,
    parent: E::VirtualAddress,
    str_ref: &StringRefs<E::VirtualAddress>,
) -> EntryOf<E::VirtualAddress> {
    let ctx = analysis.ctx;
    let binary = analysis.binary;
    let arg_cache = &analysis.arg_cache;
    let mut analysis = FuncAnalysis::new(binary, ctx, parent);
    let mut analyzer = FindDatRoot {
        str_ref,
        addr_found: false,
        result: None,
        arg_cache,
        binary,
    };
    analysis.analyze(&mut analyzer);
    if let Some(result) = analyzer.result {
        EntryOf::Ok(result)
    } else if analyzer.addr_found {
        EntryOf::Stop
    } else {
        EntryOf::Retry
    }
}

struct FindDatRoot<'a, 'e, E: ExecutionState<'e>> {
    str_ref: &'a StringRefs<E::VirtualAddress>,
    addr_found: bool,
    result: Option<E::VirtualAddress>,
    arg_cache: &'a ArgCache<'e, E>,
    binary: &'e BinaryFile<E::VirtualAddress>,
}

impl<'a, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for FindDatRoot<'a, 'e, E> {
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if ctrl.address() == self.str_ref.use_address {
            self.addr_found = true;
        }
        if let Operation::Call(dest) = *op {
            let dest = if_callable_const(self.binary, dest, ctrl);
            let arg1 = ctrl.resolve(self.arg_cache.on_call(0)).if_constant();
            let arg2 = ctrl.resolve(self.arg_cache.on_call(1)).if_constant();
            if let (Some(_dest), Some(arg1), Some(arg2)) = (dest, arg1, arg2) {
                if arg1 == self.str_ref.string_address.as_u64() {
                    self.result = Some(E::VirtualAddress::from_u64(arg2));
                    ctrl.end_analysis();
                }
            }
        }
    }
}

pub(crate) fn dat_patches<'e, E: ExecutionState<'e>>(
    cache: &mut AnalysisCache<'e, E>,
    analysis: &AnalysisCtx<'e, E>,
) -> Option<DatPatches<'e, E::VirtualAddress>> {
    init_warnings_tls();
    let dats = [
        DatType::Units, DatType::Weapons, DatType::Flingy, DatType::Sprites,
        DatType::Upgrades, DatType::TechData, DatType::PortData, DatType::MapData,
        DatType::Orders,
    ];
    let firegraft = cache.firegraft_addresses(analysis);
    let sprite_sync = cache.sprite_include_in_vision_sync(analysis)?;
    let mut dat_ctx = DatPatchContext::new(cache, analysis);
    let dat_ctx = dat_ctx.as_mut()?;
    for &dat in &dats {
        let table = dat_ctx.cache.dat(dat, analysis)?;
        let address = table.address.if_constant().map(|x| E::VirtualAddress::from_u64(x))?;
        dat_ctx.add_dat(dat, address, table.entry_size).ok()?;
    }

    // Status screen array (Using unit 0xff)
    let (buttonset_size, status_func_size) = match E::VirtualAddress::SIZE == 4 {
        true => (0xc, 0xc),
        false => (0x18, 0x18),
    };
    for &status_addr in &firegraft.unit_status_funcs {
        let end_ptr = status_addr + 0xe4 * 0xc;
        dat_ctx.add_dat_global_refs(
            DatType::Units,
            0xff,
            status_addr,
            end_ptr,
            0,
            status_func_size,
            false,
        );
    }
    for &buttons in &firegraft.buttonsets {
        let end_ptr = buttons + 0xfa * 0xc;
        dat_ctx.add_dat_global_refs(
            DatType::Units,
            0xfe,
            buttons,
            end_ptr,
            0,
            buttonset_size,
            false,
        );
        units::button_use_analysis(dat_ctx, buttons)?;
    }
    if let Some(sync) = sprite_sync.if_constant() {
        let sync = E::VirtualAddress::from_u64(sync);
        let end_ptr = sync + 0x205;
        dat_ctx.add_dat_global_refs(DatType::Sprites, 0xff, sync, end_ptr, 0, 0x1, false);
    }

    // This will also use add_dat_global_refs, specifically for wireframe type array.
    // Must be done before instructions_needing_verify.build_lookup
    units::init_units_analysis(dat_ctx)?;

    dat_ctx.unchecked_refs.build_lookup();
    dat_ctx.instructions_needing_verify.build_lookup();

    dat_ctx.add_patches_from_code_refs();
    // Always analyze step_ai_script as it has checks for unit ids in every opcode,
    // and the function is hard to reach otherwise.
    if let Some(step_ai_script) = dat_ctx.cache.step_ai_script(dat_ctx.analysis) {
        dat_ctx.analyze_function_without_goal(step_ai_script);
    }
    while !dat_ctx.funcs_needing_retval_patch.is_empty() ||
        dat_ctx.u8_funcs_pos != dat_ctx.u8_funcs.len() ||
        !dat_ctx.func_arg_widen_queue.is_empty()
    {
        dat_ctx.retval_patch_funcs();
        dat_ctx.add_u8_func_patches();
        dat_ctx.add_func_arg_patches();
    }
    if dat_ctx.unknown_global_u8_mem.len() != 1 {
        dat_warn!(
            dat_ctx, "Expected to have 1 unknown global u8 memory, got {}",
            dat_ctx.unknown_global_u8_mem.len(),
        );
    }
    game::dat_game_analysis(
        &mut dat_ctx.cache,
        &dat_ctx.analysis,
        &mut dat_ctx.required_stable_addresses,
        &mut dat_ctx.result,
    );
    units::command_analysis(dat_ctx)?;
    wireframe::grp_index_patches(dat_ctx)?;
    triggers::trigger_analysis(dat_ctx)?;
    cmdbtns::cmdbtn_analysis(dat_ctx)?;
    sprites::patch_hp_bar_init(dat_ctx)?;
    campaign::patch_mapdata_names(dat_ctx)?;
    dat_ctx.finish_all_patches();
    dat_ctx.result.warnings = get_warnings_tls();
    if crate::test_assertions() {
        // is_sorted_by_key(|x| x.0)
        for pair in dat_ctx.result.arrays_in_code_bytes.windows(2) {
            assert!(pair[0].0 < pair[1].0);
        }
    }
    Some(mem::replace(&mut dat_ctx.result, DatPatches::empty()))
}

pub(crate) struct DatPatchContext<'a, 'acx, 'e, E: ExecutionState<'e>> {
    relocs: Rc<Vec<RelocValues<E::VirtualAddress>>>,
    array_lookup: HashMap<E::VirtualAddress, (DatType, u8)>,
    units: DatTable<E::VirtualAddress>,
    weapons: DatTable<E::VirtualAddress>,
    flingy: DatTable<E::VirtualAddress>,
    sprites: DatTable<E::VirtualAddress>,
    upgrades: DatTable<E::VirtualAddress>,
    techdata: DatTable<E::VirtualAddress>,
    portdata: DatTable<E::VirtualAddress>,
    mapdata: DatTable<E::VirtualAddress>,
    orders: DatTable<E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    text: &'e BinarySection<E::VirtualAddress>,
    result: DatPatches<'e, E::VirtualAddress>,
    unchecked_refs: util::UncheckedRefs<'acx>,
    /// Verifies that DatPatch::Array references in code are actually instructions
    /// accessing the array and not false positives. False positives are removed
    /// before returning the result.
    /// Needed for 64-bit. Not done for 32-bit as
    /// 1) The globals from relocs are assumed to be accurate
    /// 2) This does not currently handle instructions where the global is used as constant
    ///     that exist in 32-bit code. E.g. `cmp [eax], units_dat_hitpoints`
    instructions_needing_verify: util::InstructionsNeedingVerify<'acx>,
    // Funcs that seem to possibly only return in al need to be patched to widen
    // the return value to entirety of eax.
    // That's preferred over patching callers to widen the retval on their own side, as
    // then they don't need to worry about the function returning a wider value, e.g.
    // having get_ground_weapon patched to return u16 eventually.
    funcs_needing_retval_patch: BumpVec<'acx, Rva>,
    funcs_added_for_retval_patch: HashSet<Rva>,
    // Funcs that returned u8 and any of their callers now need to patched to widen the
    // return value
    u8_funcs: BumpVec<'acx, Rva>,
    // First unhandled rva in u8_funcs
    u8_funcs_pos: usize,
    operand_to_u8_op: HashMap<OperandHashByAddress<'e>, Option<U8Operand>>,
    analysis: &'acx AnalysisCtx<'e, E>,
    cache: &'a mut AnalysisCache<'e, E>,
    patched_addresses: HashSet<E::VirtualAddress>,
    analyzed_functions: HashMap<Rva, Box<DatFuncAnalysisState<'acx, 'e, E>>>,
    /// Maps array address patch -> index in result vector.
    /// Meant to solve conflicts where an address technically is inside one array but
    /// in reality is `array[unit_id - first_index]`
    array_address_patches: HashMap<Rva, usize>,

    /// Structures for widening variables that are being passed to a function.
    /// func_arg_widen_requests are used during analysis to lookup if a certain insturction
    /// needs to be widened, func_arg_widen_queue is functions whose callers need to be
    /// analyzed.
    func_arg_widen_requests: HashMap<E::VirtualAddress, [Option<DatType>; 8]>,
    func_arg_widen_queue: BumpVec<'acx, E::VirtualAddress>,
    /// Which callers of function that needs arg widening have been handled.
    found_func_arg_widen_refs: HashSet<E::VirtualAddress>,
    /// Expected to have 1 entry for weapons
    /// global address -> code address
    unknown_global_u8_mem: HashMap<E::VirtualAddress, E::VirtualAddress>,

    step_iscript: E::VirtualAddress,
    /// Set during analysis, contains refs but isn't fully analyzed.
    /// Maybe dumb to special case this
    update_status_screen_tooltip: E::VirtualAddress,
    required_stable_addresses: RequiredStableAddressesMap<'acx, E::VirtualAddress>,
    rdtsc_tracker: util::RdtscTracker<'e>,
    unwind_functions: Rc<x86_64_unwind::UnwindFunctions>,
}

/// Selects handling of memory accesses in widen_instruction()
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum WidenInstruction {
    /// Instruction's R/M memory access is assumed to be something that is
    /// a struct field or global; not replacing u8 -> u32
    Default,
    /// Memory access is assumed to be stack variable, replace with u32 stack variable
    /// (Possibly increasing stack allocation to gain more space to use)
    ///
    /// i32 specifies offset from func entry esp of the instruction, without the
    /// offset of instruction.
    ///
    /// E.g. if assuming usual
    /// push ebp; mov ebp, esp => ebp = esp - 4
    /// Any instruction accessing stack through ebp will have this i32 be -4, regardless
    /// of extra offsets in the instruction.
    StackAccess(i32),
    /// Memory access is assumed to be index to dat arrays, replace u8 index with u32 index.
    /// u64 is address of the array.
    ArrayIndex(u64, DatType, u8, Option<BaseIndexRegs>),
}

/// For widening insturctions on 64bit, where there can be
/// an instruction such as movzx eax, [rax + r12 + dat_array_offset] with rax being byte
/// index while r12 is constant binary base.
/// Or just [rax + r12] where r12 is (binary_base + dat_array_offset)
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct BaseIndexRegs {
    base: u8,
    index: u8,
}

pub(crate) struct RequiredStableAddressesMap<'acx, Va: VirtualAddress> {
    map: HashMap<Rva, RequiredStableAddresses<'acx, Va>>,
    bump: &'acx Bump,
}

pub(crate) struct RequiredStableAddresses<'acx, Va: VirtualAddress> {
    list: RangeList<'acx, Rva, IsJumpDest>,
    phantom: std::marker::PhantomData<*const Va>,
}

impl<'acx, Va: VirtualAddress> RequiredStableAddressesMap<'acx, Va> {
    pub fn with_capacity(cap: usize, bump: &'acx Bump) -> RequiredStableAddressesMap<Va> {
        RequiredStableAddressesMap {
            map: HashMap::with_capacity_and_hasher(cap, Default::default()),
            bump,
        }
    }

    pub fn get(&mut self, rva: Rva) -> &mut RequiredStableAddresses<'acx, Va> {
        let bump = self.bump;
        self.map.entry(rva)
            .or_insert_with(|| RequiredStableAddresses {
                list: RangeList::with_capacity(64, bump),
                phantom: Default::default(),
            })
    }

    pub fn take(&mut self, rva: Rva) -> RequiredStableAddresses<'acx, Va> {
        match self.map.entry(rva) {
            Entry::Occupied(e) => e.remove(),
            Entry::Vacant(_) => RequiredStableAddresses {
                list: RangeList::with_capacity(64, self.bump),
                phantom: Default::default(),
            },
        }
    }

    pub fn add_back(&mut self, rva: Rva, list: RequiredStableAddresses<'acx, Va>) {
        let had_any = self.map.insert(rva, list).is_some();
        debug_assert!(!had_any);
    }
}

impl<'acx, Va: VirtualAddress> RequiredStableAddresses<'acx, Va> {
    pub fn try_add(
        &mut self,
        binary: &BinaryFile<Va>,
        start: Va,
        end: Va,
        is_jump_dest: IsJumpDest,
    ) -> Result<(), (Va, Va, &mut IsJumpDest)> {
        let start = Rva((start.as_u64() - binary.base.as_u64()) as u32);
        let end = Rva((end.as_u64() - binary.base.as_u64()) as u32);
        if let Err(old_range) = self.list.add(start, end, is_jump_dest) {
            let start = binary.base + (old_range.0).0;
            let end = binary.base + (old_range.1).0;
            Err((start, end, old_range.2))
        } else {
            Ok(())
        }
    }

    pub fn try_add_for_patch(
        &mut self,
        binary: &BinaryFile<Va>,
        start: Va,
        end: Va,
    ) -> Result<(), (Va, Va)> {
        match self.try_add(binary, start, end, IsJumpDest::No) {
            Ok(()) => Ok(()),
            Err(e) => {
                if e.0 == start && e.1 >= end && *e.2 == IsJumpDest::Yes {
                    *e.2 = IsJumpDest::No;
                    Ok(())
                } else if e.0 == start && e.1 < end && *e.2 == IsJumpDest::Yes {
                    // Can potentially grow this to contain this entire range.
                    let start = Rva((start.as_u64() - binary.base.as_u64()) as u32);
                    let end = Rva((end.as_u64() - binary.base.as_u64()) as u32);
                    if let Err(e2) = self.list.grow(start, end, IsJumpDest::No) {
                        let start = binary.base + (e2.0).0;
                        let end = binary.base + (e2.1).0;
                        Err((start, end))
                    } else {
                        Ok(())
                    }
                } else {
                    Err((e.0, e.1))
                }
            }
        }
    }

    pub fn add_jump_dest(
        &mut self,
        binary: &BinaryFile<Va>,
        to: Va,
    ) -> Result<(), (Va, Va)> {
        if let Some(len) = instruction_length(binary, to) {
            let end = to + len as u32;
            if let Err(e) = self.try_add(binary, to, end, IsJumpDest::Yes) {
                let e = (e.0, e.1, *e.2);
                let input = (to, end, IsJumpDest::Yes);
                if (e.0, e.1) != (input.0, input.1) {
                    // Accept jumps inside a jump dest, as those are sometimes
                    // generated
                    let accept = e.2 == IsJumpDest::Yes && (
                            (e.0 <= input.0 && e.1 >= input.1) ||
                            (e.0 >= input.0 && e.1 <= input.1)
                        );
                    if !accept {
                        return Err((e.0, e.1));
                    }
                }
            }
        }
        Ok(())
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = (Rva, Rva)> + 'a {
        self.list.iter()
    }
}

struct DatTable<Va: VirtualAddress> {
    table_address: Va,
    field_count: u32,
    entry_size: u32,
}

/// For keeping track of when an argument or return value is being accessed
/// with only 8bit width.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
enum U8Operand {
    Arg(u8),
    /// Custom id
    Return(u32),
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> DatPatchContext<'a, 'acx, 'e, E> {
    fn new(
        cache: &'a mut AnalysisCache<'e, E>,
        analysis: &'acx AnalysisCtx<'e, E>,
    ) -> Option<DatPatchContext<'a, 'acx, 'e, E>> {
        fn dat_table<Va: VirtualAddress>(field_count: u32) -> DatTable<Va> {
            DatTable {
                table_address: Va::from_u64(0),
                field_count,
                entry_size: 0,
            }
        }

        let text = analysis.binary_sections.text;
        let step_iscript = cache.step_iscript(analysis)?;
        let unwind_functions = cache.unwind_functions();
        let bump = &analysis.bump;
        let ctx = analysis.ctx;
        let instructions_needing_verify_capacity = match E::VirtualAddress::SIZE == 4 {
            true => 0,
            false => 1024,
        };
        Some(DatPatchContext {
            array_lookup: HashMap::with_capacity_and_hasher(128, Default::default()),
            operand_to_u8_op: HashMap::with_capacity_and_hasher(2048, Default::default()),
            funcs_needing_retval_patch: bumpvec_with_capacity(16, bump),
            funcs_added_for_retval_patch:
                HashSet::with_capacity_and_hasher(16, Default::default()),
            u8_funcs: bumpvec_with_capacity(16, bump),
            u8_funcs_pos: 0,
            unchecked_refs: util::UncheckedRefs::new(bump),
            instructions_needing_verify:
                util::InstructionsNeedingVerify::new(bump, instructions_needing_verify_capacity),
            units: dat_table(0x36),
            weapons: dat_table(0x18),
            flingy: dat_table(0x7),
            sprites: dat_table(0x6),
            upgrades: dat_table(0xc),
            techdata: dat_table(0xb),
            portdata: dat_table(0x6),
            mapdata: dat_table(0x1),
            orders: dat_table(0x13),
            binary: analysis.binary,
            relocs: cache.globals_with_values(),
            text,
            analysis,
            cache,
            result: DatPatches {
                patches: Vec::with_capacity(1024),
                code_bytes: Vec::with_capacity(2048),
                arrays_in_code_bytes: Vec::with_capacity(64),
                set_status_screen_tooltip: None,
                unit_wireframe_type: None,
                campaign_map_names: None,
                warnings: DatWarnings::new(),
            },
            patched_addresses: HashSet::with_capacity_and_hasher(64, Default::default()),
            analyzed_functions: HashMap::with_capacity_and_hasher(64, Default::default()),
            func_arg_widen_requests: HashMap::with_capacity_and_hasher(32, Default::default()),
            func_arg_widen_queue: bumpvec_with_capacity(32, bump),
            found_func_arg_widen_refs:
                HashSet::with_capacity_and_hasher(128, Default::default()),
            step_iscript,
            unknown_global_u8_mem: HashMap::with_capacity_and_hasher(4, Default::default()),
            array_address_patches: HashMap::with_capacity_and_hasher(256, Default::default()),
            update_status_screen_tooltip: E::VirtualAddress::from_u64(0),
            required_stable_addresses: RequiredStableAddressesMap::with_capacity(1024, bump),
            rdtsc_tracker: util::RdtscTracker::new(
                ctx.and_const(ctx.custom(RDTSC_CUSTOM), 0xffff_ffff)
            ),
            unwind_functions,
        })
    }

    fn add_dat(
        &mut self,
        dat: DatType,
        table_address: E::VirtualAddress,
        entry_size: u32,
    ) -> Result<(), ()> {
        let (entry, entry_count, field_sizes) = match dat {
            DatType::Units => (&mut self.units, 0xe4, &UNIT_ARRAY_WIDTHS),
            DatType::Weapons => (&mut self.weapons, 0x82, &WEAPON_ARRAY_WIDTHS),
            DatType::Flingy => (&mut self.flingy, 0xd1, &FLINGY_ARRAY_WIDTHS),
            DatType::Sprites => (&mut self.sprites, 0x205, &SPRITE_ARRAY_WIDTHS),
            DatType::Upgrades => (&mut self.upgrades, 0x3d, &UPGRADE_ARRAY_WIDTHS),
            DatType::TechData => (&mut self.techdata, 0x2c, &TECHDATA_ARRAY_WIDTHS),
            DatType::PortData => {
                if E::VirtualAddress::SIZE == 4 {
                    (&mut self.portdata, 0x6e, &PORTDATA_ARRAY_WIDTHS_32)
                } else {
                    (&mut self.portdata, 0x6e, &PORTDATA_ARRAY_WIDTHS_64)
                }
            }
            DatType::MapData => {
                if E::VirtualAddress::SIZE == 4 {
                    (&mut self.mapdata, 0x41, &MAPDATA_ARRAY_WIDTHS_32)
                } else {
                    (&mut self.mapdata, 0x41, &MAPDATA_ARRAY_WIDTHS_64)
                }
            }
            DatType::Orders => (&mut self.orders, 0xbd, &ORDER_ARRAY_WIDTHS),
            _ => return Err(()),
        };
        entry.table_address = table_address;
        entry.entry_size = entry_size;
        for i in 0..entry.field_count {
            let entry_address = table_address + i * entry_size;
            let array_ptr = self.binary.read_address(entry_address)
                .map_err(|_| ())?;
            self.array_lookup.insert(array_ptr, (dat, i as u8));

            // DatTable size value. DatTable ptr isn't needed since it's also a global ref
            self.result.patches.push(DatPatch::EntryCount(DatEntryCountPatch {
                dat,
                size_bytes: 4,
                multiply: 1,
                address: entry_address + E::VirtualAddress::SIZE + 4,
            }));

            let do_analysis = true;
            // Global refs
            let field_size = field_sizes[i as usize];
            let (array_entries, start_index) = match (dat, i) {
                (DatType::Units, 0x03) => (0x60, 0x6a),
                (DatType::Units, 0x1d) => (0x6a, 0x00),
                (DatType::Units, 0x20) => (0x6a, 0x00),
                (DatType::Units, 0x21) => (0x6a, 0x00),
                (DatType::Units, 0x22) => (0x6a, 0x00),
                (DatType::Units, 0x23) => (0x6a, 0x00),
                (DatType::Units, 0x25) => (0x60, 0x6a),
                (DatType::Sprites, 0x01) => (0x183, 0x82),
                (DatType::Sprites, 0x04) => (0x183, 0x82),
                (DatType::Sprites, 0x05) => (0x183, 0x82),
                _ => (entry_count, 0),
            };
            let end_ptr = array_ptr + array_entries * field_size as u32;
            self.add_dat_global_refs(
                dat,
                i as u8,
                array_ptr,
                end_ptr,
                start_index,
                field_size,
                do_analysis,
            );
        }
        Ok(())
    }

    fn add_dat_global_refs(
        &mut self,
        dat: DatType,
        field_id: u8,
        array_ptr: E::VirtualAddress,
        end_ptr: E::VirtualAddress,
        start_index: u32,
        field_size: u8,
        add_unchecked_ref_analysis: bool,
    ) {
        let start_ptr = match dat {
            // There are some 1-indexed unit ids
            // Ai attack forces refers to flags,
            // and for some reason armor and only armor is written with -1
            // pointer with chk unit settings.
            DatType::Units if matches!(field_id, 0x16 | 0x1b) => array_ptr - field_size as u32,
            _ => array_ptr,
        };
        let start = self.relocs.binary_search_by(|x| match x.value >= start_ptr {
            true => Ordering::Greater,
            false => Ordering::Less,
        }).unwrap_err();
        let text = self.text;
        let text_end = text.virtual_address + text.virtual_size;
        for i in start.. {
            let reloc = match self.relocs.get(i) {
                Some(s) if s.value < end_ptr => s,
                _ => break,
            };
            let address = reloc.address;
            let rva = Rva(self.binary.rva_32(address));
            let offset_bytes = (reloc.value.as_u64().wrapping_sub(array_ptr.as_u64())) as i32;
            let offset = (start_index as i32).saturating_add(offset_bytes / field_size as i32);
            let byte_offset = offset_bytes as u32 % field_size as u32;
            let array_patch = DatArrayPatch {
                dat,
                field_id,
                address,
                entry: offset,
                orig_entry: offset,
                byte_offset,
            };
            if !self.add_dat_array_patch_unverified(array_patch) {
                continue;
            }
            // Assuming that array ref analysis for hardcoded indices isn't important.
            // (It isn't as of this writing)
            // Adding them as well would require better entry_of results as currently
            // they are checked by looking up the array_lookup hashtable which only contains
            // offset 0 addresses.
            if add_unchecked_ref_analysis && offset_bytes == 0 {
                if address >= text.virtual_address && address < text_end {
                    self.unchecked_refs.push(rva);
                }
            }
        }
        if start_index != 0 {
            // If there's a reloc for array_ptr - start_index * field_size,
            // assume it's meant for array[id - start_index]
            let zero_ptr = array_ptr - start_index.wrapping_mul(field_size as u32);
            let last_valid = if dat == DatType::Units && field_id == 0x25 {
                // Units.dat addon position should also accept .y index
                zero_ptr + 2
            } else {
                zero_ptr
            };
            let start = self.relocs.binary_search_by(|x| match x.value >= zero_ptr {
                true => Ordering::Greater,
                false => Ordering::Less,
            }).unwrap_err();
            for i in start.. {
                if let Some(reloc) = self.relocs.get(i).filter(|x| x.value <= last_valid) {
                    let byte_offset = (reloc.value.as_u64() as u32)
                        .wrapping_sub(zero_ptr.as_u64() as u32);
                    let patch = DatArrayPatch {
                        dat,
                        field_id,
                        address: reloc.address,
                        entry: 0,
                        orig_entry: 0,
                        byte_offset,
                    };
                    self.add_dat_array_patch_unverified(patch);
                } else {
                    break;
                }
            }
        }
    }

    /// Return false if the patch wasn't added due to an existing patch having priority.
    ///
    /// Adds the patch, but adds the address to instructions_needing_verify list.
    /// The verification is needed to avoid global false positives in 64bit,
    /// but will also be done in 32bit for consistency. Shouldn't be too expensive?
    fn add_dat_array_patch_unverified(
        &mut self,
        patch: DatArrayPatch<E::VirtualAddress>,
    ) -> bool {
        let address = patch.address;
        if !self.add_or_override_dat_array_patch(patch) {
            return false;
        }

        let text = self.text;
        let text_end = text.virtual_address + text.virtual_size;
        if E::VirtualAddress::SIZE == 8 && address >= text.virtual_address && address < text_end {
            // Address should be 4 bytes from instruction end..
            let rva = Rva(self.binary.rva_32(address).wrapping_add(4));
            self.instructions_needing_verify.push(rva);
        }
        true
    }

    /// Return false if the patch wasn't added due to an existing patch having priority.
    ///
    /// Has heuristics to determine which of two arrays gets priority in case of conflict.
    fn add_or_override_dat_array_patch(
        &mut self,
        patch: DatArrayPatch<E::VirtualAddress>,
    ) -> bool {
        enum Action {
            UseOld,
            UseNew,
            Warn,
        }

        let address = patch.address;
        let entry = patch.entry;
        let field_id = patch.field_id;
        let dat = patch.dat;
        let rva = Rva(self.binary.rva_32(address));
        let patch = DatPatch::Array(patch);
        match self.array_address_patches.entry(rva) {
            Entry::Occupied(e) => {
                // Overlap, if the entry isn't 0 it's likely 0 entry
                // for an array whose start_index isn't 0
                // Also assume that entry -1 is more correct than something else.
                let index = *e.get();
                let action = if entry == i32::MIN {
                    // Special case of known array end; (at least) units::init_units_analysis
                    // will add this for units.dat dimensionbox end which likely overlaps
                    // with another array.
                    Action::UseNew
                } else if entry != 0 {
                    Action::UseOld
                } else {
                    if let DatPatch::Array(ref old) = self.result.patches[index] {
                        if entry == -1 && old.entry != -1 {
                            Action::UseNew
                        } else if old.entry == -1 && entry != -1 {
                            Action::UseOld
                        } else if entry == 0 && old.entry != 0 {
                            Action::UseNew
                        } else {
                            Action::Warn
                        }
                    } else {
                        Action::Warn
                    }
                };
                match action {
                    Action::UseOld => false,
                    Action::Warn => {
                        dat_warn!(
                            self, "Conflict with dat global refs @ {:?}  {:?}:{:x}",
                            address, dat, field_id,
                        );
                        false
                    }
                    Action::UseNew => {
                        self.result.patches[index] = patch;
                        true
                    }
                }
            }
            Entry::Vacant(e) => {
                e.insert(self.result.patches.len());
                self.result.patches.push(patch);
                true
            }
        }
    }

    fn add_patches_from_code_refs(&mut self) {
        let functions = self.cache.functions();
        let binary = self.binary;
        loop {
            let rva = match self.unchecked_refs.pop() {
                Some(s) => s,
                None => break,
            };
            let address = binary.base + rva.0;
            entry_of_until(binary, &functions, address, |entry| {
                if entry == self.update_status_screen_tooltip {
                    return EntryOf::Ok(());
                }
                let entry_rva = Rva((entry.as_u64() - binary.base.as_u64()) as u32);
                let mode = DatFuncAnalysisMode::ArrayIndex;
                if !self.analyzed_functions.contains_key(&entry_rva) {
                    self.analyze_function(entry, address, mode)
                } else {
                    EntryOf::Retry
                }
            });
        }
    }

    fn analyze_function(
        &mut self,
        entry: E::VirtualAddress,
        ref_address: E::VirtualAddress,
        mode: DatFuncAnalysisMode,
    ) -> EntryOf<()> {
        let binary = self.binary;
        let ctx = self.analysis.ctx;
        let mut analysis = FuncAnalysis::new(binary, ctx, entry);
        let entry_rva = Rva((entry.as_u64() - binary.base.as_u64()) as u32);
        let mut rsa = self.required_stable_addresses.take(entry_rva);
        let mut analyzer = match self.analyzed_functions.remove(&entry_rva) {
            Some(state) => {
                DatReferringFuncAnalysis::rebuild(self, self.text, &mut rsa, state, mode)
            }
            None => {
                DatReferringFuncAnalysis::new(self, self.text, &mut rsa, entry, ref_address, mode)
            }
        };
        analyzer.state.stack_size_tracker.reset();
        analysis.analyze(&mut analyzer);
        analyzer.generate_needed_patches(analysis, entry);
        let result = analyzer.result;
        let state = analyzer.state;
        self.required_stable_addresses.add_back(entry_rva, rsa);
        self.analyzed_functions.insert(entry_rva, state);
        result
    }

    /// Analyzes function to see if anything can be patched.
    /// Useful for removing dat_id >= max check if the function is known to be
    /// hard to find from other analysis.
    fn analyze_function_without_goal(&mut self, entry: E::VirtualAddress) {
        let entry_rva = Rva((entry.as_u64() - self.binary.base.as_u64()) as u32);
        if !self.analyzed_functions.contains_key(&entry_rva) {
            self.analyze_function(entry, entry, DatFuncAnalysisMode::ArrayIndex);
        }
    }

    fn add_u8_func_patches(&mut self) {
        let functions = self.cache.functions();
        let binary = self.binary;
        let mut checked_funcs = HashSet::with_capacity_and_hasher(64, Default::default());
        for i in self.u8_funcs_pos.. {
            let func_rva = match self.u8_funcs.get(i) {
                Some(&s) => s,
                None => {
                    self.u8_funcs_pos = i;
                    break;
                }
            };
            let func = binary.base + func_rva.0;
            let function_finder = self.cache.function_finder();
            let callers = function_finder.find_callers(self.analysis, func);
            for &address in &callers {
                entry_of_until(binary, &functions, address, |entry| {
                    if entry == self.update_status_screen_tooltip {
                        // This is bit iffy since this may be needed for func args,
                        // but update_status_screen_tooltip shouldn't have cfg analysis
                        // required outside of the weapon tooltip code..
                        return EntryOf::Ok(());
                    }
                    let entry_rva = Rva((entry.as_u64() - binary.base.as_u64()) as u32);
                    let mode = DatFuncAnalysisMode::ArrayIndex;
                    if !self.analyzed_functions.contains_key(&entry_rva) {
                        self.analyze_function(entry, address, mode);
                    }
                    let mut result = EntryOf::Retry;
                    if let Some(mut state) = self.analyzed_functions.remove(&entry_rva) {
                        if state.has_called_func(func_rva) {
                            if checked_funcs.insert(entry_rva) {
                                let mut rsa = self.required_stable_addresses.take(entry_rva);
                                let mut analyzer = DatReferringFuncAnalysis::rebuild(
                                    self,
                                    self.text,
                                    &mut rsa,
                                    state,
                                    mode,
                                );
                                for &rva in &analyzer.dat_ctx.u8_funcs {
                                    if let Some(&index) =
                                        analyzer.state.calls_reverse_lookup.get(&rva)
                                    {
                                        analyzer.needed_func_results.insert(index);
                                    }
                                }
                                analyzer.generate_noncfg_patches();
                                state = analyzer.state;
                                self.required_stable_addresses.add_back(entry_rva, rsa);
                            }
                            result = EntryOf::Ok(());
                        }
                        self.analyzed_functions.insert(entry_rva, state);
                    }
                    result
                });
            }
        }
    }

    fn add_func_arg_patches(&mut self) {
        let functions = self.cache.functions();
        let binary = self.binary;
        while let Some(child_func) = self.func_arg_widen_queue.pop() {
            // TODO: This does not find tail calls.
            let callers = self.cache.function_finder().find_callers(self.analysis, child_func);
            for &address in &callers {
                if self.found_func_arg_widen_refs.contains(&address) {
                    continue;
                }
                entry_of_until(binary, &functions, address, |entry| {
                    // As long as update_status_screen_tooltip is not fully patched,
                    // func args are needed for widening func calls using scarab / interceptor
                    // weapon ids.
                    self.analyze_function(entry, address, DatFuncAnalysisMode::FuncArg);
                    if self.found_func_arg_widen_refs.contains(&address) {
                        EntryOf::Ok(())
                    } else {
                        EntryOf::Retry
                    }
                });
            }
        }
    }

    fn finish_all_patches(&mut self) {
        let binary = self.binary;
        if E::VirtualAddress::SIZE == 8 {
            self.verify_remaining_instructions();
            let bad_patch_rvas = self.instructions_needing_verify.finish(&self.analysis.bump);
            if !bad_patch_rvas.is_empty() {
                // TODO: This would be better(?) with swap_remove, but some code
                // may rely on patch order so not doing it right now.
                // Usually will have to remove few patches so retain is better
                // than multiple removes.
                // Or maybe could just have Patch::None nops?
                for &rva in &bad_patch_rvas {
                    if let Some(&index) = self.array_address_patches.get(&Rva(rva.0 - 4)) {
                        self.result.patches[index] =
                            DatPatch::GrpIndexHook(E::VirtualAddress::from_u64(0));
                    } else {
                        dat_warn!(self, "Expected to find array patch for rva {:x}", rva.0);
                    }
                }
                self.result.patches.retain(|x| match x {
                    DatPatch::GrpIndexHook(x) => x.as_u64() != 0,
                    _ => true,
                });
            }
        }
        let funcs = mem::replace(&mut self.analyzed_functions, Default::default());
        for (rva, state) in funcs.into_iter() {
            if self.u8_funcs.contains(&rva) {
                // These funcs are hooked completely, no need to process their
                // instruction-level hooks
                // (And the hooks may overlap with hooking over the entry point, which would
                // cause issues)
                continue;
            }
            let mode = DatFuncAnalysisMode::ArrayIndex;
            let mut rsa = self.required_stable_addresses.take(rva);
            let mut analyzer =
                DatReferringFuncAnalysis::rebuild(self, self.text, &mut rsa, state, mode);
            analyzer.generate_stack_size_patches();
            let pending_hooks = mem::replace(
                &mut analyzer.state.pending_hooks,
                BumpVec::new_in(&self.analysis.bump),
            );
            if !pending_hooks.is_empty() {
                let mut hook_ctx = FunctionHookContext::<E> {
                    result: &mut self.result,
                    required_stable_addresses: &mut rsa,
                    entry: binary.base() + rva.0,
                    binary,
                };
                hook_ctx.process_pending_hooks(pending_hooks);
            }
        }
    }

    /// instructions_needing_verify will have most of the instructions verified in
    /// dat ref analysis, but that is not done for all of the array patches, which
    /// will be handled here.
    fn verify_remaining_instructions(&mut self) {
        let mut pos = 0usize;
        let base = self.binary.base();
        while let Some(rva) = self.instructions_needing_verify.next_unverified(&mut pos) {
            let address = base + rva.0;
            self.analyze_for_instruction_verify(address);
        }
    }

    fn analyze_for_instruction_verify(&mut self, address: E::VirtualAddress) {
        let functions = self.cache.functions();
        let binary = self.binary;
        let ctx = self.analysis.ctx;
        entry_of_until(binary, &functions, address, |entry| {
            let mut analyzer = util::InstructionVerifyOnlyAnalyzer::<E>::new(
                &mut self.instructions_needing_verify,
                self.text,
                &self.rdtsc_tracker,
            );
            let mut analysis = FuncAnalysis::new(binary, ctx, entry);
            analysis.analyze(&mut analyzer);
            analyzer.entry_of()
        });
    }

    fn retval_patch_funcs(&mut self) {
        let binary = self.binary;
        let ctx = self.analysis.ctx;
        loop {
            let rva = match self.funcs_needing_retval_patch.pop() {
                Some(s) => s,
                None => break,
            };
            let address = binary.base + rva.0;
            let mut analyzer = RecognizeDatPatchFunc::new(self);
            let mut analysis = FuncAnalysis::new(binary, ctx, address);
            analysis.analyze(&mut analyzer);
            if let Ok(result) = analyzer.result() {
                if let Some(func) = result {
                    self.result.patches.push(DatPatch::ReplaceFunc(address, func));
                    self.u8_funcs.push(rva);
                }
            } else {
                dat_warn!(self, "Cannot recognize function @ {:?}", address);
            }
        }
    }

    fn contains_u8_operand(&mut self, op: Operand<'e>) -> Option<U8Operand> {
        let key = op.hash_by_address();
        if let Some(&result) = self.operand_to_u8_op.get(&key) {
            return result;
        }
        let result = match *op.ty() {
            OperandType::Arithmetic(ref arith) => {
                let is_and_ff = arith.ty == ArithOpType::And &&
                    arith.right.if_constant() == Some(0xff);
                if E::VirtualAddress::SIZE == 8 {
                    // Check 64 bit register args
                    if is_and_ff {
                        if let Some(reg) = arith.left.if_register() {
                            let result = match reg {
                                1 => Some(U8Operand::Arg(0)),
                                2 => Some(U8Operand::Arg(1)),
                                8 => Some(U8Operand::Arg(2)),
                                9 => Some(U8Operand::Arg(3)),
                                _ => None,
                            };
                            self.operand_to_u8_op.insert(key, result);
                            return result;
                        }
                    }
                }

                let left = self.contains_u8_operand(arith.left);
                if is_and_ff {
                    left
                } else {
                    let right = self.contains_u8_operand(arith.right);
                    if left == right {
                        left
                    } else {
                        None
                    }
                }
            }
            OperandType::Custom(c) => Some(U8Operand::Return(c)),
            OperandType::Memory(ref mem) if mem.size == MemAccessSize::Mem8 => {
                let (base, offset) = mem.address();
                let ctx = self.analysis.ctx;
                if base == ctx.register(4) {
                    if let Some(arg_n) = arg_n_from_offset::<E>(offset) {
                        return Some(U8Operand::Arg(arg_n));
                    }
                }
                None
            }
            _ => None,
        };
        self.operand_to_u8_op.insert(key, result);
        result
    }

    /// Requests patching any function which calls `func` to widen `arg` from u8
    /// These can be generated during the initial dat index analysis, but also
    /// during one of these func arg widening passes
    fn add_func_arg_widening_request(&mut self, func: E::VirtualAddress, arg_n: u8, dat: DatType) {
        if arg_n >= 8 {
            return;
        }
        let entry = self.func_arg_widen_requests.entry(func);
        let arr = entry.or_insert_with(|| [None; 8]);
        if arr[arg_n as usize].is_some() {
            return;
        }
        arr[arg_n as usize] = Some(dat);
        // It's most likely the last one if any but check all anyway
        if !self.func_arg_widen_queue.iter().rev().any(|&x| x == func) {
            self.func_arg_widen_queue.push(func);
        }
    }

    fn add_replace_patch(&mut self, address: E::VirtualAddress, patch: &[u8]) {
        let result = &mut self.result;
        let code_bytes_offset = result.code_bytes.len() as u32;
        result.code_bytes.extend_from_slice(patch);
        result.patches.push(DatPatch::Replace(address, code_bytes_offset, patch.len() as u8));
    }
}

struct DatReferringFuncAnalysis<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'b, 'acx, 'e, E>,
    state: Box<DatFuncAnalysisState<'acx, 'e, E>>,
    partial_register_moves: PartialRegisterMoves,
    ref_address: E::VirtualAddress,
    needed_func_params: [Option<DatType>; 16],
    needed_func_results: HashSet<u32>,
    needed_cfg_analysis:
        BumpVec<'acx, (E::VirtualAddress, E::VirtualAddress, Option<Operand<'e>>, DatType)>,
    result: EntryOf<()>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    text: &'e BinarySection<E::VirtualAddress>,
    current_branch: E::VirtualAddress,
    entry: E::VirtualAddress,
    is_update_status_screen_tooltip: bool,
    switch_table: E::VirtualAddress,
    mode: DatFuncAnalysisMode,
    /// Address ranges which can't be patched over. Either because they have a
    /// patch/hook already, or they are a jump destination.
    /// (Jump destinations can be patched over if the patch starts at the start
    /// of the range)
    required_stable_addresses: &'a mut RequiredStableAddresses<'acx, E::VirtualAddress>,
    instruction_verify_pos: util::InsVerifyIter<E::VirtualAddress>,
}

#[derive(Eq, PartialEq, Copy, Clone, Debug, Hash)]
enum DatFuncAnalysisMode {
    ArrayIndex,
    FuncArg,
}

/// State that can be saved away while other analysises are ran
struct DatFuncAnalysisState<'acx, 'e, E: ExecutionState<'e>> {
    // Eax from calls is written as Custom(index_to_calls_vec)
    // to distinguish them from undefs that come from state merges
    calls: BumpVec<'acx, Rva>,
    calls_reverse_lookup: HashMap<Rva, u32>,
    next_cfg_custom_id: u32,
    /// Bit 0x8000_0000 on rva is set if stack access
    u8_instruction_lists: InstructionLists<'acx, U8Operand>,
    stack_size_tracker: stack_analysis::StackSizeTracker<'acx, 'e, E>,
    /// Buffer hooks after all other patches to be sure that we don't add a longjump
    /// hook which prevents another patch.
    ///
    /// 2 step hooks require a 10 byte free block from somewhere, but just
    /// taking one while asking for a hook could end up taking an address
    /// that would need to be hooked.
    /// So buffer 2step hooks and do them last.
    pending_hooks: BumpVec<'acx, (E::VirtualAddress, u32, u8, u8)>,
    detect_tail_call: DetectTailCall<'e, E>,
}

impl<'acx, 'e, E: ExecutionState<'e>> DatFuncAnalysisState<'acx, 'e, E> {
    fn has_called_func(&self, rva: Rva) -> bool {
        self.calls_reverse_lookup.contains_key(&rva)
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub(crate) enum IsJumpDest {
    Yes,
    No,
}

/// More or less equivalent to HashMap<Key, Vec<(Rva, WidenInstruction)>>,
/// but allocates only a single Vec.
/// Technically WidenInstruction wouldn't have to be stored here, as it
/// could be just separate Rva -> WidenInstruction map instead (Isn't supposed to
/// change based on Key)
struct InstructionLists<'acx, Key: Hash + Eq> {
    heads: HashMap<Key, usize>,
    /// usize is link to the next operand, or !0 if end of list
    store: BumpVec<'acx, ((Rva, WidenInstruction), usize)>,
    /// Avoid adding same Rva to the list twice
    used_addresses: HashSet<Rva>,
}

/// bool means that first invalid is None
fn entry_limit_to_dat(entries: u32) -> Option<(DatType, bool)> {
    Some(match entries {
        0x6a => (DatType::Units, false), // First building
        0xe4 => (DatType::Units, true),
        0x82 => (DatType::Weapons, true),
        0xd1 => (DatType::Flingy, false),
        0x205 => (DatType::Sprites, false),
        0x3e7 => (DatType::Images, false),
        0x3d => (DatType::Upgrades, true),
        0x2c => (DatType::TechData, true),
        0x6e => (DatType::PortData, false),
        0xbd => (DatType::Orders, false),
        // Not including mapdata, its entry limit patch requires bit of special handling
        _ => return None,
    })
}

fn is_widened_dat_field(dat: DatType, field_id: u8) -> bool {
    match (dat, field_id) {
        // units_dat_flingy
        (DatType::Units, 0x00) => true,
        // Ground/air weapons
        (DatType::Units, 0x11) => true,
        (DatType::Units, 0x13) => true,
        // Upgrades
        (DatType::Units, 0x19) => true,
        (DatType::Weapons, 0x06) => true,
        // Order weapon
        (DatType::Orders, 0x0d) => true,
        // Order tech
        (DatType::Orders, 0x0e) => true,
        _ => false,
    }
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    DatReferringFuncAnalysis<'a, 'b, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.state.detect_tail_call.operation(ctrl, op) {
            if let Operation::Jump { to, .. } = *op {
                if let Some(to) = ctrl.resolve_va(to) {
                    if self.mode == DatFuncAnalysisMode::FuncArg {
                        self.check_call_for_func_arg_widen(ctrl, to, true);
                    }
                    // Hackfix to prevent analysis regression:
                    // There is one simple function where it tail calls a function immediately
                    // following itself, and that function is needed for analysis.
                    // function finder does not consider the tail called function be
                    // a separate function since it is only tail called, but it finds the
                    // function immediately before and things work out since it tail calls
                    // the other.
                    // Proper fix would fix function finder find functions that are only tail
                    // called, instead of relying placement of functions making things work out.
                    let address = ctrl.address();
                    if self.current_branch == self.entry && to > address && to < address + 0x20 {
                        return;
                    }
                }
            }
            ctrl.end_branch();
            return;
        }

        if self.state.stack_size_tracker.operation(ctrl, op) {
            return;
        }
        let binary = self.binary;
        let ctx = ctrl.ctx();
        if self.is_update_status_screen_tooltip {
            match *op {
                Operation::Call(dest) => {
                    let arg_cache = &self.dat_ctx.analysis.arg_cache;
                    let arg1 = ctrl.resolve(arg_cache.on_call(0));
                    let arg2 = ctrl.resolve(arg_cache.on_call(1));
                    let init_cap = match E::VirtualAddress::SIZE {
                        4 => 0x8000_000f,
                        _ => 0x8000_0000_0000_000f,
                    };
                    let access =
                        ctx.mem_access(arg2, 2 * E::VirtualAddress::SIZE as u64, E::WORD_SIZE);
                    let arg2_capacity = ctrl.read_memory(&access);
                    let ok = Some(())
                        .filter(|_| arg1 == arg_cache.on_entry(0))
                        .and_then(|_| arg2_capacity.if_constant())
                        .filter(|&c| c == init_cap)
                        .is_some();
                    if ok {
                        if let Some(dest) = ctrl.resolve(dest).if_constant() {
                            let dest = E::VirtualAddress::from_u64(dest);
                            self.dat_ctx.result.set_status_screen_tooltip = Some(dest);
                            ctrl.end_analysis();
                        }
                    }
                }
                _ => (),
            }
            return;
        }
        let ins_address = ctrl.address();
        let current_instruction_end = ctrl.current_instruction_end();
        let ref_addr = self.ref_address;
        if ins_address == self.switch_table {
            // Executed to switch table cases, stop
            ctrl.skip_operation();
            ctrl.end_branch();
            return;
        }
        if ref_addr >= ins_address && ref_addr < current_instruction_end {
            self.result = EntryOf::Ok(());
        }

        // InstructionsNeedingVerify needs "instruction end" as the position that
        // is added at first and now checked. The added value is just `memaddr_pos + 4`,
        // which is the actual instruction end when there is no immediate constant,
        // but for instructions that have an immediate, adjust the "instruction_verify_end"
        // to be before it so that it matches the initial `+ 4`.
        if E::VirtualAddress::SIZE == 8 &&
            self.instruction_verify_pos.near_instruction_end(current_instruction_end)
        {
            let instruction_verify_end = current_instruction_end -
                util::instruction_verify_imm_size(self.text, ins_address);
            let end_start_diff = (instruction_verify_end.as_u64() as u32)
                .wrapping_sub(ins_address.as_u64() as u32);
            // See commment in InstructionVerifyOnlyAnalyzer::operation
            if end_start_diff >= 5 {
                self.instruction_verify_pos.at_instruction_end(
                    instruction_verify_end,
                    binary,
                    &mut self.dat_ctx.instructions_needing_verify,
                );
            }
        }

        // Rdtsc checks usually are enough but not always.
        ctrl.aliasing_memory_fix(op);

        match *op {
            Operation::Move(ref dest, val, None) => {
                if self.dat_ctx.rdtsc_tracker.check(ctrl, dest, val) {
                    return;
                }
                if self.mode == DatFuncAnalysisMode::ArrayIndex {
                    self.check_array_ref(ctrl, val);
                    if let DestOperand::Memory(mem) = dest {
                        self.check_array_ref_const(ctrl, mem.address().1);
                    }
                }
                // Check l/r separately if the instruction has two operands
                // Ignore ands since they're likely low registers and not
                // real 2-operand instructions
                let mut did_skip = false;
                match *val.ty() {
                    OperandType::Arithmetic(ref arith) if arith.ty != ArithOpType::And => {
                        // This shares quite a lot of code with flags below..
                        let left = ctrl.resolve(arith.left);
                        let right = ctrl.resolve(arith.right);
                        self.check_u8_instruction(ctrl, Some(dest), left, arith.left);
                        self.check_u8_instruction(ctrl, Some(dest), right, arith.right);
                        if self.mode == DatFuncAnalysisMode::ArrayIndex {
                            let new_left =
                                self.check_memory_read(ctrl, Some(dest), arith.left, left);
                            let new_right =
                                self.check_memory_read(ctrl, Some(dest), arith.right, right);
                            if new_left.is_some() || new_right.is_some() {
                                let left = new_left.unwrap_or(left);
                                let right = new_right.unwrap_or(right);
                                ctrl.skip_operation();
                                did_skip = true;
                                let state = ctrl.exec_state();
                                let new = ctx.arithmetic(arith.ty, left, right);
                                state.move_resolved(dest, new);
                            } else {
                                self.check_widened_pointer_add(ctrl, arith, left, right);
                            }
                        }
                    }
                    _ => {
                        let resolved = ctrl.resolve(val);
                        self.check_u8_instruction(ctrl, Some(dest), resolved, val);
                        if self.mode == DatFuncAnalysisMode::ArrayIndex {
                            let new = self.check_memory_read(ctrl, Some(dest), val, resolved);
                            if let Some(new) = new {
                                ctrl.skip_operation();
                                did_skip = true;
                                let state = ctrl.exec_state();
                                state.move_resolved(dest, new);
                            }
                        }
                    }
                }
                self.partial_register_moves.operation_move(ctrl, dest, val, did_skip);
            }
            Operation::SetFlags(arith)
                if arith.ty == FlagArith::Sub || arith.ty == FlagArith::And =>
            {
                let left = ctrl.resolve(arith.left);
                let right = ctrl.resolve(arith.right);
                self.check_u8_instruction(ctrl, None, left, arith.left);
                self.check_u8_instruction(ctrl, None, right, arith.right);

                if self.mode == DatFuncAnalysisMode::ArrayIndex {
                    let new_left = self.check_memory_read(ctrl, None, arith.left, left);
                    let new_right = self.check_memory_read(ctrl, None, arith.right, right);
                    if new_left.is_some() || new_right.is_some() {
                        let left = new_left.unwrap_or(left);
                        let right = new_right.unwrap_or(right);
                        ctrl.skip_operation();
                        let state = ctrl.exec_state();
                        let new_arith = FlagUpdate {
                            left,
                            right,
                            ty: arith.ty,
                            size: arith.size,
                        };
                        state.set_flags_resolved(&new_arith, None);
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve_va(dest) {
                    if self.mode == DatFuncAnalysisMode::FuncArg {
                        self.check_call_for_func_arg_widen(ctrl, dest, false);
                    }
                    if let Some(custom) = self.custom_value_for_call(dest) {
                        ctrl.skip_operation();
                        ctrl.set_register(0, custom);
                    }
                }
            }
            Operation::Jump { condition, to } => {
                let condition = ctrl.resolve(condition);
                if let Some(to) = ctrl.resolve_va(to) {
                    if let Err(e) = self.required_stable_addresses.add_jump_dest(binary, to) {
                        dat_warn!(
                            self, "Overlapping stable addresses {:?} for jump to {:?}", e, to,
                        );
                    }
                    if self.dat_ctx.rdtsc_tracker.check_rdtsc_jump(ctrl, condition, to) {
                        self.make_jump_unconditional(ins_address);
                        return;
                    }
                }
                // A bit hacky fix to register switch table locations to prevent certain
                // noreturn code from executing them.
                // Probably could be better to have analysis to recognize that noreturn
                // function instead of relying control flow from it reaching switch table.
                // NOTE: Copypasted to game::GameAnalyzer
                if let Some(mem) = ctrl.if_mem_word(to) {
                    let mem = ctrl.resolve_mem(mem);
                    let (index, base) = mem.address();
                    let index = index.if_arithmetic_mul_const(E::VirtualAddress::SIZE as u64);
                    if let Some(index) = index {
                        let exec_state = ctrl.exec_state();
                        if exec_state.value_limits(index).0 == 0 {
                            self.switch_table = E::VirtualAddress::from_u64(base);
                        }
                    }
                }
                if self.mode == DatFuncAnalysisMode::ArrayIndex {
                    self.check_array_limit_jump(ctrl, condition);
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        let address = ctrl.address();
        self.current_branch = address;
        if E::VirtualAddress::SIZE == 8 {
            self.instruction_verify_pos.reset(
                address,
                self.binary,
                &mut self.dat_ctx.instructions_needing_verify,
            );
        }
    }
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> DatReferringFuncAnalysis<'a, 'b, 'acx, 'e, E> {
    pub fn new(
        dat_ctx: &'a mut DatPatchContext<'b, 'acx, 'e, E>,
        text: &'e BinarySection<E::VirtualAddress>,
        required_stable_addresses: &'a mut RequiredStableAddresses<'acx, E::VirtualAddress>,
        entry: E::VirtualAddress,
        ref_address: E::VirtualAddress,
        mode: DatFuncAnalysisMode,
    ) -> DatReferringFuncAnalysis<'a, 'b, 'acx, 'e, E> {
        let binary = dat_ctx.binary;
        let bump = &dat_ctx.analysis.bump;
        DatReferringFuncAnalysis {
            dat_ctx,
            ref_address,
            needed_func_params: [None; 16],
            needed_func_results: Default::default(),
            needed_cfg_analysis: BumpVec::new_in(bump),
            result: EntryOf::Retry,
            binary,
            text,
            current_branch: entry,
            entry: entry,
            is_update_status_screen_tooltip: false,
            switch_table: E::VirtualAddress::from_u64(0),
            mode,
            required_stable_addresses,
            partial_register_moves: PartialRegisterMoves::new(),
            instruction_verify_pos: util::InsVerifyIter::empty(),
            state: Box::new(DatFuncAnalysisState {
                calls: bumpvec_with_capacity(64, bump),
                calls_reverse_lookup:
                    HashMap::with_capacity_and_hasher(64, Default::default()),
                u8_instruction_lists: InstructionLists {
                    heads: HashMap::with_capacity_and_hasher(32, Default::default()),
                    store: bumpvec_with_capacity(128, bump),
                    used_addresses:
                        HashSet::with_capacity_and_hasher(64, Default::default()),
                },
                next_cfg_custom_id: 0,
                stack_size_tracker: stack_analysis::StackSizeTracker::new(
                    entry,
                    binary,
                    bump,
                ),
                detect_tail_call: DetectTailCall::new(entry),
                pending_hooks: bumpvec_with_capacity(8, bump),
            }),
        }
    }

    pub fn rebuild(
        dat_ctx: &'a mut DatPatchContext<'b, 'acx, 'e, E>,
        text: &'e BinarySection<E::VirtualAddress>,
        required_stable_addresses: &'a mut RequiredStableAddresses<'acx, E::VirtualAddress>,
        state: Box<DatFuncAnalysisState<'acx, 'e, E>>,
        mode: DatFuncAnalysisMode,
    ) -> DatReferringFuncAnalysis<'a, 'b, 'acx, 'e, E> {
        let binary = dat_ctx.binary;
        let bump = &dat_ctx.analysis.bump;
        DatReferringFuncAnalysis {
            dat_ctx,
            ref_address: E::VirtualAddress::from_u64(0),
            needed_func_params: [None; 16],
            needed_func_results: Default::default(),
            needed_cfg_analysis: BumpVec::new_in(bump),
            result: EntryOf::Retry,
            binary,
            text,
            current_branch: E::VirtualAddress::from_u64(0),
            entry: E::VirtualAddress::from_u64(0),
            is_update_status_screen_tooltip: false,
            switch_table: E::VirtualAddress::from_u64(0),
            state,
            mode,
            required_stable_addresses,
            partial_register_moves: PartialRegisterMoves::new(),
            instruction_verify_pos: util::InsVerifyIter::empty(),
        }
    }

    /// If there's a conflict in a jump instruction then converts to IsJumpDest::No.
    fn add_required_stable_address_for_patch(
        &mut self,
        start: E::VirtualAddress,
        end: E::VirtualAddress,
    ) {
        match self.try_add_required_stable_address_for_patch(start, end) {
            Ok(()) => (),
            Err(e) => {
                dat_warn!(self, "Required stable address overlap: {:?} vs {:?}", e, (start, end));
            }
        }
    }

    fn try_add_required_stable_address_for_patch(
        &mut self,
        start: E::VirtualAddress,
        end: E::VirtualAddress,
    ) -> Result<(), (E::VirtualAddress, E::VirtualAddress)> {
        self.required_stable_addresses.try_add_for_patch(self.binary, start, end)
    }

    /// For DatFuncAnalysisMode::FuncArg.
    /// Widen any arguments that need widening to 32bit when calling function `dest`.
    fn check_call_for_func_arg_widen(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dest: E::VirtualAddress,
        is_tail_call: bool,
    ) {
        if let Some(&args) = self.dat_ctx.func_arg_widen_requests.get(&dest) {
            for (i, dat) in args.iter()
                .cloned()
                .enumerate()
                .filter_map(|x| Some((x.0, x.1?)))
            {
                let arg_cache = &self.dat_ctx.analysis.arg_cache;
                let arg_loc = if !is_tail_call {
                    arg_cache.on_call(i as u8)
                } else {
                    arg_cache.on_entry(i as u8)
                };
                let value = ctrl.resolve(arg_loc);
                self.dat_ctx.found_func_arg_widen_refs.insert(ctrl.address());
                self.check_func_argument(ctrl, arg_loc, value, dat);
            }
        }
    }

    fn custom_value_for_call(&mut self, dest: E::VirtualAddress) -> Option<Operand<'e>> {
        let text_end = self.text.virtual_address + self.text.virtual_size;
        if dest >= self.text.virtual_address && dest < text_end {
            let ctx = self.dat_ctx.analysis.ctx;
            let rva = Rva((dest.as_u64() - self.binary.base.as_u64()) as u32);
            let index = {
                let entry = self.state.calls_reverse_lookup.entry(rva);
                let new_id = self.state.calls.len() as u32;
                *entry.or_insert_with(|| new_id)
            };
            let custom = ctx.custom(index);
            if index == self.state.calls.len() as u32 {
                self.state.calls.push(rva);
            }
            return Some(custom);
        } else {
            // It's somewhat possible that the dest was meant to be written by
            // a child function.
        }
        None
    }

    /// Checks if the value is memory access of one of the dat arrays.
    /// If the array is being indexed with u8, marks the index value as something
    /// that needs all instructions accessing it to be widened to 32bit.
    ///
    /// Return some if the operation should be replaced with a new op using returned value
    /// in place of input value.
    #[must_use]
    fn check_memory_read(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dest_unresolved: Option<&DestOperand<'e>>,
        value_unresolved: Operand<'e>,
        value: Operand<'e>,
    ) -> Option<Operand<'e>> {
        let mem = match value.if_memory() {
            Some(s) => s,
            None => return None,
        };

        let size_bytes = mem.size.bits() / 8;
        let (index, base) = mem.address();
        let index = if index.is_undefined() || size_bytes == 1 {
            Some(index)
        } else {
            index.if_arithmetic_mul_const(size_bytes as u64)
        };
        let index = match index {
            Some(s) => s,
            None => return None,
        };
        let addr = E::VirtualAddress::from_u64(base);
        if let Some(&(dat, field_id)) = self.dat_ctx.array_lookup.get(&addr) {
            self.reached_array_ref_32(ctrl, addr);
            let array_itself_needs_widen = is_widened_dat_field(dat, field_id);
            if array_itself_needs_widen {
                // This instruction can be array indexed read (the usual case; Default),
                // but also case where the indexed variable was spilled to stack and
                // read back (StackAccess)
                let widen_mode = Self::select_widen_mode_array_index(
                    ctrl,
                    dest_unresolved,
                    value_unresolved,
                    addr,
                    dat,
                    field_id,
                );
                self.widen_instruction(ctrl.address(), widen_mode);
            }
            if dat == DatType::Orders {
                // Probs never reason to increase order limit
                return None;
            }
            // Only care about patches if there's an assumption about byte-sized
            // access
            if index.relevant_bits() == (0..8) {
                // Determine what kind of operand is being used as the index.
                // Arguments, function return values, and undefined values will
                // be marked for widening, then there are few ones that are expected
                // but won't be widened, otherwise this adds a warning.
                return self.reached_widen_value(ctrl, index, dat);
            }
        }
        None
    }

    /// Common implementation of select_widen_mode / select_widen_mode_array_index
    fn select_widen_mode_inner(
        ctrl: &mut Control<'e, '_, '_, Self>,
        write: Option<&DestOperand<'e>>,
        read: Operand<'e>,
        array_addr: E::VirtualAddress,
    ) -> (WidenInstruction, Option<BaseIndexRegs>) {
        let mut base_idx = None;
        for i in 0..2 {
            // Iteration 0: Value if memory, 1: Dest if memory
            // Assuming that if both are memory value takes priority.
            // Usually on x86 they're same, though `push dword[x]` will
            // write to [esp - 4] and read from [x], and we care about the
            // read.
            // (Is it fine that `push ecx` would be detected as widen req to [esp - 4]`?
            // Think it's fine and will be just no-op)
            let unres = if i == 0 {
                match read.if_memory() {
                    Some(s) => s,
                    None => continue,
                }
            } else {
                match write {
                    Some(DestOperand::Memory(mem)) => mem,
                    _ => continue,
                }
            };
            (|| {
                let (addr_var, addr_const) = unres.address();
                let (l, r) = addr_var.if_arithmetic_add()?;
                let l = l.if_register()?;
                let r = r.if_register()?;
                let l_val = ctrl.resolve_register(l);
                let r_val = ctrl.resolve_register(r);
                let expected_base = if addr_const == 0 {
                    // Assuming [r1 + r2]
                    // where one reg is index, and other is `exe_base + dat_array_offset`
                    array_addr.as_u64()
                } else {
                    // Assuming [r1 + r2 + dat_array_offset]
                    // where one is index, and other is exe_base
                    ctrl.binary().base().as_u64()
                };
                if l_val.if_constant() == Some(expected_base) {
                    base_idx = Some(BaseIndexRegs {
                        base: l,
                        index: r,
                    });
                } else if r_val.if_constant() == Some(expected_base) {
                    base_idx = Some(BaseIndexRegs {
                        base: r,
                        index: l,
                    });
                }
                Some(())
            })();
            let resolved = ctrl.resolve_mem(unres);
            let ctx = ctrl.ctx();
            let esp = ctx.register(4);
            // Assuming that if first iteration gives memory address, checking
            // the second value isn't necessary.
            let (base, offset) = resolved.address();
            if base == esp {
                let offset = offset.wrapping_sub(unres.address().1);
                if let Ok(offset) = i32::try_from(offset as i64) {
                    return (WidenInstruction::StackAccess(offset), None);
                }
            }
        }
        (WidenInstruction::Default, base_idx)
    }

    /// Both write and read value have to be unresolved.
    /// If these refer to stack memory, return WidenInstruction::StackAccess
    ///
    /// Similar to CfgAnalyzer::set_assigning_instruction, other than only needing
    /// one layer of resolving.
    fn select_widen_mode(
        ctrl: &mut Control<'e, '_, '_, Self>,
        write: Option<&DestOperand<'e>>,
        read: Operand<'e>,
    ) -> WidenInstruction {
        Self::select_widen_mode_inner(ctrl, write, read, E::VirtualAddress::from_u64(0)).0
    }

    /// Like select_widen_mode, but instead of Default / StackAaccess
    /// returns ArrayIndex / StackAccess.
    fn select_widen_mode_array_index(
        ctrl: &mut Control<'e, '_, '_, Self>,
        write: Option<&DestOperand<'e>>,
        read: Operand<'e>,
        array_addr: E::VirtualAddress,
        dat: DatType,
        field_id: u8,
    ) -> WidenInstruction {
        match Self::select_widen_mode_inner(ctrl, write, read, array_addr) {
            (WidenInstruction::Default, base_idx) => {
                WidenInstruction::ArrayIndex(array_addr.as_u64(), dat, field_id, base_idx)
            }
            (mode, _) => mode,
        }
    }

    /// Patches x > array_limit jumps to not jump / only check for equivalency
    /// if array_limit == None.
    /// Condition has to be resolved.
    fn check_array_limit_jump(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        condition: Operand<'e>,
    ) {
        let make_jump_unconditional = condition.if_arithmetic_gt()
            .and_then(|(l, r)| {
                // limit > value should be converted to always jump
                l.if_constant()
                    .and_then(|c| {
                        let (right_inner, mask) = Operand::and_masked(r);
                        Some(()).and_then(|()| {
                            // Check signed comparisions
                            if let Some((add_l, add_r)) = right_inner.if_arithmetic_add() {
                                // `8000_0050 > (x + 8000_0000) & ffff_ffff`
                                // is signed 50 > x
                                let add_r = add_r.if_constant()?;
                                if add_r == mask.wrapping_add(1) >> 1 {
                                    let c = c.checked_sub(add_r)?;
                                    let dat = entry_limit_to_dat(c.try_into().ok()?)?;
                                    return Some((true, add_l, dat));
                                }
                            } else if let Some((sub_l, sub_r)) = right_inner.if_arithmetic_sub() {
                                // 7fff_ffaf > (x - 51)
                                // is signed x > 50
                                // (7fff_ffaf + 51 == 8000_0000)
                                let sub_r = sub_r.if_constant()?;
                                let sum = sub_r.wrapping_add(c);
                                if matches!(sum, 0x8000 | 0x8000_0000 | 0x8000_0000_0000_0000) {
                                    // Catch signed comparision (value > last_valid)
                                    // c = last_valid + 1, but since entry_limit_to_dat
                                    // takes last_valid + 1 too, just pass c directly there
                                    let dat = entry_limit_to_dat(sub_r.try_into().ok()?)?;
                                    return Some((false, sub_l, dat));
                                }
                            }
                            None
                        }).or_else(|| {
                            if right_inner.if_sub_with_const().is_some() {
                                // c1 > (x - c2) is a range check,
                                // assuming that you never get dat id by subtracting a
                                // constant and then checking if it's less than invalid
                                // Repair order check does check 0x6a..0x80 range which
                                // shouldn't be (just) removed
                                return None;
                            }
                            let dat = entry_limit_to_dat(c.try_into().ok()?)?;
                            Some((true, r, dat))
                        })
                    })
                    .or_else(|| {
                        if l.if_sub_with_const().is_some() {
                            // Range check
                            return None;
                        }
                        // value > last_valid should never jump
                        let c = r.if_constant()?;
                        let c = u32::try_from(c).ok()?
                            .wrapping_add(1);
                        let dat = entry_limit_to_dat(c)?;
                        Some((false, l, dat))
                    })
            });
        if let Some((jump, op, (dat, first_invalid_is_none))) = make_jump_unconditional {
            // TODO currently just assumes that those above constant checks are always
            // dat limit checks

            let address = ctrl.address();
            // Hackfix for step_lone_sprites, which does a lone.sprite.id > 0x81
            // check
            if dat == DatType::Weapons {
                let skip = op.if_mem16_offset(u64::from(E::VirtualAddress::SIZE) * 2)
                    .and_then(|x| ctrl.if_mem_word(x))
                    .is_some();
                if skip {
                    return;
                }
            }
            match (jump, first_invalid_is_none) {
                (true, false) => self.make_jump_unconditional(address),
                (true, true) => self.make_jump_eq_neq(address, false),
                (false, false) => self.nop(address),
                (false, true) => self.make_jump_eq_neq(address, true),
            }
        }
    }

    fn check_func_argument(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        location_unresolved: Operand<'e>,
        orig_value: Operand<'e>,
        dat: DatType,
    ) {
        fn get_8bit_from_ors<'e>(value: Operand<'e>) -> Operand<'e> {
            match value.if_arithmetic_or() {
                Some((l, r)) => {
                    let l = get_8bit_from_ors(l);
                    if l.relevant_bits().start >= 8 && r.relevant_bits().end <= 8 {
                        r
                    } else if r.relevant_bits().start >= 8 && l.relevant_bits().end <= 8 {
                        l
                    } else {
                        value
                    }
                }
                None => value,
            }
        }

        fn is_non_global_mem8<'e>(value: Operand<'e>) -> bool {
            match value.if_mem8() {
                Some(s) => s.if_constant_address().is_none(),
                None => false,
            }
        }

        let value_no_word_mask = if E::VirtualAddress::SIZE == 4 {
            match orig_value.if_and_with_const() {
                Some((s, mask)) => {
                    if (s.relevant_bits_mask() & !mask) as u32 == 0 {
                        // Masks out only high half of u64, mask
                        // should be removable for these purposes(?)
                        // Or maybe should only remove such mask
                        // when get_8bit_from_ors returns a 8bit value,
                        // and keep the mask otherwise?
                        s
                    } else {
                        orig_value
                    }
                }
                None => orig_value,
            }
        } else {
            orig_value
        };
        let value = get_8bit_from_ors(value_no_word_mask);
        if value != value_no_word_mask || value.is_undefined() || is_non_global_mem8(value) {
            self.needed_cfg_analysis.push((
                self.current_branch,
                ctrl.address(),
                Some(location_unresolved),
                dat,
            ));
        }
        // Widening constants is pointless
        if value.if_constant().is_some() {
            return;
        }
        // Note: Unlike dat array indexing, for function args we want to
        // check even ones wider than 8 bits, as the code can implicitly assume
        // that the high bits aren't going to be used and use 32-bit instructions.
        //
        // Either way unwrap cases where there's an or of two values, with only one
        // being 8 bit
        self.reached_widen_value(ctrl, value, dat);
    }

    fn reached_widen_value(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        value: Operand<'e>,
        dat: DatType,
    ) -> Option<Operand<'e>> {
        match self.reached_widen_value_main(ctrl, value, dat) {
            Ok(o) => o,
            Err(()) => {
                dat_warn!(
                    self, "Unknown {:?} dat offset @ {:?}: {}",
                    dat, ctrl.address(), format_stable_undef(value),
                );
                None
            }
        }
    }

    fn reached_widen_value_main(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        value: Operand<'e>,
        dat: DatType,
    ) -> Result<Option<Operand<'e>>, ()> {
        let ctx = ctrl.ctx();
        let is_local = value.if_memory()
            .filter(|x| {
                let (base, offset) = x.address();
                (-0x2000..0).contains(&(offset as i32)) && base == ctx.register(4)
            })
            .is_some();
        let is_undef = Operand::and_masked(value).0.is_undefined();
        if is_local || is_undef {
            // Accessing u8 which is result from 2 branches merging to undefined.
            // Consider the following, with `cl` being the index
            //     movzx ecx, cl
            //     mov eax, [weapons_dat_damage + ecx * 2]
            //     cmp eax, 50
            //     ...
            // We want to only care about the line where the memory is only read,
            // as that's the last point of at which u8 index will be relevant,
            // and do CFG analysis backwards from that. To do that, store a CFG
            // analysis request and assign dest using Custom(0x1000_0000 | new_id)
            // instead of the undef value, so that later operations won't be caught
            // by the undefined check.
            self.needed_cfg_analysis.push((self.current_branch, ctrl.address(), None, dat));
            let new_op = ctx.custom(0x1000_0000 | self.state.next_cfg_custom_id);
            self.state.next_cfg_custom_id += 1;
            return Ok(Some(new_op));
        }

        // -- Check arguments and struct offsets --
        if let Some(mem) = value.if_memory() {
            let (base, offset) = mem.address();
            return self.check_mem_widen_value(ctrl, base, offset, mem.size, dat)
                .map(|()| None);
        }
        // -- Check 64bit register args --
        if E::VirtualAddress::SIZE == 8 {
            let reg = value.if_arithmetic_and()
                .and_then(|(l, r)| {
                    r.if_constant()?;
                    l.if_register()
                })
                .or_else(|| value.if_register());
            if let Some(reg) = reg {
                let arg_n = match reg {
                    1 => 0,
                    2 => 1,
                    8 => 2,
                    9 => 3,
                    _ => return Err(()),
                };
                self.needed_func_params[arg_n] = Some(dat);
                return Ok(None);
            }
        }
        // -- Check return value --
        let custom = value.if_arithmetic_and_const(0xff)
            .or_else(|| value.if_arithmetic_and_const(0xffff_ffff))
            .unwrap_or(value)
            .if_custom();
        if let Some(custom) = custom {
            // If the high byte is 0x1000_0000 then it was added as a cfg request earlier.
            if custom & 0xf000_0000 == 0 {
                let rva = self.state.calls[custom as usize];
                if self.dat_ctx.funcs_added_for_retval_patch.insert(rva) {
                    self.dat_ctx.funcs_needing_retval_patch.push(rva);
                }
                self.needed_func_results.insert(custom);
            }
            return Ok(None);
        }
        Err(())
    }

    fn is_status_screen_data(&self, op: Operand<'e>) -> bool {
        // Mem32[arg1 + 0x40]
        let arg_cache = &self.dat_ctx.analysis.arg_cache;
        op.if_memory()
            .filter(|mem| mem.size == E::WORD_SIZE)
            .and_then(|mem| {
                mem.if_offset(E::struct_layouts().control_ptr_value())
            })
            .filter(|&base| base == arg_cache.on_entry(0))
            .is_some()
    }

    fn check_mem_widen_value(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        base: Operand<'e>,
        offset: u64,
        size: MemAccessSize,
        dat: DatType,
    ) -> Result<(), ()> {
        let ctx = ctrl.ctx();
        let is_stack = base == ctx.register(4);
        if is_stack {
            if let Some(arg) = arg_n_from_offset::<E>(offset).map(|x| x as usize) {
                if arg < self.needed_func_params.len() {
                    self.needed_func_params[arg] = Some(dat);
                }
            }
            return Ok(());
        }
        if size == MemAccessSize::Mem8 {
            if offset == E::struct_layouts().bullet_weapon_id() &&
                dat == DatType::Weapons
            {
                // Most likely Bullet.weapon_id, todo
                return Ok(());
            } else if offset == E::struct_layouts().unit_current_tech() &&
                dat == DatType::TechData
            {
                // Unit.building_union.current_tech, todo
                return Ok(());
            } else if offset == E::struct_layouts().unit_current_upgrade() &&
                dat == DatType::Upgrades
            {
                // Unit.building_union.current_upgrade, todo
                return Ok(());
            } else if offset == E::struct_layouts().status_screen_stat_dat() &&
                dat == DatType::Weapons && self.is_status_screen_data(base)
            {
                // This is a bit hacky, especially limiting to only ArrayIndex,
                // but without it this would quit too eagerly in func
                // arg analysis and cause extra work in the end.
                if self.mode == DatFuncAnalysisMode::ArrayIndex {
                    self.is_update_status_screen_tooltip = true;
                    self.result = EntryOf::Ok(());
                }
                return Ok(());
            }
            if offset == 1 && (dat == DatType::Upgrades || dat == DatType::TechData) {
                // Tech/upgrade net commands read at arg1[1]
                let arg_cache = &self.dat_ctx.analysis.arg_cache;
                if base == arg_cache.on_entry(0) {
                    return Ok(());
                }
            }
            let expected_dat = Some(offset)
                .filter(|&x| x > 0x1000)
                .map(|x| E::VirtualAddress::from_u64(x))
                .filter(|&x| {
                    let ok = self.dat_ctx.array_lookup.get(&x)
                        .is_some_and(|x| is_widened_dat_field(x.0, x.1));
                    if ok {
                        return true;
                    }
                    // There are also hardcoded reads to nonhero tank turret
                    // weapons
                    let units_dat = &self.dat_ctx.units;
                    self.binary
                        .read_address(units_dat.table_address + 0x11 * units_dat.entry_size)
                        .ok()
                        .filter(|&ground_weapon| {
                            x == ground_weapon + 0x6 || x == ground_weapon + 0x1f
                        })
                        .is_some()
                })
                .is_some();
            if expected_dat {
                return Ok(());
            }
            // step_iscript has Mem8[iscript_ptr] dereferences
            if self.entry == self.dat_ctx.step_iscript {
                return Ok(());
            }
            // There's one expected constant mem address that can stay u8.
            // It is only assigned hardcoded spell weapon ids (It's a
            // for_each_unit_in_area callback or such)
            if base.if_constant() == Some(0) && dat == DatType::Weapons {
                let addr = E::VirtualAddress::from_u64(offset);
                self.dat_ctx.unknown_global_u8_mem.insert(addr, ctrl.address());
                return Ok(());
            }
            Err(())
        } else {
            Ok(())
        }
    }

    /// Checks for array refs that check_memory_read isn't expected to catch.
    fn check_array_ref(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, val: Operand<'e>) {
        if let Some(c) = val.if_constant() {
            self.check_array_ref_const(ctrl, c);
        }
    }

    fn check_array_ref_const(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, val: u64) {
        if val > 0x10000 {
            let addr = E::VirtualAddress::from_u64(val);
            if self.dat_ctx.array_lookup.contains_key(&addr) {
                self.reached_array_ref_32(ctrl, addr);
            }
        }
    }

    fn reached_array_ref_32(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        array_addr: E::VirtualAddress,
    ) {
        if let Some(imm_addr) = reloc_address_of_instruction(ctrl, self.binary, array_addr) {
            let rva = Rva((imm_addr.as_u64() - self.binary.base.as_u64()) as u32);
            self.dat_ctx.unchecked_refs.remove(rva);
        }
    }

    /// Checks if this Operation::Move is doing
    /// `dat_array + index` on dat array that used u8 indices but will now be widened to u32,
    /// and adds patch on the instruction to multiply index register by 4 before adding
    /// (And then return it back to what it was)
    fn check_widened_pointer_add(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        arith_unres: &ArithOperand<'e>,
        resolved_left: Operand<'e>,
        resolved_right: Operand<'e>,
    ) {
        if arith_unres.ty != ArithOpType::Add {
            return;
        }
        if let Some((c, _)) = Operand::either(resolved_left, resolved_right, |x| x.if_constant()) {
            let addr = E::VirtualAddress::from_u64(c);
            if addr > self.binary.base() {
                if let Some(&(dat, field_id)) = self.dat_ctx.array_lookup.get(&addr) {
                    if is_widened_dat_field(dat, field_id) {
                        self.widen_pointer_add(ctrl, dat, field_id);
                    }
                }
            }
        }
    }

    fn generate_needed_patches(
        &mut self,
        analysis: FuncAnalysis<'e, E, analysis::DefaultState>,
        entry: E::VirtualAddress,
    ) {
        if self.is_update_status_screen_tooltip {
            self.dat_ctx.result.patches.push(
                DatPatch::ReplaceFunc(self.entry, DatReplaceFunc::UpdateStatusScreenTooltip),
            );
            self.dat_ctx.update_status_screen_tooltip = self.entry;
            return;
        }
        let bump = &self.dat_ctx.analysis.bump;
        let needed_cfg_analysis = mem::replace(
            &mut self.needed_cfg_analysis,
            BumpVec::new_in(bump),
        );
        if !needed_cfg_analysis.is_empty() {
            let mut cfg = analysis.finish();
            let mut checked_addresses = bumpvec_with_capacity(needed_cfg_analysis.len(), bump);
            let predecessors = cfg.predecessors();
            for (branch_start, address, op, dat) in needed_cfg_analysis {
                let key = (address, branch_start, op);
                if !checked_addresses.contains(&key) {
                    checked_addresses.push(key);
                    self.do_cfg_analysis(
                        &mut cfg,
                        &predecessors,
                        entry,
                        branch_start,
                        address,
                        op,
                        dat,
                    );
                }
            }
        }
        self.generate_noncfg_patches();
    }

    fn generate_noncfg_patches(&mut self) {
        let binary = self.binary;
        let bump = &self.dat_ctx.analysis.bump;
        let needed_func_params = self.needed_func_params;
        let needed_func_results = mem::replace(&mut self.needed_func_results, Default::default());
        let u8_instruction_lists = mem::replace(
            &mut self.state.u8_instruction_lists,
            InstructionLists {
                heads: Default::default(),
                store: BumpVec::new_in(bump),
                used_addresses: Default::default(),
            },
        );
        for (i, dat) in needed_func_params.iter()
            .enumerate()
            .filter_map(|x| Some((x.0, (*x.1)?)))
        {
            self.dat_ctx.add_func_arg_widening_request(self.entry, i as u8, dat);
            for (rva, widen_mode) in u8_instruction_lists.iter(U8Operand::Arg(i as u8)) {
                let address = binary.base + rva.0;
                self.widen_instruction(address, widen_mode);
            }
        }
        for &custom_id in needed_func_results.iter() {
            // Func args may be added for extension unnecessarily
            for (rva, widen_mode) in u8_instruction_lists.iter(U8Operand::Return(custom_id)) {
                let address = binary.base + rva.0;
                self.widen_instruction(address, widen_mode);
            }
        }
        self.state.u8_instruction_lists = u8_instruction_lists;
    }

    fn do_cfg_analysis(
        &mut self,
        cfg: &mut Cfg<'e, E, analysis::DefaultState>,
        predecessors: &scarf::cfg::Predecessors,
        entry: E::VirtualAddress,
        branch: E::VirtualAddress,
        final_address: E::VirtualAddress,
        needed_operand: Option<Operand<'e>>,
        dat: DatType,
    ) {
        // Slower analysis which is able to find instructions that need to be patched
        // even if the final index that was being used to access .dat can be result
        // of multiple branches.
        let binary = self.binary;
        let ctx = self.dat_ctx.analysis.ctx;
        let bump = &self.dat_ctx.analysis.bump;
        // This may(?) infloop under certain conditions, so have a hard limit of
        // branches to go through before quitting.
        let mut limit = 64;
        let mut analyzer = CfgAnalyzer {
            branch,
            final_address,
            func_entry: entry,
            needed_operand,
            resolved_dest_address: None,
            unchecked_branches: bumpvec_with_capacity(32, bump),
            added_unchecked_branches: HashSet::with_capacity_and_hasher(32, Default::default()),
            parent: self,
            instruction_lists: InstructionLists {
                heads: HashMap::with_capacity_and_hasher(32, Default::default()),
                store: bumpvec_with_capacity(128, bump),
                used_addresses:
                    HashSet::with_capacity_and_hasher(64, Default::default()),
            },
            cfg,
            predecessors,
            assign_instruction_widen_request: None,
            rerun_branch: None,
            ending: false,
            dat,
            ctx,
        };
        let orig_branch = branch;
        let orig_final = final_address;

        let mut analysis = FuncAnalysis::new(binary, ctx, branch);
        analysis.analyze(&mut analyzer);
        while let Some((branch, operand, final_address, resolved_dest)) =
            analyzer.unchecked_branches.pop()
        {
            if limit == 0 {
                dat_warn!(
                    self, "CFG analysis of {:?} / {:?} took too long", orig_branch, orig_final,
                );
                break;
            }
            limit -= 1;
            analyzer.branch = branch;
            analyzer.needed_operand = Some(operand);
            analyzer.instruction_lists.clear();
            analyzer.final_address = final_address;
            analyzer.resolved_dest_address = resolved_dest;
            analyzer.ending = false;
            let mut analysis = FuncAnalysis::new(binary, ctx, branch);
            analysis.analyze(&mut analyzer);
        }
    }

    fn make_jump_eq_neq(&mut self, address: E::VirtualAddress, eq: bool) {
        if !self.dat_ctx.patched_addresses.insert(address) {
            return;
        }

        let bytes = match self.binary.slice_from_address(address, 0x10) {
            Ok(o) => o,
            Err(_) => {
                dat_warn!(self, "Can't uncond @ {:?}", address);
                return;
            }
        };

        assert!(bytes.len() == 0x10);
        let cond_id = if eq { 0x4 } else { 0x5 };
        if bytes[0] == 0x0f && matches!(bytes[1], 0x80 ..= 0x8f) {
            let mut patch = [0u8; 6];
            for i in 0..6 {
                patch[i] = bytes[i];
            }
            patch[1] = 0x80 + cond_id;
            self.add_patch(address, &patch, 6);
        } else if matches!(bytes[0], 0x70 ..= 0x7f) {
            self.add_patch(address, &[0x70 + cond_id, bytes[1]], 2);
        } else {
            dat_warn!(self, "Can't uncond @ {:?}", address);
        }
    }

    fn make_jump_unconditional(&mut self, address: E::VirtualAddress) {
        if !self.dat_ctx.patched_addresses.insert(address) {
            return;
        }

        let bytes = match self.binary.slice_from_address(address, 0x10) {
            Ok(o) => o,
            Err(_) => {
                dat_warn!(self, "Can't uncond @ {:?}", address);
                return;
            }
        };
        assert!(bytes.len() == 0x10);

        if bytes[0] == 0x0f && matches!(bytes[1], 0x80 ..= 0x8f) {
            self.add_patch(address, &[0x90, 0xe9, bytes[2], bytes[3], bytes[4], bytes[5]], 6);
        } else if matches!(bytes[0], 0x70 ..= 0x7f) {
            self.add_patch(address, &[0xeb, bytes[1]], 2);
        } else {
            dat_warn!(self, "Can't uncond @ {:?}", address);
        }
    }

    fn nop(&mut self, address: E::VirtualAddress) {
        if !self.dat_ctx.patched_addresses.insert(address) {
            return;
        }
        let ins_len = match instruction_length(self.binary, address) {
            Some(s) => s,
            None => return,
        };
        let nops = [0x90; 0x10];
        self.add_patch(address, &nops[..ins_len as usize], ins_len);
    }

    fn widen_instruction(&mut self, address: E::VirtualAddress, mode: WidenInstruction) {
        let is_struct_field_rm = |bytes: &[u8]| -> bool {
            mode == WidenInstruction::Default &&
                bytes[1] & 0xc0 != 0xc0
        };

        if !self.dat_ctx.patched_addresses.insert(address) {
            return;
        }

        let mut full_bytes = [0x90u8; 16];
        let (rex_off, bytes, ins_len) =
            match self.init_instruction_patch(address, &mut full_bytes)
        {
            Some(s) => s,
            None => return,
        };
        let rex_off = rex_off as usize;
        match *bytes {
            // movzx to mov
            [0x0f, 0xb6, ..] => {
                if !is_struct_field_rm(&bytes[1..]) {
                    if rex_off == 0 {
                        full_bytes[1] = 0x8b;
                    } else {
                        if full_bytes[0] == 0x40 {
                            // Not adding unnecessary 0x40 REX prefix
                            // (It may have been necessary for accessing sil or
                            // such new low register, but unnecessary with u32-u32 move)
                            full_bytes[1] = 0x90;
                        } else {
                            full_bytes[1] = full_bytes[0];
                        }
                        full_bytes[2] = 0x8b;
                    }
                    full_bytes[0] = 0x90;
                    self.add_rm_patch(
                        address,
                        &mut full_bytes,
                        rex_off + 1,
                        ins_len,
                        ins_len,
                        mode,
                    );
                }
            }
            // add rm8, r8; cmp r8, rm8; cmp rm8, r8
            [0x00, ..] | [0x3a, ..] | [0x38, ..] => {
                if !is_struct_field_rm(&bytes[..]) {
                    bytes[0] += 1;
                    self.add_rm_patch(
                        address,
                        &mut full_bytes,
                        rex_off,
                        ins_len,
                        ins_len,
                        mode,
                    );
                }
            }
            // cmp al, constant u8
            // I think it's safe to assume it's never going to be a signed gt/lt
            [0x3c, ..] => {
                bytes[0] = 0x3d;
                bytes[2] = 0x00;
                bytes[3] = 0x00;
                bytes[4] = 0x00;
                self.add_hook(address, ins_len, &full_bytes[..(rex_off + 5)]);
            }
            // arith rm32, const8
            [0x80, ..] => {
                bytes[0] = 0x81;
                for i in ins_len..(ins_len + 3) {
                    full_bytes[i as usize] = 0x00;
                }
                self.add_rm_patch(
                    address,
                    &mut full_bytes,
                    rex_off,
                    ins_len + 3,
                    ins_len,
                    mode,
                );
            }
            // test rm8, r8
            [0x84, second, ..] => {
                // Going to only support test r8low with itself for now
                if second & 0xc0 == 0xc0 && second & 0x7 == (second >> 3) & 0x7 {
                    bytes[0] = 0x85;
                    self.add_patch(address, &full_bytes, ins_len);
                }
            }
            // mov r8, rm8, to mov r32, rm32
            [0x8a, ..] => {
                if is_struct_field_rm(&bytes[..]) {
                    // Convert to movzx r32, rm8
                    full_bytes.copy_within(rex_off..15, rex_off + 1);
                    full_bytes[rex_off + 0] = 0x0f;
                    full_bytes[rex_off + 1] = 0xb6;
                    self.add_hook(address, ins_len, &full_bytes[..ins_len as usize + 1]);
                } else {
                    bytes[0] = 0x8b;
                    self.add_rm_patch(
                        address,
                        &mut full_bytes,
                        rex_off,
                        ins_len,
                        ins_len,
                        mode,
                    );
                }
            }
            // mov rm8, r8
            [0x88, ..] => {
                if !is_struct_field_rm(&bytes[..]) {
                    bytes[0] = 0x89;
                    self.add_rm_patch(
                        address,
                        &mut full_bytes,
                        rex_off,
                        ins_len,
                        ins_len,
                        mode,
                    );
                }
            }
            // mov rm8, const8
            [0xc6, ..] => {
                if !is_struct_field_rm(&bytes[..]) {
                    bytes[0] = 0xc7;
                    for i in ins_len..(ins_len + 3) {
                        full_bytes[i as usize] = 0x00;
                    }
                    self.add_rm_patch(
                        address,
                        &mut full_bytes,
                        rex_off,
                        ins_len + 3,
                        ins_len,
                        mode,
                    );
                }
            }
            // mov r8, const8
            [0xb0..=0xb7, ..] => {
                bytes[0] += 8;
                bytes[2] = 0;
                bytes[3] = 0;
                bytes[4] = 0;
                self.add_hook(address, ins_len, &full_bytes[..ins_len as usize + 3]);
            }
            // Already u32 cmp
            [0x3d, ..] => (),
            // Already u32 arith
            [0x03, ..] | [0x81, ..] | [0x83, ..] => (),
            // Lea
            [0x8d, ..] => (),
            // Already u32 moves
            [0x89, ..] | [0xc7, ..] => (),
            // Push, pop reg
            [x, ..] if x >= 0x50 && x < 0x60 => (),
            // mov r32, rm32
            [0x8b, ..] => {
                // add_rm_patch_if_stack_relocated assumes rm instruction start 0 atm
                // Also not sure if the ebp relocation is useful in 64bit so leaving this
                // only for non-rex opcodes for now.
                if let WidenInstruction::StackAccess(offset) = mode {
                    if rex_off == 0 {
                        self.add_rm_patch_if_stack_relocated(
                            address,
                            &full_bytes[..(ins_len as usize)],
                            offset,
                        );
                    }
                }
            }
            // Push any
            [0xff, x, ..] if (x >> 3) & 7 == 6 => {
                if let WidenInstruction::StackAccess(offset) = mode {
                    if rex_off == 0 {
                        self.add_rm_patch_if_stack_relocated(
                            address,
                            &full_bytes[..(ins_len as usize)],
                            offset,
                        );
                    }
                }
            }
            // Movzx from u16
            [0x0f, 0xb7, ..] => (),
            // Hoping that u16 is fine
            [0x66, ..] => (),
            _ => dat_warn!(self, "Can't widen instruction @ {:?}", address),
        }
    }

    // For instructions which read from rm but are already u32 wide.
    // They still may use an address that should be relocated, so relocate
    // them by calling add_rm_patch if it's using [ebp - x].
    //
    // (Mode is implicitly considered to be WidenInstruction::StackAccess)
    fn add_rm_patch_if_stack_relocated(
        &mut self,
        address: E::VirtualAddress,
        patch: &[u8],
        stack_offset: i32,
    ) {
        let rm_byte = match patch.get(1) {
            Some(&s) => s,
            None => return,
        };
        let base = rm_byte & 0x7;
        let variant = rm_byte >> 6;
        if (variant == 1 || variant == 2) && base == 5 {
            let offset = if variant == 1 {
                patch[2] as i8 as i32
            } else {
                LittleEndian::read_u32(&patch[2..]) as i32
            };
            if offset > 0 && offset & 3 == 0 {
                // [ebp + x] and already aligned to 4
                return;
            }

            // [ebp - x]
            let mut copy = [0; 16];
            for i in 0..patch.len().min(16) {
                copy[i] = patch[i];
            }
            let mode = WidenInstruction::StackAccess(stack_offset);
            self.add_rm_patch(address, &mut copy, 0, patch.len() as u8, patch.len() as u8, mode);
        } else if variant < 3 {
            // TODO non ebp offsets / ebp with no offset
            dat_warn!(self, "Unimplemented stack rm patch at {address:?}, base {base:x}");
        }
    }

    fn add_rm_patch(
        &mut self,
        address: E::VirtualAddress,
        patch: &mut [u8; 16],
        start: usize,
        patch_len: u8,
        ins_len: u8,
        mode: WidenInstruction,
    ) {
        if start > 8 || patch_len >= 16 {
            return;
        }
        let idx_1 = start.wrapping_add(1);
        let idx_2 = start.wrapping_add(2);
        let idx_3 = start.wrapping_add(3);
        let base = patch[idx_1] & 0x7;
        let variant = (patch[idx_1] & 0xc0) >> 6;
        if matches!(mode, WidenInstruction::ArrayIndex(..)) == false || variant == 3 {
            let mut patch_len = patch_len;
            // Fix u8 [ebp - x] offset to a newly allocated u32
            if let WidenInstruction::StackAccess(reg_offset) = mode {
                if variant == 1 || variant == 2 {
                    let imm_offset = if base == 4 { idx_3 } else { idx_2 };
                    let const_off = &patch[imm_offset..];
                    let offset = if variant == 1 {
                        const_off[0] as i8 as i32
                    } else {
                        LittleEndian::read_i32(const_off)
                    };
                    let entry_rel_offset = offset.wrapping_add(reg_offset);
                    if entry_rel_offset >= 0 {
                        // Don't reallocate func arguments, but still align them to 4
                        // The argument slots may be used for temps later, but assuming
                        // that conflicts there are rare enough to not be relevant.
                        patch[imm_offset] &= 0xfc;
                    } else {
                        if base == 4 {
                            let sib = patch[idx_2];
                            // Verify that this is just [ESP + const]
                            if sib != 0x24 {
                                // Technically should also check that rex & 2 == 0, as otherwise
                                // 0x24 means r12 index
                                dat_warn!(
                                    self, "Don't know how to patch multi-reg SIB {address:?}",
                                );
                                return;
                            }
                        }
                        let new_offset = match
                            self.state.stack_size_tracker.remap_stack_offset(offset, reg_offset)
                        {
                            Some(s) => s,
                            None => {
                                dat_warn!(
                                    self, "Unable to remap stack pointer offset @ {address:?}",
                                );
                                return;
                            }
                        };
                        if let Ok(new_offset) = i8::try_from(new_offset) {
                            patch[idx_1] = (patch[idx_1] & !0xc0) | 0x40;
                            patch[imm_offset] = new_offset as u8;
                            if variant == 2 {
                                // If there's another constant after offset imm,
                                // move it from imm32 offset to imm8 offset
                                let rest = LittleEndian::read_u32(&patch[(imm_offset + 4)..]);
                                LittleEndian::write_u32(&mut patch[(imm_offset + 1)..], rest);
                            }
                            if variant == 2 {
                                patch_len = patch_len.wrapping_sub(3);
                            }
                        } else {
                            patch[idx_1] = (patch[idx_1] & !0xc0) | 0x80;
                            LittleEndian::write_i32(&mut patch[imm_offset..], new_offset);
                            if variant == 1 {
                                // If there's another constant after offset imm,
                                // move it from imm8 offset to imm32 offset
                                let rest = LittleEndian::read_u32(&patch[(imm_offset + 1)..]);
                                LittleEndian::write_u32(&mut patch[(imm_offset + 4)..], rest);
                            }
                            if variant == 1 {
                                patch_len = patch_len.wrapping_add(3);
                            }
                        }
                    }
                } else if variant < 3 {
                    // TODO non ebp offsets / ebp with no offset
                    dat_warn!(self, "Unimplemented rm patch at {address:?}, base {base:x} {reg_offset:x}");
                    return;
                }
            }
            if ins_len == patch_len {
                self.add_patch(address, &patch[..], ins_len);
            } else {
                self.add_hook(address, ins_len, &patch[..(patch_len as usize)]);
            }
            return;
        } else if let WidenInstruction::ArrayIndex(array_addr, dat, field_id, base_idx) = mode {
            let modrm = patch[idx_1];
            let sib = patch[idx_2];
            let index_reg = modrm & 0x7;
            let other = modrm & 0x38;
            if E::VirtualAddress::SIZE == 4 {
                if matches!(modrm & 0xc7, 0x80 | 0x81 | 0x82 | 0x83 | 0x85 | 0x86 | 0x87) {
                    // Widen [reg + base] to [reg * 4 + base]
                    let mut buf = [0; 16];
                    for i in 0..(idx_1) {
                        buf[i as usize] = patch[i as usize];
                    }
                    buf[idx_1] = 0x4 | other;
                    buf[idx_2] = 0x85 | (index_reg << 3);
                    for i in idx_3..(patch_len as usize + 1) {
                        buf[i] = patch[i - 1];
                    }
                    // This instruction should have the array address immediate,
                    // mark is at something that needs to be fixed in result.code_bytes
                    if let Some(bytes) = buf.get_mut(idx_3..(idx_3 + 4)) {
                        let value = LittleEndian::read_u32(bytes);
                        if value == array_addr as u32 {
                            let result = &mut self.dat_ctx.result;
                            let offset = result.code_bytes.len() + idx_3;
                            result.arrays_in_code_bytes.push((offset, dat, field_id));
                            LittleEndian::write_u32(bytes, u32::MAX);
                        } else {
                            dat_warn!(self, "Expected to find array immediate @ {address:?}");
                        }
                    }
                    self.add_hook(address, ins_len, &buf[..(patch_len as usize + 1)]);
                    return;
                }
            } else {
                // 64bit:
                if (modrm & 0xc7 == 0x84 || modrm & 0xc7 == 0x04) && sib & 0xc0 == 0x00 {
                    // SIB with 32bit immediate and base + index * 1
                    // Or SIB with base + index * 1
                    if let Some(base_idx) = base_idx {
                        let has_imm = modrm & 0xc0 != 0;
                        // Get REX byte, assume either at [start - 1] or [start - 2]
                        // if [start - 1] is 0x0f (0x0f not currently used though)
                        let maybe_rex_idx = match patch.get(start.wrapping_sub(1)) {
                            Some(&0x0f) => start.wrapping_sub(2),
                            _ => start.wrapping_sub(1),
                        };
                        let rex = match patch.get(maybe_rex_idx) {
                            Some(&x) if x & 0xf0 == 0x40 => x & 0xf,
                            _ => 0,
                        };
                        let index = ((sib >> 3) & 7) | ((rex & 2) << 2);
                        let base = (sib & 7) | ((rex & 1) << 3);
                        if index == base_idx.index && base == base_idx.base {
                            // Can just change index scale to 4
                            patch[idx_2] |= 0x80;
                        } else if index == base_idx.base && base == base_idx.index {
                            // Have to switch index and base around
                            patch[idx_2] = ((sib & 7) << 3) |
                                ((sib >> 3) & 7) |
                                0x80;
                            if rex != 0 {
                                patch[maybe_rex_idx] = (patch[maybe_rex_idx] & 0xfc) |
                                    ((rex & 1) << 1) |
                                    ((rex & 2) >> 1);
                            }
                        } else {
                            dat_warn!(self, "Expected base/idx @ {address:?} were wrong");
                            return;
                        }
                        if has_imm {
                            // This instruction should have the array address immediate,
                            // mark is at something that needs to be fixed in result.code_bytes
                            if let Some(bytes) = patch.get_mut(idx_3..(idx_3 + 4)) {
                                let value = self.binary.base() + LittleEndian::read_u32(bytes);
                                if value.as_u64() == array_addr {
                                    let result = &mut self.dat_ctx.result;
                                    let offset = result.code_bytes.len() + idx_3;
                                    result.arrays_in_code_bytes.push((offset, dat, field_id));
                                    LittleEndian::write_u32(bytes, u32::MAX);
                                } else {
                                    dat_warn!(
                                        self, "Expected to find array immediate @ {address:?}",
                                    );
                                }
                            }
                        }
                        if ins_len == patch_len {
                            self.add_patch(address, &patch[..], ins_len);
                        } else {
                            self.add_hook(address, ins_len, &patch[..(patch_len as usize)]);
                        }
                        return;
                    }
                } else if modrm & 0xc0 == 0x00 && matches!(modrm & 0x7, 4 | 5) == false {
                    // Single register as address without anything else,
                    // should not need any modrm byte changes.
                    // Presumably an address constant was loaded to register with
                    // a RIP-relative `lea reg, [constant]` before.
                    if ins_len == patch_len {
                        self.add_patch(address, &patch[..], ins_len);
                    } else {
                        self.add_hook(address, ins_len, &patch[..(patch_len as usize)]);
                    }
                    return;
                }
            }
        }
        dat_warn!(self, "Don't know how to widen array index @ {address:?}");
    }

    fn widen_pointer_add(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dat: DatType,
        field_id: u8,
    ) {
        let address = ctrl.address();
        if !self.dat_ctx.patched_addresses.insert(address) {
            return;
        }

        let mut full_bytes = [0x90u8; 16];
        let (rex_off, bytes, ins_len) =
            match self.init_instruction_patch(address, &mut full_bytes)
        {
            Some(s) => s,
            None => return,
        };
        if E::VirtualAddress::SIZE != 4 && !rex_off {
            // Pointer additions should always be full sized regs
            dat_warn!(self, "Can't widen pointer add @ {:?}", address);
            return;
        }
        let rex_off = rex_off as usize;
        match *bytes {
            [0x01 | 0x03, second, ..] if second & 0xc0 == 0xc0 => {
                // add reg, reg
                // Determine which register has index and which arr
                // (arr is constant >= binary.base)
                // Then add patch
                // ```
                // shl index_reg, 2
                // mov ...
                // shr index_reg, 2 ; if index_reg wasn't written by mov
                // ```
                let opcode = bytes[0];
                let rex = if rex_off == 0 { 0 } else { full_bytes[0] };
                let rm = (second & 7) | ((rex & 1) << 3);
                let r = ((second >> 3) & 7) | ((rex & 4) << 1);
                let (dest, other) = match opcode == 1 {
                    true => (rm, r),
                    false => (r, rm),
                };
                let index_reg = if ctrl.resolve_register(dest)
                    .if_constant()
                    .is_some_and(|x| x >= self.binary.base().as_u64())
                {
                    other
                } else {
                    dest
                };
                if E::VirtualAddress::SIZE == 4 {
                    dat_warn!(self, "Unimplemented for 32bit @ {:?}", address);
                    return;
                }
                let patch = [
                    // shl index_reg, 2
                    0x48 | ((index_reg & 8) >> 3), 0xc1, 0xe0 | (index_reg & 7), 0x02,
                    // orig instruction
                    rex, opcode, second,
                    // shr index_reg, 2 (Not included in patch if index_reg == dest)
                    0x48 | ((index_reg & 8) >> 3), 0xc1, 0xe8 | (index_reg & 7), 0x02,
                ];
                let patch = if index_reg == dest {
                    &patch[..7]
                } else {
                    &patch[..11]
                };
                self.add_hook(address, ins_len, patch);
            }
            [0x05, ..] if E::VirtualAddress::SIZE == 4 => {
                // add eax, u32 (Still u32 on 64bit so not used there)
                let patch = [
                    // shl eax, 2
                    0xc1, 0xe0, 0x02,
                    // orig instruction
                    0x05, 0xff, 0xff, 0xff, 0xff,
                ];
                let result = &mut self.dat_ctx.result;
                let offset = result.code_bytes.len() + 4;
                result.arrays_in_code_bytes.push((offset, dat, field_id));
                self.add_hook(address, ins_len, &patch);
            }
            [0xff, second, ..] if second & 0xf8 == 0xc0 => {
                // (64bit) register inc
                // Convert to add reg, 4
                bytes[0] = 0x83;
                bytes[2] = 0x04;
                self.add_hook(address, ins_len, &full_bytes[..(rex_off + 3)]);
            }
            _ => dat_warn!(self, "Can't widen pointer add @ {:?}", address),
        }
    }

    /// Shared code for widen_instruction and widen_pointer_add; reads instruction to
    /// mutable u8 buffer, returns
    /// 0: Does instruction have REX byte
    /// 1: 15 bytes of instruction without REX byte
    /// 2: instruction length
    fn init_instruction_patch<'x>(
        &mut self,
        address: E::VirtualAddress,
        full_bytes: &'x mut [u8; 16],
    ) -> Option<(bool, &'x mut [u8; 15], u8)> {
        let imm_bytes = match self.binary.slice_from_address(address, 0x18) {
            Ok(o) => o,
            Err(_) => {
                dat_warn!(self, "Can't widen instruction @ {:?}", address);
                return None;
            }
        };
        let ins_len = if E::VirtualAddress::SIZE == 4 {
            lde::X86::ld(imm_bytes) as u8
        } else {
            lde::X64::ld(imm_bytes) as u8
        };
        if ins_len >= 16 {
            dat_warn!(self, "Instruction is too long ({})", ins_len);
            return None;
        }

        let imm_bytes = &imm_bytes[..16];
        for i in 0..ins_len {
            full_bytes[i as usize] = imm_bytes[i as usize];
        }
        if E::VirtualAddress::SIZE == 8 && full_bytes[0] & 0xf0 == 0x40 {
            Some((true, (&mut full_bytes[1..16]).try_into().unwrap(), ins_len))
        } else {
            Some((false, (&mut full_bytes[..15]).try_into().unwrap(), ins_len))
        }
    }

    /// NOTE: Address should be start of a instruction, and the patch should be long
    /// enough to cover the entire instruction even if some later bytes are redundant.
    /// Needed due to marking that instruction as required_stable_address
    fn add_patch(&mut self, address: E::VirtualAddress, patch: &[u8], len: u8) {
        let patch = &patch[..len as usize];
        self.add_required_stable_address_for_patch(address, address + len as u32);
        self.dat_ctx.add_replace_patch(address, patch);
    }

    fn add_hook(&mut self, address: E::VirtualAddress, skip: u8, hook: &[u8]) {
        let result = &mut self.dat_ctx.result;
        let code_bytes_offset = result.code_bytes.len() as u32;
        result.code_bytes.extend_from_slice(hook);
        self.state.pending_hooks.push((address, code_bytes_offset, hook.len() as u8, skip));
    }

    #[inline]
    fn debug_verify_patch_is_same(&self, addr: E::VirtualAddress, patch: &[u8], skip: u8) {
        // Ignore unused warning when the code below is not compiled in
        let _ = (addr, patch, skip);
        // For cases where a patch was already added to an address, confirm
        // that the patch is same as would've been added here.
        #[cfg(any(debug_assertions, feature = "test_assertions", feature = "binaries"))]
        {
            let result = &self.dat_ctx.result;
            let old_patch = if skip as usize == patch.len() {
                // Not hook
                result.patches.iter()
                    .find_map(|x| match *x {
                        DatPatch::Replace(a, offset, len) if a == addr && len == skip => {
                            Some(offset)
                        }
                        _ => None,
                    })
                    .map(|offset| &result.code_bytes[(offset as usize)..][..(skip as usize)])
            } else {
                // Hook
                result.patches.iter()
                    .find_map(|x| match *x {
                        DatPatch::Hook(a, offset, len, s) |
                            DatPatch::TwoStepHook(a, _, offset, len, s)
                            if a == addr && len == patch.len() as u8 && s == skip =>
                        {
                            Some(offset)
                        }
                        _ => None,
                    })
                    .or_else(|| {
                        self.state.pending_hooks.iter()
                            .find(|&&(a, _, len, s)| {
                                a == addr && len == patch.len() as u8 && s == skip
                            })
                            .map(|x| x.1)
                    })
                    .map(|offset| &result.code_bytes[(offset as usize)..][..patch.len()])
            };
            if let Some(old_patch) = old_patch {
                if patch != old_patch {
                    dat_warn!(
                        self, "Tried to patch {addr:?} with {patch:02x?}, \
                        but a different patch {old_patch:02x?} was already applied"
                    );
                }
            } else {
                dat_warn!(
                    self, "Tried to patch {addr:?} with {patch:02x?}, \
                    but a different patch was already applied"
                );
            }
        }
    }

    fn generate_stack_size_patches(&mut self) {
        let bump = &self.dat_ctx.analysis.bump;
        let mut stack_size_tracker = mem::replace(
            &mut self.state.stack_size_tracker,
            stack_analysis::StackSizeTracker::empty(self.binary, bump),
        );
        let unwind = Rc::clone(&self.dat_ctx.unwind_functions);
        stack_size_tracker.generate_patches(&unwind, |addr, patch, skip| {
            if !self.dat_ctx.patched_addresses.insert(addr) {
                self.debug_verify_patch_is_same(addr, patch, skip as u8);
                return;
            }
            if skip == patch.len() {
                self.add_patch(addr, patch, patch.len() as u8);
            } else {
                self.add_hook(addr, skip as u8, patch);
            }
        });
    }

    fn check_u8_instruction(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dest_unresolved: Option<&DestOperand<'e>>,
        op: Operand<'e>,
        unresolved: Operand<'e>,
    ) {
        if !contains_u8(unresolved) {
            return;
        }
        if let Some(u8_op) = self.dat_ctx.contains_u8_operand(op) {
            let widen_mode = Self::select_widen_mode(ctrl, dest_unresolved, unresolved);
            let rva = Rva((ctrl.address().as_u64() - self.binary.base.as_u64()) as u32);
            self.state.u8_instruction_lists.add_check_used_address(u8_op, (rva, widen_mode));
        }
    }
}

fn contains_u8(op: Operand<'_>) -> bool {
    match *op.ty() {
        OperandType::Arithmetic(ref arith) => {
            op.relevant_bits() == (0..8) ||
                contains_u8(arith.left) ||
                contains_u8(arith.right)
        }
        OperandType::Constant(_) => false,
        _ => op.relevant_bits() == (0..8),
    }
}

struct CfgAnalyzer<'a, 'b, 'c, 'acx, 'e, E: ExecutionState<'e>> {
    branch: E::VirtualAddress,
    // Only used for the first branch when needed_operand is None
    final_address: E::VirtualAddress,
    func_entry: E::VirtualAddress,
    ctx: OperandCtx<'e>,
    // Used if doing CFG analysis for function argument instead of array index
    // Causes analyzer to determine what is the value of this unresolved operand
    // at end of the branch. (This is resolved when being added from succeeding branch,
    // but unresolved from the preceding branch analysis's point of view)
    needed_operand: Option<Operand<'e>>,
    resolved_dest_address: Option<MemAccess<'e>>,
    unchecked_branches:
        BumpVec<'acx, (E::VirtualAddress, Operand<'e>, E::VirtualAddress, Option<MemAccess<'e>>)>,
    added_unchecked_branches:
        HashSet<(E::VirtualAddress, OperandHashByAddress<'e>, E::VirtualAddress)>,
    parent: &'a mut DatReferringFuncAnalysis<'b, 'c, 'acx, 'e, E>,
    cfg: &'a mut Cfg<'e, E, analysis::DefaultState>,
    predecessors: &'a scarf::cfg::Predecessors,
    // High bit of rva here is used to tell if instruction writes to stack memory.
    // (Not bothering to making InstructionLists generic over value)
    instruction_lists: InstructionLists<'acx, OperandHashByAddress<'e>>,
    // Instruction which assigns to `needed_operand`.
    // Bool is true if it reads from stack memory (Requiring the stack variable
    // to be grown to 4 bytes as well)
    assign_instruction_widen_request: Option<(E::VirtualAddress, WidenInstruction)>,
    // Tells if the current branch needs to be reanalyzed with a different operand & end
    rerun_branch: Option<(E::VirtualAddress, Operand<'e>, E::VirtualAddress)>,
    dat: DatType,
    ending: bool,
}

impl<'a, 'b, 'c, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    CfgAnalyzer<'a, 'b, 'c, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let address = ctrl.address();
        if address == self.final_address && !self.ending {
            self.ending = true;
            self.end(ctrl);
        }
        match *op {
            Operation::Move(ref dest, val, None) => {
                let resolved = ctrl.resolve(val);
                self.check_u8_instruction(ctrl, Some(dest), resolved, val);
                match *dest {
                    DestOperand::Register32(r) | DestOperand::Register64(r) => {
                        if let Some(op) = self.needed_operand {
                            if Operand::and_masked(op).0.if_register()
                                .filter(|&x| x == r)
                                .is_some()
                            {
                                // I feel like this doesn't need to be a branch rerun..
                                // (It wouldn't hurt but would be just a bit more time spent)
                                // But saving this as an assigning instruction that needs widening
                                // catches an edge case where [ebp - xx] needs to be relocated.
                                // Specifically `mov r32, [ebp - xx]`
                                self.set_assigning_instruction(ctrl, dest, val, address);
                            }
                        }
                    }
                    DestOperand::Register8Low(r) => {
                        // We want to also patch assignment like mov al, 82,
                        // but that isn't caught by check_u8_instruction
                        if let Some(op) = self.needed_operand {
                            if Operand::and_masked(op).0.if_register()
                                .filter(|&x| x == r)
                                .is_some()
                            {
                                self.set_assigning_instruction(ctrl, dest, val, address);
                                self.instruction_lists.clear();
                                // Ask the branch to be rerun with
                                // self.final_address set to this instruction
                                // This operand should be unresolved, pretty sure..
                                self.rerun_branch = Some((self.branch, val, address));
                            }
                        }
                    }
                    DestOperand::Memory(ref mem) => {
                        let matches = if let Some(resolved_dest) = self.resolved_dest_address {
                            resolved_dest.address() == ctrl.resolve_mem(mem).address()
                        } else {
                            self.needed_operand
                                .and_then(|x| x.if_memory())
                                .filter(|x| x.address() == mem.address())
                                .is_some()
                        };
                        // Same for mov byte [esp - 4], al and such
                        if matches {
                            self.set_assigning_instruction(ctrl, dest, val, address);
                            self.instruction_lists.clear();
                            self.rerun_branch = Some((self.branch, val, address));
                        }
                    }
                    _ => (),
                }
                if address == self.final_address {
                    if self.needed_operand.is_none() {
                        self.check_final_op(ctrl, resolved);
                    }
                }
            }
            Operation::SetFlags(ref arith) => {
                let left = ctrl.resolve(arith.left);
                let right = ctrl.resolve(arith.right);
                self.check_u8_instruction(ctrl, None, left, arith.left);
                self.check_u8_instruction(ctrl, None, right, arith.right);
                if address == self.final_address {
                    if self.needed_operand.is_none() {
                        self.check_final_op(ctrl, left);
                        self.check_final_op(ctrl, right);
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if let Some(custom) = self.parent.custom_value_for_call(dest) {
                        ctrl.skip_operation();
                        ctrl.set_register(0, custom);
                    }
                }
            }
            _ => (),
        }
    }

    fn branch_end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        self.end(ctrl);
    }
}

impl<'a, 'b, 'c, 'acx, 'e, E: ExecutionState<'e>> CfgAnalyzer<'a, 'b, 'c, 'acx, 'e, E> {
    fn set_assigning_instruction(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dest_unres: &DestOperand<'e>,
        unresolved: Operand<'e>,
        address: E::VirtualAddress,
    ) {
        let widen_mode = self.widen_mode_for_instruction(ctrl, Some(dest_unres), unresolved);
        self.assign_instruction_widen_request = Some((address, widen_mode));
    }

    fn widen_mode_for_instruction(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        write: Option<&DestOperand<'e>>,
        read: Operand<'e>,
    ) -> WidenInstruction {
        // Don't widen assigning instruction if its memory access is to non-stack memory.
        // Similar to what DatReferringFuncAnalysis::select_widen_mode does, but
        // adapted to CfgAnalyzer having ctrl resolving to start of branch, having
        // to do separate resolve for start of function.
        for i in 0..2 {
            // Iteration 0: Value if memory, 1: Dest if memory
            // Assuming that if both are memory value takes priority.
            // Usually on x86 they're same, though `push dword[x]` will
            // write to [esp - 4] and read from [x], and we care about the
            // read.
            // (Is it fine that `push ecx` would be detected as widen req to [esp - 4]`?
            // Think it's fine and will be just no-op)
            let unres = if i == 0 {
                match read.if_memory() {
                    Some(s) => s,
                    None => continue,
                }
            } else {
                match write {
                    Some(DestOperand::Memory(mem)) => mem,
                    _ => continue,
                }
            };
            let (base, _) = unres.address();
            let branch_start_resolved = ctrl.resolve(base);
            // One memory was processed, can just end here even if i == 0
            let mode = self.widen_mode_for_resolved_mem(branch_start_resolved);
            return mode;
        }
        WidenInstruction::Default
    }

    /// Mem must be resolved (to start of analysis, that is, to start of self.branch).
    ///
    /// This function will resolve it to start of function and check if it is referring to stack.
    fn widen_mode_for_resolved_mem(
        &mut self,
        branch_start_base: Operand<'e>,
    ) -> WidenInstruction {
        let state = self.parent.binary.try_rva_32(self.branch)
            .and_then(|rva| self.cfg.get_state(Rva(rva)));
        if let Some(state) = state {
            let (base1, offset1) = branch_start_base.add_sub_offset();
            let func_start_resolved = state.exec_state_mut().resolve(base1);
            let (base, offset) = func_start_resolved.add_sub_offset();
            let ctx = self.ctx;
            let esp = ctx.register(4);
            if base == esp {
                let offset = offset.wrapping_add(offset1);
                if let Ok(offset) = i32::try_from(offset as i64) {
                    return WidenInstruction::StackAccess(offset);
                }
            }
            WidenInstruction::Default
        } else {
            dat_warn!(self, "No cfg node for {:?}", self.branch);
            WidenInstruction::Default
        }
    }

    fn end(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        ctrl.end_analysis();
        if let Some(op) = self.needed_operand {
            if self.resolved_dest_address.is_none() {
                if let Some(mem) = op.if_memory() {
                    // If unresolved address is [esp + x] (Not [esp])
                    // and resolved is [esp - x], redo the analysis
                    // with resolved_dest_address set.
                    // It's a bit hacky fix and probably could be more general,
                    // but oh well.
                    let ctx = ctrl.ctx();
                    let (base, offset) = mem.address();
                    if base == ctx.register(4) && (1..0x200).contains(&offset) {
                        let mem = ctrl.resolve_mem(mem);
                        let (base, offset) = mem.address();
                        if base == ctx.register(4) && (-0x200..0).contains(&(offset as i32)) {
                            self.add_resolved_dest_redo(mem);
                        }
                    }
                }
            }
            let val = ctrl.resolve(op);
            self.finishing_branch(val);
        }
    }

    /// Called when at instruction self.final_address (needed_operand not set)
    /// `op` is supposed to be a operand which is being read from
    /// (Expected dat_array[index]), from where the index will be cheked and handled.
    fn check_final_op(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: Operand<'e>) {
        // Match Mem[index + C], Mem[index * C2 + C]
        let ctx = ctrl.ctx();
        let index = match op.if_memory()
            .and_then(|mem| {
                let (base, offset) = mem.address();
                if offset == 0 || base == ctx.const_0() {
                    return None;
                }
                // Remove * 2 or * 4 if mem address is not byte
                let removed = base.if_arithmetic_mul()
                    .filter(|(_, r)| r.if_constant().is_some())
                    .map(|(l, _)| l)
                    .unwrap_or(base);
                Some(removed)
            })
        {
            Some(s) => s,
            None => return,
        };

        ctrl.end_analysis();
        self.finishing_branch(index);
    }

    /// Called at end of the branch (And entire scarf analyze() run due to CfgAnalyzer
    /// only running for the one branch at a time)
    /// `op` should be the resolved dat array index/other value that is being tracked for
    /// this current analyze() run.
    fn finishing_branch(&mut self, op: Operand<'e>) {
        if let Some((address, mode)) = self.assign_instruction_widen_request.take() {
            self.parent.widen_instruction(address, mode);
        }
        if let Some(s) = self.rerun_branch.take() {
            self.add_unchecked_branch(s.0, s.1, s.2);
            return;
        }
        match *Operand::and_masked(op).0.ty() {
            OperandType::Register(reg) => {
                if E::VirtualAddress::SIZE == 8 && self.branch == self.func_entry {
                    let arg = match reg {
                        1 => 0,
                        2 => 1,
                        8 => 2,
                        9 => 3,
                        _ => 4,
                    };
                    if arg < 4 {
                        self.parent.needed_func_params[arg] = Some(self.dat);
                    }
                }
            }
            OperandType::Memory(mem) => {
                let (base, offset) = mem.address();
                let reg = base.if_register()
                    .filter(|&x| x == 4 || x == 5);
                match reg {
                    Some(r) if r == 4 && self.branch == self.func_entry => {
                        // If this is an argument, then request all of its uses to be widened
                        // for parent.
                        if let Some(arg) = arg_n_from_offset::<E>(offset).map(|x| x as usize) {
                            if arg < self.parent.needed_func_params.len() {
                                self.parent.needed_func_params[arg] = Some(self.dat);
                            }
                        }
                    }
                    Some(_) => (),
                    None => return,
                }
            }
            _ => {
                return;
            }
        };

        let binary = self.parent.binary;
        let base = binary.base();
        for (rva, widen_mode) in self.instruction_lists.iter(op.hash_by_address()) {
            let address = base + rva.0;
            self.parent.widen_instruction(address, widen_mode);
        }
        let branch_rva = Rva(binary.rva_32(self.branch));
        if let Some(own_branch_link) = self.cfg.get_link(branch_rva) {
            for link in self.predecessors.predecessors(self.cfg, &own_branch_link) {
                let address = base + link.address().0;
                Self::add_unchecked_branch_(
                    &mut self.added_unchecked_branches,
                    &mut self.unchecked_branches,
                    address,
                    op,
                    E::VirtualAddress::from_u64(0),
                );
            }
        } else {
            error!("Broken cfg? Branch {:?} not found", self.branch);
        }
    }

    fn add_unchecked_branch(
        &mut self,
        address: E::VirtualAddress,
        op: Operand<'e>,
        final_address: E::VirtualAddress,
    ) {
        Self::add_unchecked_branch_(
            &mut self.added_unchecked_branches,
            &mut self.unchecked_branches,
            address,
            op,
            final_address,
        )
    }

    fn add_unchecked_branch_(
        added_unchecked_branches:
            &mut HashSet<(E::VirtualAddress, OperandHashByAddress<'e>, E::VirtualAddress)>,
        unchecked_branches:
            &mut BumpVec<'acx, (E::VirtualAddress, Operand<'e>, E::VirtualAddress, Option<MemAccess<'e>>)>,
        address: E::VirtualAddress,
        op: Operand<'e>,
        final_address: E::VirtualAddress,
    ) {
        if added_unchecked_branches.insert((address, op.hash_by_address(), final_address)) {
            unchecked_branches.push((address, op, final_address, None));
        }
    }

    fn add_resolved_dest_redo(&mut self, resolved: MemAccess<'e>) {
        if let Some(needed) = self.needed_operand {
            self.unchecked_branches.push((
                self.branch,
                needed,
                self.final_address,
                Some(resolved),
            ));
        }
    }

    fn check_u8_instruction(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        dest: Option<&DestOperand<'e>>,
        op: Operand<'e>,
        unresolved: Operand<'e>,
    ) {
        // Cfg analysis save all u8-sized operands (and their parts), unlike main analysis
        // which is cheaper by only saving U8Operand values
        if !contains_u8(unresolved) {
            return;
        }
        let binary = self.parent.binary;
        let rva = Rva((ctrl.address().as_u64() - binary.base.as_u64()) as u32);
        let widen_mode = self.widen_mode_for_instruction(ctrl, dest, unresolved);
        for part in op.iter_no_mem_addr() {
            self.instruction_lists.add(part.hash_by_address(), (rva, widen_mode));
        }
    }
}

impl<'acx, Key: Hash + Eq> InstructionLists<'acx, Key> {
    fn clear(&mut self) {
        self.heads.clear();
        self.store.clear();
        self.used_addresses.clear();
    }

    /// This probs shouldn't be part of InstructionLists but one level higher,
    /// if ever refactored.
    fn add_check_used_address(&mut self, key: Key, rva: (Rva, WidenInstruction)) {
        if !self.used_addresses.insert(rva.0) {
            return;
        }
        self.add(key, rva);
    }

    fn add(&mut self, key: Key, rva: (Rva, WidenInstruction)) {
        let new_head = self.store.len();
        let entry = self.heads.entry(key);
        match entry {
            Entry::Occupied(mut e) => {
                let prev_head = *e.get();
                self.store.push((rva, prev_head));
                *e.get_mut() = new_head;
            }
            Entry::Vacant(e) => {
                self.store.push((rva, !0));
                e.insert(new_head);
            }
        }
    }

    fn iter<'a>(&'a self, key: Key) -> impl Iterator<Item = (Rva, WidenInstruction)> + 'a {
        let index = self.heads.get(&key).cloned().unwrap_or(!0);
        U8InstructionListsIter(self, index)
    }
}

struct U8InstructionListsIter<'acx, 'a, K: Hash + Eq>(&'a InstructionLists<'acx, K>, usize);

impl<'acx, 'a, K: Hash + Eq> Iterator for U8InstructionListsIter<'acx, 'a, K> {
    type Item = (Rva, WidenInstruction);
    fn next(&mut self) -> Option<Self::Item> {
        if self.1 == !0 {
            None
        } else {
            let (rva, next) = self.0.store[self.1];
            self.1 = next;
            Some(rva)
        }
    }
}

struct RecognizeDatPatchFunc<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> {
    flags: u8,
    inlining: bool,
    inline_ok: bool,
    returns: BumpVec<'acx, Operand<'e>>,
    dat_ctx: &'a mut DatPatchContext<'b, 'acx, 'e, E>,
}

const SUBUNIT_READ: u8 = 0x1;
const AIR_WEAPON_READ: u8 = 0x2;
const GROUND_WEAPON_READ: u8 = 0x4;
const ORDER_WEAPON_READ: u8 = 0x8;
const UNIT_ID_IS_INF_KERRIGAN: u8 = 0x10;

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    RecognizeDatPatchFunc<'a, 'b, 'acx, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        if self.inlining {
            match *op {
                Operation::Call(..) => {
                    self.inline_ok = false;
                    ctrl.end_analysis();
                }
                _ => (),
            }
        } else {
            match *op {
                Operation::Call(dest) => {
                    if let Some(dest) = ctrl.resolve(dest).if_constant() {
                        let dest = E::VirtualAddress::from_u64(dest);
                        self.inlining = true;
                        self.inline_ok = true;
                        ctrl.inline(self, dest);
                        if self.inline_ok {
                            ctrl.skip_operation();
                        }
                        self.inlining = false;
                    }
                }
                Operation::Move(_, val, None) => {
                    let val = ctrl.resolve(val);
                    if let Some(mem) = val.if_memory() {
                        let ctx = ctrl.ctx();
                        let (base, offset) = mem.address();
                        if base == ctx.register(1) &&
                            offset == E::struct_layouts().unit_subunit_linked()
                        {
                            self.flags |= SUBUNIT_READ;
                        }
                        let address = E::VirtualAddress::from_u64(offset);
                        let dat_field = self.dat_ctx.array_lookup.get(&address);
                        if let Some(&(dat, idx)) = dat_field {
                            match (dat, idx) {
                                (DatType::Units, 0x11) => self.flags |= GROUND_WEAPON_READ,
                                (DatType::Units, 0x13) => self.flags |= AIR_WEAPON_READ,
                                (DatType::Orders, 0x0d) => self.flags |= ORDER_WEAPON_READ,
                                _ => self.fail(ctrl),
                            }
                        }
                    }
                }
                Operation::Jump { condition, .. } => {
                    let condition = ctrl.resolve(condition);
                    let inf_kerry_cmp = condition.if_arithmetic_eq_neq()
                        .filter(|x| x.1.if_constant() == Some(0x33))
                        .and_then(|x| x.0.if_mem16_offset(E::struct_layouts().unit_id()))
                        .is_some();
                    if inf_kerry_cmp {
                        self.flags |= UNIT_ID_IS_INF_KERRIGAN;
                    }
                }
                Operation::Return(_) => {
                    let val = ctrl.resolve_register(0);
                    self.returns.push(val);
                }
                _ => (),
            }
        }
    }
}

impl<'a, 'b, 'acx, 'e, E: ExecutionState<'e>> RecognizeDatPatchFunc<'a, 'b, 'acx, 'e, E> {
    fn new(
        dat_ctx: &'a mut DatPatchContext<'b, 'acx, 'e, E>,
    ) -> RecognizeDatPatchFunc<'a, 'b, 'acx, 'e, E> {
        let bump = &dat_ctx.analysis.bump;
        RecognizeDatPatchFunc {
            flags: 0,
            dat_ctx,
            inlining: false,
            inline_ok: false,
            returns: BumpVec::new_in(bump),
        }
    }

    fn fail(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        self.flags = !0;
        ctrl.end_analysis();
    }

    fn result(&self) -> Result<Option<DatReplaceFunc>, ()> {
        use self::DatReplaceFunc::*;
        // No need to patch functions that don't return u8 values
        // One example is player_ai_first_request_type
        if !self.returns.is_empty() {
            if self.returns.iter().all(|x| {
                if let Some(mem) = x.if_memory() {
                    return mem.size != MemAccessSize::Mem8;
                }
                if x.if_constant().is_some() {
                    return true;
                }
                if x.if_arithmetic_add().and_then(|(_, r)| r.if_constant()).is_some() {
                    return true;
                }
                false
            })
            {
                return Ok(None);
            }
        }
        if self.returns.len() == 1 {
            let val = self.returns[0];
            let inner = match val.if_arithmetic_or() {
                Some((l, r)) => {
                    if l.relevant_bits().end <= 8 && r.relevant_bits().start >= 8 {
                        l
                    } else if l.relevant_bits().end >= 8 && r.relevant_bits().start <= 8 {
                        r
                    } else {
                        val
                    }
                }
                _ => val,
            };
            let this_field = inner.if_memory()
                .and_then(|mem| {
                    let (base, offset) = mem.address();
                    if base.if_register() == Some(1) {
                        Some((offset, mem.size))
                    } else {
                        None
                    }
                });
            if let Some((offset, size)) = this_field {
                if offset == E::struct_layouts().unit_current_tech() &&
                    size == MemAccessSize::Mem8
                {
                    return Ok(Some(UnitCurrentTech));
                }
                if offset == E::struct_layouts().unit_current_upgrade() &&
                    size == MemAccessSize::Mem8
                {
                    return Ok(Some(UnitCurrentUpgrade));
                }
            }
        }

        Ok(Some(match self.flags {
            x if x == GROUND_WEAPON_READ => UnitGroundWeapon,
            x if x == GROUND_WEAPON_READ | SUBUNIT_READ => SelfOrSubunitGroundWeapon,
            x if x == AIR_WEAPON_READ | SUBUNIT_READ => SelfOrSubunitAirWeapon,
            x if x == ORDER_WEAPON_READ => UnitOrderWeapon,
            x if x == UNIT_ID_IS_INF_KERRIGAN => UnitCloakTech,
            _ => return Err(()),
        }))
    }
}

/// Convert `esp + constant` to argument number if it is one.
/// Return value is 0-based.
/// E.g. First argument is at esp + 4, so arg_n_from_offset(4) == Some(0)
fn arg_n_from_offset<'e, E: ExecutionState<'e>>(constant: u64) -> Option<u8> {
    if E::VirtualAddress::SIZE == 4 {
        if constant < 0x40 && constant & 3 == 0 && constant != 0 {
            Some(constant as u8 / 4 - 1)
        } else {
            None
        }
    } else {
        if constant < 0x60 && constant & 7 == 0 && constant >= 0x28 {
            Some(constant as u8 / 8 - 1)
        } else {
            None
        }
    }
}

fn reloc_address_of_instruction<'e, E: ExecutionState<'e>, A>(
    ctrl: &mut Control<'e, '_, '_, A>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    addr: E::VirtualAddress,
) -> Option<E::VirtualAddress>
where A: analysis::Analyzer<'e, Exec=E>
{
    let mut imm_addr = ctrl.current_instruction_end() - 4;
    let expected_riprel =
        addr.as_u64().wrapping_sub(ctrl.current_instruction_end().as_u64()) as i64 as i32 as u32;
    let base_relative = binary.try_rva_32(addr)?;
    while imm_addr > ctrl.address() {
        if let Ok(imm) = binary.read_u32(imm_addr) {
            if E::VirtualAddress::SIZE == 4 {
                if imm == addr.as_u64() as u32 {
                    return Some(imm_addr);
                }
            } else {
                if imm == expected_riprel || imm == base_relative {
                    return Some(imm_addr);
                }
            }
        }
        imm_addr = imm_addr - 1;
    }
    None
}

fn instruction_length<Va: VirtualAddress>(binary: &BinaryFile<Va>, address: Va) -> Option<u8> {
    let bytes = binary.slice_from_address(address, 0x10).ok()?;
    if Va::SIZE == 4 {
        Some(lde::X86::ld(bytes) as u8)
    } else {
        Some(lde::X64::ld(bytes) as u8)
    }
}

fn min_instruction_length<Va: VirtualAddress>(
    binary: &BinaryFile<Va>,
    address: Va,
    min: u32,
) -> Option<u32> {
    let bytes = binary.slice_from_address(address, min + 0x20).ok()?;
    let mut len = 0;
    while len < min {
        let slice = bytes.get(len as usize..)?;
        let new_len = if Va::SIZE == 4 {
            lde::X86::ld(slice)
        } else {
            lde::X64::ld(slice)
        };
        len += new_len;
    }
    Some(len)
}

/// Data required to build hooks for a function
struct FunctionHookContext<'a, 'acx, 'e, E: ExecutionState<'e>> {
    result: &'a mut DatPatches<'e, E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    required_stable_addresses: &'a mut RequiredStableAddresses<'acx, E::VirtualAddress>,
    entry: E::VirtualAddress,
}

impl<'a, 'acx, 'e, E: ExecutionState<'e>> FunctionHookContext<'a, 'acx, 'e, E> {
    /// Creates patches from pending hooks and adds them to result.
    fn process_pending_hooks(
        &mut self,
        mut pending_hooks: BumpVec<'_, (E::VirtualAddress, u32, u8, u8)>,
    ) {
        pending_hooks.sort_unstable_by_key(|x| x.0);
        let binary = self.binary;
        let mut i = 0;
        let mut short_jump_hooks = 0;
        let long_jump_len = 5;
        // Add anything that can do a long hook
        while i < pending_hooks.len() {
            let (address, code_offset, len, skip) = pending_hooks[i];
            let mut needs_short_jump = false;
            let mut can_hook_at_all = true;
            // First check if another hook forces a short jump
            if let Some(next) = pending_hooks.get(i + 1) {
                if next.0 < address + long_jump_len {
                    needs_short_jump = true;
                }
                if next.0 < address + 2 {
                    can_hook_at_all = false;
                }
            }
            // Add long jump if other stable addresses won't conflict
            if !needs_short_jump {
                let stable_address_result = self.try_add_required_stable_address_for_patch(
                    address,
                    address + 5,
                );
                match stable_address_result {
                    Ok(()) => {
                        let result = &mut self.result;
                        result.patches.push(DatPatch::Hook(address, code_offset, len, skip));
                    }
                    Err(_conflict_address) => {
                        needs_short_jump = true;
                    }
                }
            }
            if needs_short_jump && can_hook_at_all {
                // Reserve the 2byte shortjmp space here
                if let Err(_) =
                    self.try_add_required_stable_address_for_patch(address, address + 2)
                {
                    can_hook_at_all = false;
                }
            }
            if !can_hook_at_all {
                dat_warn!(self, "Can't hook @ {:?}", address);
            } else if needs_short_jump {
                // Keep the pending hook for a second loop, move it to start of the vec
                pending_hooks[short_jump_hooks] = pending_hooks[i];
                short_jump_hooks += 1;
            } else {
                // Was added succesfully as a long hook
            }

            // Add hook return position as jump dest
            let return_pos = address + skip as u32;
            if let Some(len) = instruction_length(binary, return_pos) {
                let _ = self.required_stable_addresses.try_add(
                    binary,
                    return_pos,
                    return_pos + len as u32,
                    IsJumpDest::Yes,
                );
            }

            i += 1;
        }
        // Shortjump hooks
        let short_jump_hook_slice = &pending_hooks[..short_jump_hooks];
        for &(address, code_offset, len, skip) in short_jump_hook_slice {
            let space = match self.find_short_jump_hook_space(address) {
                Some(s) => s,
                None => {
                    dat_warn!(self, "Can't find shortjmp space for {:?}", address);
                    continue;
                }
            };
            let result = &mut self.result;
            result.patches.push(DatPatch::TwoStepHook(address, space, code_offset, len, skip));
        }
    }

    fn find_short_jump_hook_space(
        &mut self,
        address: E::VirtualAddress,
    ) -> Option<E::VirtualAddress> {
        let min = address - 0x7c;
        let max = address + 0x7c;
        let mut cand = None;
        let mut result = None;
        let binary = self.binary;
        let base = binary.base();
        for (start, end) in self.required_stable_addresses.iter() {
            let start = base + start.0;
            let end = base + end.0;
            if let Some(cand) = cand.take() {
                if start >= cand + 0xa {
                    result = Some(cand);
                    break;
                }
            }
            if end > max {
                break;
            }
            if end > min {
                cand = Some(end);
            }
        }
        if result.is_none() {
            // Try at start of the function.
            // Not the very first instructions though, as that is probably better
            // to leave untouched to keep function-level hooks simpler.
            // Technically this could be the what `cand` is initialized to, but to
            // keep test compare diffs simpler, do this only if nothing was found.
            let addr = self.entry + min_instruction_length(binary, self.entry, 0x10)?;
            if let Some((start, _)) = self.required_stable_addresses.iter().next() {
                let start = base + start.0;
                if start >= addr + 0xa {
                    result = Some(addr);
                }
            } else {
                result = Some(addr);
            }
        }
        if let Some(cand) = result {
            let len = min_instruction_length(binary, cand, 0xa)?;
            self.add_required_stable_address_for_patch(cand, cand + len);
        }
        result
    }

    /// If there's a conflict in a jump instruction then converts to IsJumpDest::No.
    fn add_required_stable_address_for_patch(
        &mut self,
        start: E::VirtualAddress,
        end: E::VirtualAddress,
    ) {
        match self.try_add_required_stable_address_for_patch(start, end) {
            Ok(()) => (),
            Err(e) => {
                dat_warn!(self, "Required stable address overlap: {:?} vs {:?}", e, (start, end));
            }
        }
    }

    fn try_add_required_stable_address_for_patch(
        &mut self,
        start: E::VirtualAddress,
        end: E::VirtualAddress,
    ) -> Result<(), (E::VirtualAddress, E::VirtualAddress)> {
        self.required_stable_addresses.try_add_for_patch(self.binary, start, end)
    }
}
