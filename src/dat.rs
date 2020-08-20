mod game;

use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::hash::Hash;
use std::mem;
use std::rc::Rc;

use fxhash::{FxHashMap, FxHashSet};

use scarf::analysis::{self, Cfg, Control, FuncAnalysis, RelocValues};
use scarf::exec_state::{ExecutionState, VirtualAddress};
use scarf::operand::{ArithOpType, ArithOperand, MemAccessSize, OperandType, OperandHashByAddress};
use scarf::{BinaryFile, BinarySection, DestOperand, Operand, Operation, Rva};

use crate::{
    ArgCache, Analysis, EntryOf, StringRefs, DatType, entry_of_until, single_result_assign,
    string_refs, if_callable_const, OperandExt, OptionExt,
};
use crate::range_list::RangeList;

pub static UNIT_ARRAY_WIDTHS: &[u8] = &[
    1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2,
    2, 2, 2, 2, 4, 2, 8, 2, 2, 2, 2, 2, 1, 1, 1, 1,
    1, 2, 2, 2, 1, 2,
];

pub static WEAPON_ARRAY_WIDTHS: &[u8] = &[
    2, 4, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2,
    1, 1, 1, 1, 1, 1, 2, 2,
];

pub static FLINGY_ARRAY_WIDTHS: &[u8] = &[
    2, 4, 2, 4, 1, 1, 1,
];

pub static UPGRADE_ARRAY_WIDTHS: &[u8] = &[
    2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1,
];

pub static TECHDATA_ARRAY_WIDTHS: &[u8] = &[
    2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1,
];

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct DatTablePtr<'e> {
    pub address: Operand<'e>,
    pub entry_size: u32,
}

pub struct DatPatches<'e, Va: VirtualAddress> {
    pub patches: Vec<DatPatch<'e, Va>>,
    /// Bytes refered by hook/replace patches
    pub code_bytes: Vec<u8>,
    pub set_status_screen_tooltip: Option<Va>,
}

impl<'e, Va: VirtualAddress> DatPatches<'e, Va> {
    fn empty() -> DatPatches<'e, Va> {
        DatPatches {
            patches: Vec::new(),
            code_bytes: Vec::new(),
            set_status_screen_tooltip: None,
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
    pub field_id: u8,
    /// Unaligned address of a pointer in .text (Or .data/.rdata, whynot)
    /// (e.g. casting it to *const usize and reading it would give pointer to the orig
    /// field array until overwritten)
    pub address: Va,
    /// Offset from start of the array in entries.
    pub entry: i32,
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
}

pub(crate) fn dat_table<'e, E: ExecutionState<'e>>(
    analysis: &mut Analysis<'e, E>,
    filename: &'static str,
) -> Option<DatTablePtr<'e>> {
    let binary = analysis.binary;
    let functions = analysis.functions();
    let str_refs = string_refs(binary, analysis, filename.as_bytes());

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
                    let size = (1..10).filter_map(|offset| {
                        match binary.read_address(addr + offset * 4) {
                            Ok(x) if x.as_u64() > 0x10000 => Some(offset * 4),
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
    analysis: &mut Analysis<'e, E>,
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
    analysis: &mut Analysis<'e, E>,
) -> Option<DatPatches<'e, E::VirtualAddress>> {
    let dats = [
        DatType::Units, DatType::Weapons, DatType::Flingy, DatType::Upgrades,
        DatType::TechData,
    ];
    let firegraft = analysis.firegraft_addresses();
    let mut dat_ctx = DatPatchContext::new(analysis);
    let dat_ctx = dat_ctx.as_mut()?;
    for &dat in &dats {
        let table = dat_ctx.analysis.dat(dat)?;
        let address = table.address.if_constant().map(|x| E::VirtualAddress::from_u64(x))?;
        dat_ctx.add_dat(dat, address, table.entry_size).ok()?;
    }

    let dats = [(DatType::Orders, 0x13)];
    for &(dat, field_count) in &dats {
        let table = dat_ctx.analysis.dat(dat)?;
        let address = table.address.if_constant().map(|x| E::VirtualAddress::from_u64(x))?;
        dat_ctx.register_dat(dat, address, table.entry_size, field_count).ok()?;
    }

    dat_ctx.add_patches_from_code_refs();
    while !dat_ctx.funcs_needing_retval_patch.is_empty() {
        dat_ctx.retval_patch_funcs();
        dat_ctx.add_u8_func_patches();
        dat_ctx.add_func_arg_patches();
    }
    // Status screen array (Using unit 0xff)
    for &status_addr in &firegraft.unit_status_funcs {
        let end_ptr = status_addr + 0xe4 * 0xc;
        dat_ctx.add_dat_global_refs(DatType::Units, 0xff, status_addr, end_ptr, 0xc, false);
    }
    if dat_ctx.unknown_global_u8_mem.len() != 1 {
        let msg = format!(
            "Expected to have 1 unknown global u8 memory, got {:?}",
            dat_ctx.unknown_global_u8_mem,
        );
        dat_ctx.add_warning(msg);
    }
    game::dat_game_analysis(&mut dat_ctx.analysis, &mut dat_ctx.result);
    Some(mem::replace(&mut dat_ctx.result, DatPatches::empty()))
}

struct DatPatchContext<'a, 'e, E: ExecutionState<'e>> {
    relocs: Rc<Vec<RelocValues<E::VirtualAddress>>>,
    array_lookup: FxHashMap<E::VirtualAddress, (DatType, u8)>,
    units: DatTable<E::VirtualAddress>,
    weapons: DatTable<E::VirtualAddress>,
    flingy: DatTable<E::VirtualAddress>,
    upgrades: DatTable<E::VirtualAddress>,
    techdata: DatTable<E::VirtualAddress>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    text: &'e BinarySection<E::VirtualAddress>,
    result: DatPatches<'e, E::VirtualAddress>,
    unchecked_refs: FxHashSet<Rva>,
    // Funcs that seem to possibly only return in al need to be patched to widen
    // the return value to entirety of eax.
    // That's preferred over patching callers to widen the retval on their own side, as
    // then they don't need to worry about the function returning a wider value, e.g.
    // having get_ground_weapon patched to return u16 eventually.
    funcs_needing_retval_patch: Vec<Rva>,
    funcs_added_for_retval_patch: FxHashSet<Rva>,
    // Funcs that returned u8 and any of their callers now need to patched to widen the
    // return value
    u8_funcs: Vec<Rva>,
    operand_to_u8_op: FxHashMap<OperandHashByAddress<'e>, Option<U8Operand>>,
    analysis: &'a mut Analysis<'e, E>,
    patched_addresses: FxHashSet<E::VirtualAddress>,
    analyzed_functions: FxHashMap<Rva, Box<DatFuncAnalysisState>>,

    /// Structures for widening variables that are being passed to a function.
    /// func_arg_widen_requests are used during analysis to lookup if a certain insturction
    /// needs to be widened, func_arg_widen_queue is functions whose callers need to be
    /// analyzed.
    func_arg_widen_requests: FxHashMap<E::VirtualAddress, [Option<DatType>; 8]>,
    func_arg_widen_queue: Vec<E::VirtualAddress>,
    /// Which callers of function that needs arg widening have been handled.
    found_func_arg_widen_refs: FxHashSet<E::VirtualAddress>,
    /// Expected to have 1 entry for weapons
    /// global address -> code address
    unknown_global_u8_mem: FxHashMap<E::VirtualAddress, E::VirtualAddress>,

    step_iscript: E::VirtualAddress,
    /// Set during analysis, contains refs but isn't fully analyzed.
    /// Maybe dumb to special case this
    update_status_screen_tooltip: E::VirtualAddress,
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
    /// A dat field which should be widened (weapon/flingy id)
    DatField,
}

impl<'a, 'e, E: ExecutionState<'e>> DatPatchContext<'a, 'e, E> {
    fn new(analysis: &'a mut Analysis<'e, E>) -> Option<DatPatchContext<'a, 'e, E>> {
        fn dat_table<Va: VirtualAddress>(field_count: u32) -> DatTable<Va> {
            DatTable {
                table_address: Va::from_u64(0),
                field_count,
                entry_size: 0,
            }
        }

        let text = analysis.binary.section(b".text\0\0\0").unwrap();
        let step_iscript = analysis.step_iscript().step_fn?;
        Some(DatPatchContext {
            array_lookup: FxHashMap::with_capacity_and_hasher(128, Default::default()),
            operand_to_u8_op: FxHashMap::with_capacity_and_hasher(2048, Default::default()),
            funcs_needing_retval_patch: Vec::with_capacity(16),
            funcs_added_for_retval_patch:
                FxHashSet::with_capacity_and_hasher(16, Default::default()),
            u8_funcs: Vec::with_capacity(16),
            unchecked_refs: FxHashSet::with_capacity_and_hasher(1024, Default::default()),
            units: dat_table(0x36),
            weapons: dat_table(0x18),
            flingy: dat_table(0x7),
            upgrades: dat_table(0xc),
            techdata: dat_table(0xb),
            binary: analysis.binary,
            relocs: analysis.relocs_with_values(),
            text,
            analysis,
            result: DatPatches {
                patches: Vec::with_capacity(1024),
                code_bytes: Vec::with_capacity(2048),
                set_status_screen_tooltip: None,
            },
            patched_addresses: FxHashSet::with_capacity_and_hasher(64, Default::default()),
            analyzed_functions: FxHashMap::with_capacity_and_hasher(64, Default::default()),
            func_arg_widen_requests: FxHashMap::with_capacity_and_hasher(32, Default::default()),
            func_arg_widen_queue: Vec::with_capacity(32),
            found_func_arg_widen_refs:
                FxHashSet::with_capacity_and_hasher(128, Default::default()),
            step_iscript,
            unknown_global_u8_mem: FxHashMap::with_capacity_and_hasher(4, Default::default()),
            update_status_screen_tooltip: E::VirtualAddress::from_u64(0),
        })
    }

    fn add_warning(&mut self, msg: String) {
        warn!("{}", msg);
    }

    fn register_dat(
        &mut self,
        dat: DatType,
        table_address: E::VirtualAddress,
        entry_size: u32,
        field_count: u32,
    ) -> Result<(), ()> {
        for i in 0..field_count {
            let entry_address = table_address + i * entry_size;
            let array_ptr = self.binary.read_address(entry_address)
                .map_err(|_| ())?;
            self.array_lookup.insert(array_ptr, (dat, i as u8));
            let add_as_unchecked_ref = match (dat, i) {
                (DatType::Units, 0x11) | (DatType::Units, 0x13) | (DatType::Orders, 0x0d) |
                    (DatType::Units, 0x00) => true,
                _ => false,
            };
            if add_as_unchecked_ref {
                let text = self.text;
                let text_end = text.virtual_address + text.virtual_size;
                let start = self.relocs.binary_search_by(|x| match x.value >= array_ptr {
                    true => Ordering::Greater,
                    false => Ordering::Less,
                }).unwrap_err();
                let refs = (&self.relocs[start..]).iter()
                    .take_while(|x| x.value == array_ptr)
                    .map(|x| x.address);
                for address in refs {
                    if address >= text.virtual_address && address < text_end {
                        let rva = Rva((address.as_u64() - self.binary.base.as_u64()) as u32);
                        self.unchecked_refs.insert(rva);
                    }
                }
            }
        }
        Ok(())
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
            DatType::Upgrades => (&mut self.upgrades, 0x3d, &UPGRADE_ARRAY_WIDTHS),
            DatType::TechData => (&mut self.techdata, 0x2c, &TECHDATA_ARRAY_WIDTHS),
            _ => unimplemented!(),
        };
        entry.table_address = table_address;
        entry.entry_size = entry_size;
        for i in 0..entry.field_count {
            let entry_address = table_address + i * entry_size;
            let array_ptr = self.binary.read_address(entry_address)
                .map_err(|_| ())?;
            self.array_lookup.insert(array_ptr, (dat, i as u8));

            if dat == DatType::Units {
                // TODO
                continue;
            }

            // DatTable size value. DatTable ptr isn't needed since it's also a global ref
            self.result.patches.push(DatPatch::EntryCount(DatEntryCountPatch {
                dat,
                size_bytes: 4,
                multiply: 1,
                address: entry_address + E::VirtualAddress::SIZE + 4,
            }));

            // Global refs
            let field_size = field_sizes[i as usize];
            let end_ptr = array_ptr + entry_count * field_size as u32;
            self.add_dat_global_refs(dat, i as u8, array_ptr, end_ptr, field_size, true);
        }
        Ok(())
    }

    fn add_dat_global_refs(
        &mut self,
        dat: DatType,
        field_id: u8,
        array_ptr: E::VirtualAddress,
        end_ptr: E::VirtualAddress,
        field_size: u8,
        add_unchecked_ref_analysis: bool,
    ) {
        let start = self.relocs.binary_search_by(|x| match x.value >= array_ptr {
            true => Ordering::Greater,
            false => Ordering::Less,
        }).unwrap_err();
        let refs = (&self.relocs[start..]).iter()
            .take_while(|x| x.value < end_ptr);
        let text = self.text;
        let text_end = text.virtual_address + text.virtual_size;
        for reloc in refs {
            let address = reloc.address;
            let offset_bytes = (reloc.value.as_u64() - array_ptr.as_u64()) as i32;
            let offset = offset_bytes / field_size as i32;
            let byte_offset = offset_bytes as u32 % field_size as u32;
            self.result.patches.push(DatPatch::Array(DatArrayPatch {
                dat,
                field_id,
                address,
                entry: offset,
                byte_offset,
            }));
            // Assuming that array ref analysis for hardcoded indices isn't important.
            // (It isn't as of this writing)
            // Adding them as well would require better entry_of results as currently
            // they are checked by looking up the array_lookup hashtable which only contains
            // offset 0 addresses.
            if add_unchecked_ref_analysis && offset_bytes == 0 {
                if address >= text.virtual_address && address < text_end {
                    let rva = Rva((address.as_u64() - self.binary.base.as_u64()) as u32);
                    self.unchecked_refs.insert(rva);
                }
            }
        }
    }

    fn add_patches_from_code_refs(&mut self) {
        let functions = self.analysis.functions();
        let binary = self.binary;
        loop {
            let rva = match self.unchecked_refs.iter().next() {
                Some(&s) => s,
                None => break,
            };
            self.unchecked_refs.remove(&rva);
            let address = binary.base + rva.0;
            entry_of_until(binary, &functions, address, |entry| {
                if entry == self.update_status_screen_tooltip {
                    return EntryOf::Ok(());
                }
                let entry_rva = Rva((entry.as_u64() - binary.base.as_u64()) as u32);
                if !self.analyzed_functions.contains_key(&entry_rva) {
                    self.analyze_function(entry, address, DatFuncAnalysisMode::ArrayIndex)
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
        let mut analyzer =
            DatReferringFuncAnalysis::new(self, self.text, entry, ref_address, mode);
        analysis.analyze(&mut analyzer);
        analyzer.generate_needed_patches(analysis);
        let result = analyzer.result;
        let state = analyzer.state;
        let entry_rva = Rva((entry.as_u64() - binary.base.as_u64()) as u32);
        self.analyzed_functions.insert(entry_rva, state);
        result
    }

    fn add_u8_func_patches(&mut self) {
        let functions = self.analysis.functions();
        let binary = self.binary;
        let mut checked_funcs = FxHashSet::with_capacity_and_hasher(64, Default::default());
        let funcs = mem::replace(&mut self.u8_funcs, Vec::new());
        for &func_rva in &funcs {
            let func = binary.base + func_rva.0;
            let callers = crate::find_callers(self.analysis, func);
            for &address in &callers {
                entry_of_until(binary, &functions, address, |entry| {
                    if entry == self.update_status_screen_tooltip {
                        return EntryOf::Ok(());
                    }
                    let entry_rva = Rva((entry.as_u64() - binary.base.as_u64()) as u32);
                    if !self.analyzed_functions.contains_key(&entry_rva) {
                        self.analyze_function(entry, address, DatFuncAnalysisMode::ArrayIndex);
                    }
                    let mut result = EntryOf::Retry;
                    if let Some(mut state) = self.analyzed_functions.remove(&entry_rva) {
                        if state.has_called_func(func_rva) {
                            if checked_funcs.insert(entry_rva) {
                                let mut analyzer =
                                    DatReferringFuncAnalysis::rebuild(self, self.text, state);
                                for &rva in &funcs {
                                    if let Some(&index) =
                                        analyzer.state.calls_reverse_lookup.get(&rva)
                                    {
                                        analyzer.needed_func_results.insert(index);
                                    }
                                }
                                analyzer.generate_noncfg_patches();
                                state = analyzer.state;
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
        let functions = self.analysis.functions();
        let binary = self.binary;
        while let Some(child_func) = self.func_arg_widen_queue.pop() {
            let callers = crate::find_callers(self.analysis, child_func);
            for &address in &callers {
                if self.found_func_arg_widen_refs.contains(&address) {
                    continue;
                }
                entry_of_until(binary, &functions, address, |entry| {
                    if entry == self.update_status_screen_tooltip {
                        return EntryOf::Ok(());
                    }
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
                self.add_warning(format!("Cannot recognize function @ {:?}", address));
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
                let left = self.contains_u8_operand(arith.left);
                let right = self.contains_u8_operand(arith.right);
                if arith.ty == ArithOpType::And && arith.right.if_constant() == Some(0xff) {
                    left
                } else if left == right {
                    left
                } else {
                    None
                }
            }
            OperandType::Custom(c) => Some(U8Operand::Return(c)),
            OperandType::Memory(ref mem) if mem.size == MemAccessSize::Mem8 => {
                mem.address.if_arithmetic_add()
                    .and_then(|(l, r)| {
                        let constant = r.if_constant()?;
                        if let Some(arg_n) = arg_n_from_offset(constant) {
                            l.if_register().filter(|r| r.0 == 4)?;
                            Some(U8Operand::Arg(arg_n))
                        } else if constant > 0x4000 {
                            let addr = E::VirtualAddress::from_u64(constant);
                            let &(dat, field_id) = self.array_lookup.get(&addr)?;
                            match (dat, field_id) {
                                (DatType::Units, 0x0) | (DatType::Units, 0x11) |
                                (DatType::Units, 0x13) | (DatType::Orders, 0x0d) =>
                                    Some(U8Operand::DatField),
                                _ => None,
                            }
                        } else {
                            None
                        }
                    })
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
}

struct DatReferringFuncAnalysis<'a, 'b, 'e, E: ExecutionState<'e>> {
    dat_ctx: &'a mut DatPatchContext<'b, 'e, E>,
    state: Box<DatFuncAnalysisState>,
    ref_address: E::VirtualAddress,
    needed_stack_params: [Option<DatType>; 16],
    needed_func_results: FxHashSet<u32>,
    needed_cfg_analysis:
        Vec<(E::VirtualAddress, E::VirtualAddress, Option<Operand<'e>>, DatType)>,
    result: EntryOf<()>,
    binary: &'e BinaryFile<E::VirtualAddress>,
    text: &'e BinarySection<E::VirtualAddress>,
    current_branch: E::VirtualAddress,
    entry: E::VirtualAddress,
    /// Buffer hooks after all other patches to be sure that we don't add a longjump
    /// hook which prevents another patch.
    ///
    /// 2 step hooks require a 10 byte free block from somewhere, but just
    /// taking one while asking for a hook could end up taking an address
    /// that would need to be hooked.
    /// So buffer 2step hooks and do them last.
    pending_hooks: Vec<(E::VirtualAddress, u32, u8, u8)>,
    is_update_status_screen_tooltip: bool,
    switch_table: E::VirtualAddress,
    mode: DatFuncAnalysisMode,
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
enum DatFuncAnalysisMode {
    ArrayIndex,
    FuncArg,
}

/// State that can be saved away while other analysises are ran
struct DatFuncAnalysisState {
    // Eax from calls is written as Custom(index_to_calls_vec)
    // to distinguish them from undefs that come from state merges
    calls: Vec<Rva>,
    calls_reverse_lookup: FxHashMap<Rva, u32>,
    /// Address ranges which can't be patched over. Either because they have a
    /// patch/hook already, or they are a jump destination.
    /// (Jump destinations can be patched over if the patch starts at the start
    /// of the range)
    required_stable_addresses: RangeList<Rva, IsJumpDest>,
    next_cfg_custom_id: u32,
    u8_instruction_lists: InstructionLists<U8Operand>,
}

impl DatFuncAnalysisState {
    fn has_called_func(&self, rva: Rva) -> bool {
        self.calls_reverse_lookup.contains_key(&rva)
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
enum IsJumpDest {
    Yes,
    No,
}

/// More or less equivalent to HashMap<Key, Vec<Rva>>,
/// but allocates only a single Vec.
struct InstructionLists<Key: Hash + Eq> {
    heads: FxHashMap<Key, usize>,
    /// usize is link to the next operand, or !0 if end of list
    store: Vec<(Rva, usize)>,
    /// Avoid adding same Rva to the list twice
    used_addresses: FxHashSet<Rva>,
}

impl<'a, 'b, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    DatReferringFuncAnalysis<'a, 'b, 'e, E>
{
    type State = analysis::DefaultState;
    type Exec = E;
    fn operation(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: &Operation<'e>) {
        let ctx = ctrl.ctx();
        if self.is_update_status_screen_tooltip {
            match *op {
                Operation::Call(dest) => {
                    let arg_cache = &self.dat_ctx.analysis.arg_cache;
                    let arg1 = ctrl.resolve(arg_cache.on_call(0));
                    let arg2 = ctrl.resolve(arg_cache.on_call(1));
                    let (word_size, init_cap) = match E::VirtualAddress::SIZE {
                        4 => (MemAccessSize::Mem32, 0x8000_000f),
                        _ => (MemAccessSize::Mem64, 0x8000_0000_0000_000f),
                    };
                    let arg2_capacity = ctrl.read_memory(
                        ctx.add_const(arg2, 2 * E::VirtualAddress::SIZE as u64),
                        word_size,
                    );
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
        let ref_addr = self.ref_address;
        let ins_address = ctrl.address();
        if ins_address == self.switch_table {
            // Executed to switch table cases, stop
            ctrl.skip_operation();
            ctrl.end_branch();
            return;
        }
        if ref_addr >= ins_address && ref_addr < ctrl.current_instruction_end() {
            self.result = EntryOf::Ok(());
        }
        match *op {
            Operation::Move(ref dest, val, None) => {
                if self.mode == DatFuncAnalysisMode::ArrayIndex {
                    self.check_array_ref(ctrl, val);
                    if let DestOperand::Memory(mem) = dest {
                        if let Some(op) = mem.address.if_arithmetic_add().map(|x| x.1) {
                            self.check_array_ref(ctrl, op);
                        }
                    }
                }
                // Check l/r separately if the instruction has two operands
                // Ignore ands since they're likely low registers and not
                // real 2-operand instructions
                match *val.ty() {
                    OperandType::Arithmetic(ref arith) if arith.ty != ArithOpType::And => {
                        // This shares quite a lot of code with flags below..
                        let left = ctrl.resolve(arith.left);
                        let right = ctrl.resolve(arith.right);
                        self.check_u8_instruction(ctrl, left, arith.left);
                        self.check_u8_instruction(ctrl, right, arith.right);
                        if self.mode == DatFuncAnalysisMode::ArrayIndex {
                            let new_left = self.check_memory_read(ctrl, left);
                            let new_right = self.check_memory_read(ctrl, right);
                            if new_left.is_some() || new_right.is_some() {
                                let left = new_left.unwrap_or(left);
                                let right = new_right.unwrap_or(right);
                                ctrl.skip_operation();
                                let state = ctrl.exec_state();
                                let new = ctx.arithmetic(arith.ty, left, right);
                                state.move_resolved(dest, new);
                            }
                        }
                    }
                    _ => {
                        let resolved = ctrl.resolve(val);
                        self.check_u8_instruction(ctrl, resolved, val);
                        if self.mode == DatFuncAnalysisMode::ArrayIndex {
                            let new = self.check_memory_read(ctrl, resolved);
                            if let Some(new) = new {
                                ctrl.skip_operation();
                                let state = ctrl.exec_state();
                                state.move_resolved(dest, new);
                            }
                        }
                    }
                }
            }
            Operation::SetFlags(arith, arith_size)
                if arith.ty == ArithOpType::Sub || arith.ty == ArithOpType::And =>
            {
                let left = ctrl.resolve(arith.left);
                let right = ctrl.resolve(arith.right);
                self.check_u8_instruction(ctrl, left, arith.left);
                self.check_u8_instruction(ctrl, right, arith.right);

                if self.mode == DatFuncAnalysisMode::ArrayIndex {
                    let new_left = self.check_memory_read(ctrl, left);
                    let new_right = self.check_memory_read(ctrl, right);
                    if new_left.is_some() || new_right.is_some() {
                        let left = new_left.unwrap_or(left);
                        let right = new_right.unwrap_or(right);
                        ctrl.skip_operation();
                        let state = ctrl.exec_state();
                        let new_arith = ArithOperand {
                            left,
                            right,
                            ty: arith.ty,
                        };
                        state.set_flags_resolved(&new_arith, arith_size);
                    }
                }
            }
            Operation::Call(dest) => {
                if let Some(dest) = ctrl.resolve(dest).if_constant() {
                    let dest = E::VirtualAddress::from_u64(dest);
                    if self.mode == DatFuncAnalysisMode::FuncArg {
                        if let Some(&args) = self.dat_ctx.func_arg_widen_requests.get(&dest) {
                            for (i, dat) in args.iter()
                                .cloned()
                                .enumerate()
                                .filter_map(|x| Some((x.0, x.1?)))
                            {
                                let arg_cache = &self.dat_ctx.analysis.arg_cache;
                                let arg_loc = arg_cache.on_call(i as u8);
                                let value = ctrl.resolve(arg_loc);
                                self.dat_ctx.found_func_arg_widen_refs.insert(ctrl.address());
                                self.check_func_argument(ctrl, arg_loc, value, dat);
                            }
                        }
                    }
                    if let Some(custom) = self.custom_value_for_call(dest) {
                        ctrl.skip_operation();
                        let exec_state = ctrl.exec_state();
                        exec_state.move_to(
                            &DestOperand::Register64(scarf::operand::Register(0)),
                            custom,
                        );
                    }
                }
            }
            Operation::Jump { condition, to } => {
                if let Some(to) = ctrl.resolve(to).if_constant() {
                    let to = E::VirtualAddress::from_u64(to);
                    if let Some(len) = self.instruction_length(to) {
                        let end = to + len as u32;
                        if let Err(e) =
                            self.try_add_required_stable_address(to, end, IsJumpDest::Yes)
                        {
                            let e = (e.0, e.1, *e.2);
                            let input = (to, end, IsJumpDest::Yes);
                            if e != input {
                                // Accept jumps inside a jump dest, as those are sometimes
                                // generated
                                let accept =
                                    (e.2 == IsJumpDest::Yes && e.0 <= input.0 && e.1 >= input.1) ||
                                    (e.2 == IsJumpDest::Yes && e.0 >= input.0 && e.1 <= input.1);
                                if !accept {
                                    self.add_warning(
                                        format!(
                                            "Overlapping stable addresses {:?} {:?}",
                                            e, input
                                        ),
                                    );
                                }
                            }
                        }
                    }
                }
                // A bit hacky fix to register switch table locations to prevent certain
                // noreturn code from executing them.
                // Probably could be better to have analysis to recognize that noreturn
                // function instead of relying control flow from it reaching switch table.
                if let Some(address) = ctrl.if_mem_word(to) {
                    let address = ctrl.resolve(address);
                    if let Some((index, base)) = address.if_arithmetic_add() {
                        let index = index.if_arithmetic_mul()
                            .and_then(|(l, r)| {
                                r.if_constant()
                                    .filter(|&c| c == E::VirtualAddress::SIZE as u64)?;
                                Some(l)
                            });
                        if let (Some(c), Some(index)) = (base.if_constant(), index) {
                            let exec_state = ctrl.exec_state();
                            if exec_state.value_limits(index).0 == 0 {
                                self.switch_table = E::VirtualAddress::from_u64(c);
                            }
                        }
                    }
                }
                if self.mode == DatFuncAnalysisMode::ArrayIndex {
                    let condition = ctrl.resolve(condition);
                    let make_jump_unconditional = condition.if_arithmetic_gt()
                        .and_then(|(l, r)| {
                            // limit > value should be converted to always jump
                            l.if_constant()
                                .and_then(|c| {
                                    Some((true, r, match c {
                                        0xe4 => DatType::Units,
                                        0x82 => DatType::Weapons,
                                        0xd1 => DatType::Flingy,
                                        0x205 => DatType::Sprites,
                                        0x3e7 => DatType::Images,
                                        0x3d => DatType::Upgrades,
                                        0x2c => DatType::TechData,
                                        0xdc => DatType::PortData,
                                        0xbd => DatType::Orders,
                                        _ => return None,
                                    }))
                                })
                                .or_else(|| {
                                    // value > last_valid should never jump
                                    r.if_constant()
                                        .and_then(|c| {
                                            Some((false, l, match c {
                                                0xe3 => DatType::Units,
                                                0x81 => DatType::Weapons,
                                                0xd0 => DatType::Flingy,
                                                0x204 => DatType::Sprites,
                                                0x3e6 => DatType::Images,
                                                0x3c => DatType::Upgrades,
                                                0x2b => DatType::TechData,
                                                0xdb => DatType::PortData,
                                                0xbc => DatType::Orders,
                                                _ => return None,
                                            }))
                                        })
                                })
                        });
                    if let Some((jump, _op, dat)) = make_jump_unconditional {
                        // TODO currently just assumes that those above constant checks are always
                        // dat limit checks
                        let address = ctrl.address();
                        let first_invalid_is_none = match dat {
                            DatType::Units | DatType::Weapons | DatType::Upgrades |
                                DatType::TechData => true,
                            _ => false,
                        };
                        match (jump, first_invalid_is_none) {
                            (true, false) => self.make_jump_unconditional(address),
                            (true, true) => self.make_jump_eq_neq(address, false),
                            (false, false) => self.nop(address),
                            (false, true) => self.make_jump_eq_neq(address, true),
                        }
                    }
                }
            }
            _ => (),
        }
    }

    fn branch_start(&mut self, ctrl: &mut Control<'e, '_, '_, Self>) {
        self.current_branch = ctrl.address();
    }
}

impl<'a, 'b, 'e, E: ExecutionState<'e>> DatReferringFuncAnalysis<'a, 'b, 'e, E> {
    pub fn new(
        dat_ctx: &'a mut DatPatchContext<'b, 'e, E>,
        text: &'e BinarySection<E::VirtualAddress>,
        entry: E::VirtualAddress,
        ref_address: E::VirtualAddress,
        mode: DatFuncAnalysisMode,
    ) -> DatReferringFuncAnalysis<'a, 'b, 'e, E> {
        let binary = dat_ctx.binary;
        DatReferringFuncAnalysis {
            dat_ctx,
            ref_address,
            needed_stack_params: [None; 16],
            needed_func_results: Default::default(),
            needed_cfg_analysis: Default::default(),
            result: EntryOf::Retry,
            binary,
            text,
            current_branch: entry,
            entry: entry,
            pending_hooks: Vec::new(),
            is_update_status_screen_tooltip: false,
            switch_table: E::VirtualAddress::from_u64(0),
            mode,
            state: Box::new(DatFuncAnalysisState {
                calls: Vec::with_capacity(64),
                calls_reverse_lookup:
                    FxHashMap::with_capacity_and_hasher(64, Default::default()),
                required_stable_addresses: RangeList::with_capacity(64),
                u8_instruction_lists: InstructionLists {
                    heads: FxHashMap::with_capacity_and_hasher(32, Default::default()),
                    store: Vec::with_capacity(128),
                    used_addresses:
                        FxHashSet::with_capacity_and_hasher(64, Default::default()),
                },
                next_cfg_custom_id: 0,
            }),
        }
    }

    pub fn rebuild(
        dat_ctx: &'a mut DatPatchContext<'b, 'e, E>,
        text: &'e BinarySection<E::VirtualAddress>,
        state: Box<DatFuncAnalysisState>,
    ) -> DatReferringFuncAnalysis<'a, 'b, 'e, E> {
        let binary = dat_ctx.binary;
        DatReferringFuncAnalysis {
            dat_ctx,
            ref_address: E::VirtualAddress::from_u64(0),
            needed_stack_params: [None; 16],
            needed_func_results: Default::default(),
            needed_cfg_analysis: Default::default(),
            result: EntryOf::Retry,
            binary,
            text,
            current_branch: E::VirtualAddress::from_u64(0),
            entry: E::VirtualAddress::from_u64(0),
            pending_hooks: Vec::new(),
            is_update_status_screen_tooltip: false,
            switch_table: E::VirtualAddress::from_u64(0),
            state,
            mode: DatFuncAnalysisMode::ArrayIndex,
        }
    }

    fn add_warning(&mut self, msg: String) {
        self.dat_ctx.add_warning(msg);
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
                let warn =
                    format!("Required stable address overlap: {:?} vs {:?}", e, (start, end));
                self.add_warning(warn);
            }
        }
    }

    fn try_add_required_stable_address_for_patch(
        &mut self,
        start: E::VirtualAddress,
        end: E::VirtualAddress,
    ) -> Result<(), (E::VirtualAddress, E::VirtualAddress)> {
        match self.try_add_required_stable_address(start, end, IsJumpDest::No) {
            Ok(()) => Ok(()),
            Err(e) => {
                if e.0 == start && e.1 >= end && *e.2 == IsJumpDest::Yes {
                    *e.2 = IsJumpDest::No;
                    Ok(())
                } else if e.0 == start && e.1 < end && *e.2 == IsJumpDest::Yes {
                    // Can potentially grow this to contain this entire range.
                    let start = Rva((start.as_u64() - self.binary.base.as_u64()) as u32);
                    let end = Rva((end.as_u64() - self.binary.base.as_u64()) as u32);
                    if let Err(e2) =
                        self.state.required_stable_addresses.grow(start, end, IsJumpDest::No)
                    {
                        let start = self.binary.base + (e2.0).0;
                        let end = self.binary.base + (e2.1).0;
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

    fn try_add_required_stable_address(
        &mut self,
        start: E::VirtualAddress,
        end: E::VirtualAddress,
        is_jump_dest: IsJumpDest,
    ) -> Result<(), (E::VirtualAddress, E::VirtualAddress, &mut IsJumpDest)> {
        let start = Rva((start.as_u64() - self.binary.base.as_u64()) as u32);
        let end = Rva((end.as_u64() - self.binary.base.as_u64()) as u32);
        if let Err(old_range) =
            self.state.required_stable_addresses.add(start, end, is_jump_dest)
        {
            let start = self.binary.base + (old_range.0).0;
            let end = self.binary.base + (old_range.1).0;
            Err((start, end, old_range.2))
        } else {
            Ok(())
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
        value: Operand<'e>,
    ) -> Option<Operand<'e>> {
        let mem = match value.if_memory() {
            Some(s) => s,
            None => return None,
        };

        let size_bytes = mem.size.bits() / 8;
        let base_index = mem.address.if_arithmetic_add()
            .and_then(|(l, r)| {
                let base = r.if_constant()?;
                if size_bytes == 1 {
                    Some((base, l))
                } else {
                    let index = if l.is_undefined() {
                        l
                    } else {
                        l.if_arithmetic_mul_const(size_bytes as u64)?
                    };
                    Some((base, index))
                }
            });
        let (base, index) = match base_index {
            Some(s) => s,
            None => return None,
        };
        let addr = E::VirtualAddress::from_u64(base);
        if let Some(&(dat, _field_id)) = self.dat_ctx.array_lookup.get(&addr) {
            self.reached_array_ref_32(ctrl, addr);
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
                    let r = get_8bit_from_ors(r);
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
        let value = get_8bit_from_ors(orig_value);
        if value != orig_value {
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
                self.add_warning(
                    format!("Unknown {:?} dat offset @ {:?}: {}", dat, ctrl.address(), value),
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
            .and_then(|x| x.address.if_arithmetic_sub())
            .and_then(|(l, r)| {
                r.if_constant().filter(|&c| c < 0x2000)?;
                l.if_register()
            })
            .filter(|r| r.0 == 4)
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

        let mem_offset = value.if_memory()
            .and_then(|mem| {
                mem.address.if_arithmetic_add()
                    .and_then(|(l, r)| {
                        let offset = r.if_constant()?;
                        Some((l, offset))
                    })
                    .or_else(|| {
                        if let Some(c) = mem.address.if_constant() {
                            Some((ctx.const_0(), c))
                        } else {
                            Some((mem.address, 0))
                        }
                    })
                    .map(|(base, offset)| (base, offset, mem.size))
            });
        // -- Check arguments and struct offsets --
        if let Some((base, offset, size)) = mem_offset {
            return self.check_mem_widen_value(ctrl, base, offset, size, dat)
                .map(|()| None);
        }
        // -- Check return value --
        let custom = value.if_arithmetic_and_const(0xff)
            .and_then(|x| x.if_custom())
            .or_else(|| value.if_custom());
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

    fn check_mem_widen_value(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        base: Operand<'e>,
        offset: u64,
        size: MemAccessSize,
        dat: DatType,
    ) -> Result<(), ()> {
        fn is_status_screen_data(op: Operand<'_>) -> bool {
            // Mem32[arg1 + 0x40]
            op.if_mem32()
                .and_then(|addr| addr.if_arithmetic_add_const(0x40))
                .and_then(|base| base.if_mem32())
                .and_then(|x| x.if_arithmetic_add_const(4))
                .and_then(|x| x.if_register())
                .filter(|x| x.0 == 4)
                .is_some()
        }

        let is_stack = base.if_register().filter(|x| x.0 == 4).is_some();
        if is_stack {
            if let Some(arg) = arg_n_from_offset(offset).map(|x| x as usize) {
                if arg < self.needed_stack_params.len() {
                    self.needed_stack_params[arg] = Some(dat);
                }
            }
            return Ok(());
        }
        if size == MemAccessSize::Mem8 {
            if offset == 0x60 && dat == DatType::Weapons {
                // Most likely Bullet.weapon_id, todo
                return Ok(());
            } else if offset == 0xc8 && dat == DatType::TechData {
                // Unit.building_union.current_tech, todo
                return Ok(());
            } else if offset == 0xc9 && dat == DatType::Upgrades {
                // Unit.building_union.current_upgrade, todo
                return Ok(());
            } else if offset == 8 && dat == DatType::Weapons && is_status_screen_data(base) {
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
                        .filter(|x| match **x {
                            // units_dat_flingy is u8 for now
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
                        })
                        .is_some();
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
        if let Some(c) = val.if_constant().filter(|&c| c > 0x10000) {
            let addr = E::VirtualAddress::from_u64(c);
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
        let mut imm_addr = ctrl.current_instruction_end() - 4;
        while imm_addr > ctrl.address() {
            if let Ok(imm) = self.binary.read_u32(imm_addr) {
                if imm == array_addr.as_u64() as u32 {
                    let rva = Rva((imm_addr.as_u64() - self.binary.base.as_u64()) as u32);
                    self.dat_ctx.unchecked_refs.remove(&rva);
                    return;
                }
            }
            imm_addr = imm_addr - 1;
        }
    }

    fn generate_needed_patches(
        &mut self,
        analysis: FuncAnalysis<'e, E, analysis::DefaultState>,
    ) {
        if self.is_update_status_screen_tooltip {
            self.dat_ctx.result.patches.push(
                DatPatch::ReplaceFunc(self.entry, DatReplaceFunc::UpdateStatusScreenTooltip),
            );
            self.dat_ctx.update_status_screen_tooltip = self.entry;
            return;
        }
        let needed_cfg_analysis = mem::replace(&mut self.needed_cfg_analysis, Vec::new());
        if !needed_cfg_analysis.is_empty() {
            let (mut cfg, _) = analysis.finish();
            let mut checked_addresses = Vec::with_capacity(needed_cfg_analysis.len());
            let predecessors = cfg.predecessors();
            for (branch_start, address, op, dat) in needed_cfg_analysis {
                if !checked_addresses.contains(&address) {
                    checked_addresses.push(address);
                    self.do_cfg_analysis(&cfg, &predecessors, branch_start, address, op, dat);
                }
            }
        }
        self.generate_noncfg_patches();
        self.process_pending_hooks();
    }

    fn generate_noncfg_patches(&mut self) {
        let binary = self.binary;
        let needed_stack_params = self.needed_stack_params;
        let needed_func_results = mem::replace(&mut self.needed_func_results, Default::default());
        let u8_instruction_lists = mem::replace(
            &mut self.state.u8_instruction_lists,
            InstructionLists {
                heads: Default::default(),
                store: Default::default(),
                used_addresses: Default::default(),
            },
        );
        for (i, dat) in needed_stack_params.iter()
            .enumerate()
            .filter_map(|x| Some((x.0, (*x.1)?)))
        {
            self.dat_ctx.add_func_arg_widening_request(self.entry, i as u8, dat);
            for rva in u8_instruction_lists.iter(U8Operand::Arg(i as u8)) {
                let address = binary.base + rva.0;
                self.widen_instruction(address);
            }
        }
        for &custom_id in needed_func_results.iter() {
            // Func args may be added for extension unnecessarily
            for rva in u8_instruction_lists.iter(U8Operand::Return(custom_id)) {
                let address = binary.base + rva.0;
                self.widen_instruction(address);
            }
        }
        for rva in u8_instruction_lists.iter(U8Operand::DatField) {
            let address = binary.base + rva.0;
            self.widen_instruction(address);
        }
        self.state.u8_instruction_lists = u8_instruction_lists;
    }

    fn do_cfg_analysis(
        &mut self,
        cfg: &Cfg<'e, E, analysis::DefaultState>,
        predecessors: &scarf::cfg::Predecessors,
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
        // This may(?) infloop under certain conditions, so have a hard limit of
        // branches to go through before quitting.
        let mut limit = 64;
        let mut analyzer = CfgAnalyzer {
            branch,
            final_address,
            needed_operand,
            resolved_dest_address: None,
            unchecked_branches: Vec::with_capacity(32),
            added_unchecked_branches: FxHashSet::with_capacity_and_hasher(32, Default::default()),
            parent: self,
            instruction_lists: InstructionLists {
                heads: FxHashMap::with_capacity_and_hasher(32, Default::default()),
                store: Vec::with_capacity(128),
                used_addresses:
                    FxHashSet::with_capacity_and_hasher(64, Default::default()),
            },
            cfg,
            predecessors,
            assigning_instruction: None,
            rerun_branch: None,
            ending: false,
            dat,
        };
        let orig_branch = branch;
        let orig_final = final_address;

        let mut analysis = FuncAnalysis::new(binary, ctx, branch);
        analysis.analyze(&mut analyzer);
        while let Some((branch, operand, final_address, resolved_dest)) =
            analyzer.unchecked_branches.pop()
        {
            if limit == 0 {
                self.add_warning(
                    format!("CFG analysis of {:?} / {:?} took too long", orig_branch, orig_final),
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
                self.add_warning(format!("Can't uncond @ {:?}", address));
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
            self.add_warning(format!("Can't uncond @ {:?}", address));
        }
    }

    fn make_jump_unconditional(&mut self, address: E::VirtualAddress) {
        if !self.dat_ctx.patched_addresses.insert(address) {
            return;
        }

        let bytes = match self.binary.slice_from_address(address, 0x10) {
            Ok(o) => o,
            Err(_) => {
                self.add_warning(format!("Can't uncond @ {:?}", address));
                return;
            }
        };
        assert!(bytes.len() == 0x10);

        if bytes[0] == 0x0f && matches!(bytes[1], 0x80 ..= 0x8f) {
            self.add_patch(address, &[0x90, 0xe9, bytes[2], bytes[3], bytes[4], bytes[5]], 6);
        } else if matches!(bytes[0], 0x70 ..= 0x7f) {
            self.add_patch(address, &[0xeb, bytes[1]], 2);
        } else {
            self.add_warning(format!("Can't uncond @ {:?}", address));
        }
    }

    fn instruction_length(&mut self, address: E::VirtualAddress) -> Option<u8> {
        use lde::Isa;

        let bytes = self.binary.slice_from_address(address, 0x10).ok()?;
        Some(lde::X86::ld(bytes) as u8)
    }

    fn nop(&mut self, address: E::VirtualAddress) {
        if !self.dat_ctx.patched_addresses.insert(address) {
            return;
        }
        let ins_len = match self.instruction_length(address) {
            Some(s) => s,
            None => return,
        };
        let nops = [0x90; 0x10];
        self.add_patch(address, &nops[..ins_len as usize], ins_len);
    }

    fn widen_instruction(&mut self, address: E::VirtualAddress) {
        use lde::Isa;

        fn is_struct_field_rm(bytes: &[u8]) -> bool {
            // Just checking if the base register != ebp but still a memory access
            let base = bytes[1] & 0x7;
            base != 5 && bytes[1] & 0xc0 != 0xc0
        }

        if !self.dat_ctx.patched_addresses.insert(address) {
            return;
        }

        let bytes = match self.binary.slice_from_address(address, 0x18) {
            Ok(o) => o,
            Err(_) => {
                self.add_warning(format!("Can't widen instruction @ {:?}", address));
                return;
            }
        };
        let ins_len = lde::X86::ld(bytes) as u8;
        match *bytes {
            // movzx to mov
            [0x0f, 0xb6, ..] => {
                if !is_struct_field_rm(&bytes[1..]) {
                    let mut patch = [0x90u8; 8];
                    for i in 0..8 {
                        patch[i] = bytes[i];
                    }
                    patch[0] = 0x90;
                    patch[1] = 0x8b;
                    self.fixup_instruction_rm(&mut patch[1..]);
                    self.add_patch(address, &patch, ins_len);
                }
            }
            // add rm8, r8; cmp r8, rm8; cmp rm8, r8
            [0x00, ..] | [0x3a, ..] | [0x38, ..] => {
                if !is_struct_field_rm(&bytes) {
                    let mut patch = [0x90u8; 8];
                    for i in 0..8 {
                        patch[i] = bytes[i];
                    }
                    patch[0] += 1;
                    self.fixup_instruction_rm(&mut patch);
                    self.add_patch(address, &patch, ins_len);
                }
            }
            // cmp al, constant
            // I think it's safe to assume it's never going to be a signed gt/lt
            [0x3c, constant, ..] => {
                let patch = &[0x3d, constant, 0x00, 0x00, 0x00];
                self.add_hook(address, 2, patch);
            }
            // arith rm32, constant
            [0x80, ..] => {
                let mut patch = [0x90; 12];
                patch[0] = 0x81;
                for i in 1..ins_len {
                    patch[i as usize] = bytes[i as usize];
                }
                for i in ins_len..(ins_len + 3) {
                    patch[i as usize] = 0x00;
                }
                self.fixup_instruction_rm(&mut patch);
                self.add_hook(address, ins_len, &patch);
            }
            // test rm8, r8
            [0x84, second, ..] => {
                // Going to only support test r8low with itself for now
                if second & 0xc0 == 0xc0 && second & 0x7 == (second >> 3) & 0x7 {
                    self.add_patch(address, &[0x85, second], ins_len);
                }
            }
            // mov r8, rm8, to mov r32, rm32
            [0x8a, ..] => {
                let mut patch = [0x90; 8];
                if is_struct_field_rm(&bytes) {
                    // Convert to movzx r32, rm8
                    for i in 0..(ins_len as usize) {
                        patch[i + 1] = bytes[i];
                    }
                    patch[0] = 0x0f;
                    patch[1] = 0xb6;
                    self.fixup_instruction_rm(&mut patch[1..]);
                    self.add_hook(address, ins_len, &patch);
                } else {
                    for i in 0..8 {
                        patch[i] = bytes[i];
                    }
                    patch[0] = 0x8b;
                    self.fixup_instruction_rm(&mut patch);
                    self.add_patch(address, &patch, ins_len);
                }
            }
            // mov rm8, r8
            [0x88, ..] => {
                if !is_struct_field_rm(&bytes) {
                    let mut patch = [0u8; 8];
                    for i in 0..8 {
                        patch[i] = bytes[i];
                    }
                    patch[0] = 0x89;
                    self.fixup_instruction_rm(&mut patch);
                    self.add_patch(address, &patch, ins_len);
                }
            }
            // mov rm8, const8
            [0xc6, ..] => {
                if !is_struct_field_rm(&bytes) {
                    let mut patch = [0x90; 16];
                    for i in 0..(ins_len as usize) {
                        patch[i] = bytes[i];
                    }
                    patch[0] = 0xc7;
                    for i in ins_len..(ins_len + 3) {
                        patch[i as usize] = 0x00;
                    }
                    self.fixup_instruction_rm(&mut patch);
                    self.add_hook(address, ins_len, &patch[..(ins_len as usize + 3)]);
                }
            }
            // mov r8, const8
            [0xb0, ..] | [0xb1, ..] | [0xb2, ..] | [0xb3, ..] => {
                let mut patch = [0x00; 5];
                patch[0] = bytes[0] + 8;
                patch[1] = bytes[1];
                self.add_hook(address, ins_len, &patch);
            }
            // Already u32 moves
            [0x89, ..] | [0x8b, ..] | [0xc7, ..] => (),
            // Push reg
            [x, ..] if x >= 0x50 && x < 0x58 => (),
            // Push any
            [0xff, x, ..] if (x >> 3) & 7 == 6 => (),
            _ => self.add_warning(format!("Can't widen instruction @ {:?}", address)),
        }
    }

    /// Modifies any offset in form of [ebp +/- x] so that x becomes 4-aligned,
    /// as sometimes 1byte values are stored at aligned address.
    /// Hopefully there aren't any other 1byte values that get overwritten by this;
    /// at least that seems to be rare.
    fn fixup_instruction_rm(&mut self, bytes: &mut [u8]) {
        let base = bytes[1] & 0x7;
        match (bytes[1] & 0xc0) >> 6 {
            1 | 2 => {
                match base {
                    // sib
                    4 => bytes[3] &= !0x3,
                    _ => bytes[2] &= !0x3,
                }
            }
            _ => (),
        }
    }

    /// NOTE: Address should be start of a instruction, and the patch should be long
    /// enough to cover the entire instruction even if some later bytes are redundant.
    /// Needed due to marking that instruction as required_stable_address
    fn add_patch(&mut self, address: E::VirtualAddress, patch: &[u8], len: u8) {
        self.add_required_stable_address_for_patch(address, address + len as u32);
        let result = &mut self.dat_ctx.result;
        let patch = &patch[..len as usize];
        let code_bytes_offset = result.code_bytes.len() as u32;
        result.code_bytes.extend_from_slice(patch);
        result.patches.push(DatPatch::Replace(address, code_bytes_offset, len));
    }

    fn add_hook(&mut self, address: E::VirtualAddress, skip: u8, hook: &[u8]) {
        let result = &mut self.dat_ctx.result;
        let code_bytes_offset = result.code_bytes.len() as u32;
        result.code_bytes.extend_from_slice(hook);
        self.pending_hooks.push((address, code_bytes_offset, hook.len() as u8, skip));
    }

    fn process_pending_hooks(&mut self) {
        let mut pending_hooks = mem::replace(&mut self.pending_hooks, Vec::new());
        pending_hooks.sort_unstable_by_key(|x| x.0);
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
                        let result = &mut self.dat_ctx.result;
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
                self.add_warning(format!("Can't hook @ {:?}", address));
            } else if needs_short_jump {
                // Keep the pending hook for a second loop, move it to start of the vec
                pending_hooks[short_jump_hooks] = pending_hooks[i];
                short_jump_hooks += 1;
            } else {
                // Was added succesfully as a long hook
            }

            // Add hook return position as jump dest
            let return_pos = address + skip as u32;
            if let Some(len) = self.instruction_length(return_pos) {
                let _ = self.try_add_required_stable_address(
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
                    self.add_warning(format!("Can't find shortjmp space for {:?}", address));
                    continue;
                }
            };
            let result = &mut self.dat_ctx.result;
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
        for (start, end) in self.state.required_stable_addresses.iter() {
            let start = self.binary.base + start.0;
            let end = self.binary.base + end.0;
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
        if let Some(cand) = result {
            let bytes = self.binary.slice_from_address(cand, 0x20).ok()?;
            let mut len = 0;
            while len < 0xa {
                use lde::Isa;
                let slice = bytes.get(len as usize..)?;
                len += lde::X86::ld(slice);
            }
            self.add_required_stable_address_for_patch(cand, cand + len);
        }
        result
    }

    fn check_u8_instruction(
        &mut self,
        ctrl: &mut Control<'e, '_, '_, Self>,
        op: Operand<'e>,
        unresolved: Operand<'e>,
    ) {
        if !contains_u8(unresolved) {
            return;
        }
        if let Some(u8_op) = self.dat_ctx.contains_u8_operand(op) {
            let rva = Rva((ctrl.address().as_u64() - self.binary.base.as_u64()) as u32);
            self.state.u8_instruction_lists.add_check_used_address(u8_op, rva);
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

struct CfgAnalyzer<'a, 'b, 'c, 'e, E: ExecutionState<'e>> {
    branch: E::VirtualAddress,
    // Only used for the first branch when needed_operand is None
    final_address: E::VirtualAddress,
    // Used if doing CFG analysis for function argument instead of array index
    needed_operand: Option<Operand<'e>>,
    resolved_dest_address: Option<Operand<'e>>,
    unchecked_branches:
        Vec<(E::VirtualAddress, Operand<'e>, E::VirtualAddress, Option<Operand<'e>>)>,
    added_unchecked_branches:
        FxHashSet<(E::VirtualAddress, OperandHashByAddress<'e>, E::VirtualAddress)>,
    parent: &'a mut DatReferringFuncAnalysis<'b, 'c, 'e, E>,
    cfg: &'a Cfg<'e, E, analysis::DefaultState>,
    predecessors: &'a scarf::cfg::Predecessors,
    instruction_lists: InstructionLists<OperandHashByAddress<'e>>,
    assigning_instruction: Option<E::VirtualAddress>,
    rerun_branch: Option<(E::VirtualAddress, Operand<'e>, E::VirtualAddress)>,
    dat: DatType,
    ending: bool,
}

impl<'a, 'b, 'c, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    CfgAnalyzer<'a, 'b, 'c, 'e, E>
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
                self.check_u8_instruction(ctrl, resolved, val);
                if let DestOperand::Register8Low(r) = *dest {
                    // We want to also patch assignment like mov al, 82,
                    // but that isn't caught by check_u8_instruction
                    if let Some(op) = self.needed_operand {
                        if Operand::and_masked(op).0.if_register()
                            .filter(|x| x.0 == r.0)
                            .is_some()
                        {
                            self.instruction_lists.clear();
                            self.assigning_instruction = Some(address);
                            // Ask the branch to be rerun with
                            // self.final_address set to this instruction
                            // This operand should be unresolved, pretty sure..
                            self.rerun_branch = Some((self.branch, val, address));
                        }
                    }
                }
                if let DestOperand::Memory(ref mem) = *dest {
                    let matches = if let Some(resolved_dest) = self.resolved_dest_address {
                        resolved_dest == ctrl.resolve(mem.address)
                    } else {
                        self.needed_operand
                            .and_then(|x| x.if_memory())
                            .filter(|x| x.address == mem.address)
                            .is_some()
                    };
                    // Same for mov byte [esp - 4], al and such
                    if matches {
                        self.instruction_lists.clear();
                        self.assigning_instruction = Some(address);
                        self.rerun_branch = Some((self.branch, val, address));
                    }
                }
                if address == self.final_address {
                    if self.needed_operand.is_none() {
                        self.check_final_op(ctrl, resolved);
                    }
                }
            }
            Operation::SetFlags(arith, _size) => {
                let left = ctrl.resolve(arith.left);
                let right = ctrl.resolve(arith.right);
                self.check_u8_instruction(ctrl, left, arith.left);
                self.check_u8_instruction(ctrl, right, arith.right);
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
                        let exec_state = ctrl.exec_state();
                        exec_state.move_to(
                            &DestOperand::Register64(scarf::operand::Register(0)),
                            custom,
                        );
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

impl<'a, 'b, 'c, 'e, E: ExecutionState<'e>> CfgAnalyzer<'a, 'b, 'c, 'e, E> {
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
                    let is_esp_offset = mem.address.if_arithmetic_add()
                        .filter(|x| x.0.if_register().filter(|&r| r.0 == 4).is_some())
                        .and_then(|x| x.1.if_constant())
                        .filter(|&c| c < 0x200)
                        .is_some();
                    if is_esp_offset {
                        let addr = ctrl.resolve(mem.address);
                        let is_esp_offset = addr.if_arithmetic_sub()
                            .filter(|x| x.0.if_register().filter(|&r| r.0 == 4).is_some())
                            .and_then(|x| x.1.if_constant())
                            .filter(|&c| c < 0x200)
                            .is_some();
                        if is_esp_offset {
                            self.add_resolved_dest_redo(addr);
                        }
                    }
                }
            }
            let val = ctrl.resolve(op);
            self.finishing_branch(val);
        }
    }

    fn check_final_op(&mut self, ctrl: &mut Control<'e, '_, '_, Self>, op: Operand<'e>) {
        let index = match op.if_memory()
            .and_then(|x| x.address.if_arithmetic_add())
            .filter(|(_, r)| r.if_constant().is_some())
            .map(|(l, _)| {
                // Remove * 2 or * 4 if mem address is not byte
                l.if_arithmetic_mul()
                    .filter(|(_, r)| r.if_constant().is_some())
                    .map(|(l, _)| l)
                    .unwrap_or(l)
            })
        {
            Some(s) => s,
            None => return,
        };

        ctrl.end_analysis();
        self.finishing_branch(index);
    }

    fn finishing_branch(&mut self, op: Operand<'e>) {
        if let Some(address) = self.assigning_instruction.take() {
            self.parent.widen_instruction(address);
        }
        if let Some(s) = self.rerun_branch.take() {
            self.add_unchecked_branch(s.0, s.1, s.2);
        }
        match *Operand::and_masked(op).0.ty() {
            OperandType::Register(_) => (),
            OperandType::Memory(mem) => {
                let stack_offset = Some(())
                    .and_then(|()| {
                        if let Some((l, r)) = mem.address.if_arithmetic_add() {
                            Some((l.if_register()?, r.if_constant()?))
                        } else if let Some((l, r)) = mem.address.if_arithmetic_sub() {
                            Some((l.if_register()?, 0u64.wrapping_sub(r.if_constant()?)))
                        } else {
                            None
                        }
                    })
                    .or_else(|| Some((mem.address.if_register()?, 0)))
                    .filter(|&x| x.0.0 == 4 || x.0.0 == 5);
                match stack_offset {
                    Some((r, s)) if r.0 == 4 => {
                        // If this is an argument, then request all of its uses to be widened
                        // for parent.
                        if let Some(arg) = arg_n_from_offset(s).map(|x| x as usize) {
                            if arg < self.parent.needed_stack_params.len() {
                                self.parent.needed_stack_params[arg] = Some(self.dat);
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

        for rva in self.instruction_lists.iter(op.hash_by_address()) {
            let address = self.parent.binary.base + rva.0;
            self.parent.widen_instruction(address);
        }
        if let Some(own_branch_link) = self.cfg.get_link(self.branch) {
            for link in self.predecessors.predecessors(self.cfg, &own_branch_link) {
                self.add_unchecked_branch(link.address(), op, E::VirtualAddress::from_u64(0));
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
        if self.added_unchecked_branches.insert((address, op.hash_by_address(), final_address)) {
            self.unchecked_branches.push((address, op, final_address, None));
        }
    }

    fn add_resolved_dest_redo(&mut self, resolved: Operand<'e>) {
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
        for part in op.iter_no_mem_addr() {
            self.instruction_lists.add(part.hash_by_address(), rva);
        }
    }
}

impl<Key: Hash + Eq> InstructionLists<Key> {
    fn clear(&mut self) {
        self.heads.clear();
        self.store.clear();
        self.used_addresses.clear();
    }

    /// This probs shouldn't be part of InstructionLists but one level higher,
    /// if ever refactored.
    fn add_check_used_address(&mut self, key: Key, rva: Rva) {
        if !self.used_addresses.insert(rva) {
            return;
        }
        self.add(key, rva);
    }

    fn add(&mut self, key: Key, rva: Rva) {
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

    fn iter<'a>(&'a self, key: Key) -> impl Iterator<Item = Rva> + 'a {
        let index = self.heads.get(&key).cloned().unwrap_or(!0);
        U8InstructionListsIter(self, index)
    }
}

struct U8InstructionListsIter<'a, K: Hash + Eq>(&'a InstructionLists<K>, usize);

impl<'a, K: Hash + Eq> Iterator for U8InstructionListsIter<'a, K> {
    type Item = Rva;
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

struct RecognizeDatPatchFunc<'a, 'b, 'e, E: ExecutionState<'e>> {
    flags: u8,
    inlining: bool,
    inline_ok: bool,
    returns: Vec<Operand<'e>>,
    dat_ctx: &'a mut DatPatchContext<'b, 'e, E>,
}

const SUBUNIT_READ: u8 = 0x1;
const AIR_WEAPON_READ: u8 = 0x2;
const GROUND_WEAPON_READ: u8 = 0x4;
const ORDER_WEAPON_READ: u8 = 0x8;
const UNIT_ID_IS_INF_KERRIGAN: u8 = 0x10;

impl<'a, 'b, 'e, E: ExecutionState<'e>> analysis::Analyzer<'e> for
    RecognizeDatPatchFunc<'a, 'b, 'e, E>
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
                        let this_field = mem.address.if_arithmetic_add()
                            .filter(|(l, _)| l.if_register().filter(|x| x.0 == 1).is_some())
                            .and_then(|(_, r)| r.if_constant())
                            .filter(|&c| c < 0x400);
                        if let Some(offset) = this_field {
                            if offset == 0x70 {
                                self.flags |= SUBUNIT_READ;
                            }
                        }
                        let dat_field = mem.address.if_arithmetic_add()
                            .and_then(|(_, r)| r.if_constant())
                            .filter(|&c| c > 0x4000)
                            .map(|x| E::VirtualAddress::from_u64(x))
                            .and_then(|address| self.dat_ctx.array_lookup.get(&address));
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
                    let inf_kerry_cmp = crate::if_arithmetic_eq_neq(condition)
                        .map(|(l, r, _)| (l, r))
                        .and_either_other(|x| x.if_constant().filter(|&c| c == 0x33))
                        .and_then(|x| x.if_mem16())
                        .and_then(|x| x.if_arithmetic_add_const(0x64))
                        .is_some();
                    if inf_kerry_cmp {
                        self.flags |= UNIT_ID_IS_INF_KERRIGAN;
                    }
                }
                Operation::Return(_) => {
                    let ctx = ctrl.ctx();
                    let val = ctrl.resolve(ctx.register(0));
                    self.returns.push(val);
                }
                _ => (),
            }
        }
    }
}

impl<'a, 'b, 'e, E: ExecutionState<'e>> RecognizeDatPatchFunc<'a, 'b, 'e, E> {
    fn new(dat_ctx: &'a mut DatPatchContext<'b, 'e, E>) -> RecognizeDatPatchFunc<'a, 'b, 'e, E> {
        RecognizeDatPatchFunc {
            flags: 0,
            dat_ctx,
            inlining: false,
            inline_ok: false,
            returns: Vec::new(),
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
                    let (l, r) = mem.address.if_arithmetic_add()?;
                    l.if_register().filter(|r| r.0 == 1)?;
                    let offset = r.if_constant()?;
                    Some((offset, mem.size))
                });
            if let Some((offset, size)) = this_field {
                if offset == 0xc8 && size == MemAccessSize::Mem8 {
                    return Ok(Some(UnitCurrentTech));
                }
                if offset == 0xc9 && size == MemAccessSize::Mem8 {
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
fn arg_n_from_offset(constant: u64) -> Option<u8> {
    if constant < 0x40 && constant & 3 == 0 && constant != 0 {
        Some(constant as u8 / 4 - 1)
    } else {
        None
    }
}
