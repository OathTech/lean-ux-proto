import FiniteExecution
import Image
import AllowedipsImage
import ServiceImage
import Memory
import LookupProjection
import AllowedipsProjection
import AllowedipsSelection
import AllowedipsWords

/-! Named trust surface for the pinned lookup proof, under construction.
    These are explicit hypotheses, not globally asserted facts. No declaration
    here assumes the lookup result, a region's R-preservation, or a mirror run.
    Pre_lookup is accompanied by its concrete satisfying witness.
    The final milestone report must reproduce this file verbatim.

    External interpretation: binutils 2.42 supplied the literal AST and DWARF
    layouts from the ELF below. Lean checks execution of those terms, not the
    binutils decoder, DWARF producer, SHA computation or correspondence of
    Kraken's model with x86 hardware. The loader checks identity and branch
    encodings. Mutable runtime globals are NOT assumed equal to ELF initial
    bytes at a function entry; their current values belong in Pre_lookup.
    A fixed fetch models stable text; the external ELF interpretation requires
    no runtime text patch in these ranges. Independent review measured no
    alternatives entry in the ranges, no jump table, empty smp_locks, no RET
    thunk rewriting, and no GS use. These are interpretation facts, not unused
    Lean premises. Permissions and serialization below are headline hypotheses.

-/
namespace Binary.TrustBase

def krakenCommit : String := "7ebba06a30eaf08c10b26b28ca14bfee1c791576"
def kernelIdentity : String := "6b2018b9"
def elfSha256 : String := "16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774"
def decoderVersion : String := "GNU objdump (GNU Binutils for Ubuntu) 2.42"

local instance : Labels := Image.linkedLabels

/-- The partial linked decoder for both anchored functions and all reached
    service bodies. A rejected instruction remains a failing fetch; neither
    its semantics nor successful execution is assumed by this definition. -/
def pinnedFetch (pc : Int64) : Option Decoded :=
  (Image.fetch pc).orElse (fun _ => ServiceImage.fetch pc)

/-- The ambient decoder agrees with the pinned literal instructions/lengths.
    Interpreting those literals as this ELF is the external decoding assumption. -/
def AnchoredDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, Image.fetch pc = some instruction → fetch pc = some instruction

/-- External paging/access permissions, absent from Kraken MachineState. -/
structure Permissions where
  read : BitVec 64 → Width → Prop
  write : BitVec 64 → Width → Prop
  execute : Std.Rco Int64 → Prop

/-- Kraken's All grants permission requests. This separate premise makes
    that grant explicit for every effect, including every undefined outcome. -/
def AccessAllowed (permissions : Permissions) : Effects → Prop
  | .done _ => True
  | .unimplemented _ | .gp_unaligned .. | .nonmem_load .. | .nonmem_store .. => False
  | @Effects.undefined α _ next => ∀ value : α, AccessAllowed permissions (next value)
  | .require_read_access address width next =>
      permissions.read address width ∧ AccessAllowed permissions (next ())
  | .require_write_access address width next =>
      permissions.write address width ∧ AccessAllowed permissions (next ())
  | .require_exec_access pc next =>
      permissions.execute pc ∧ AccessAllowed permissions (next ())

/-- Every actually executed instruction has its requested accesses granted;
    the final return destination is not itself executed by this run. -/
def RunAccessAllowed (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, ∃ decoded, fetch s.pc = some decoded ∧
    permissions.execute ⟨s.pc, s.pc + .ofNat decoded.size⟩ ∧
    AccessAllowed permissions
      (decoded.instruction.interp s.data ⟨s.pc, s.pc + .ofNat decoded.size⟩
        (fun d => .done ⟨d, s.pc + .ofNat decoded.size⟩) (fun pc d => .done ⟨d, pc⟩))

/-- The environment places no interrupt, preemption or competing CPU action
    inside this anchored call; the records place such actions between calls. -/
structure SerializedEnvironment (onlineCPUs : Nat) (externalActions : List Nat) : Prop where
  singleCPU : onlineCPUs = 1
  noInterleaving : externalActions = []

/-- Permission safety of finite actual prefixes through the first outer RET.
    This is safety only: no termination, source result or relation is assumed.
    Service interiors are included; the unexecuted return destination is not. -/
def InvocationPermissions (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (initial : MachineState) (returnPC : Int64) : Prop :=
  ∀ history, ActualHistory fetch initial history → NoEarlyReturn returnPC history →
    RunAccessAllowed fetch permissions history

/-- The exported interpretation audit of this actual instruction history. -/
def RunEnvironment (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (onlineCPUs : Nat) (externalActions : List Nat) (history : List MachineState) : Prop :=
  SerializedEnvironment onlineCPUs externalActions ∧ RunAccessAllowed fetch permissions history

/-- Kernel ABI: the stack word is the actual CALL return address. Eight-byte
    alignment follows this kernel's compiler flags, not a userspace ABI guess. -/
def EntryFrame (s : MachineState) (returnAddress : UInt64) : Prop :=
  s.data.regs.rsp.toNat % 8 = 0 ∧
  s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 = some (returnAddress.toNat : Int)

/-- Only ABI-preserved registers are constrained; caller-save registers and
    flags may change. The callee has consumed the actual return-address word. -/
def Returned (entry final : MachineState) (returnAddress : UInt64) : Prop :=
  final.pc = .ofBitVec returnAddress.toBitVec ∧
  final.data.regs.rsp = entry.data.regs.rsp + 8 ∧
  final.data.regs.rbx = entry.data.regs.rbx ∧
  final.data.regs.rbp = entry.data.regs.rbp ∧
  final.data.regs.r12 = entry.data.regs.r12 ∧
  final.data.regs.r13 = entry.data.regs.r13 ∧
  final.data.regs.r14 = entry.data.regs.r14 ∧
  final.data.regs.r15 = entry.data.regs.r15

/-- Service internals emit no anchored observation or cut. The final state
    may return to an anchored address; it is deliberately not excluded. -/
def NoAnchoredReentry (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, Image.fetch s.pc = none

/-- A service contract uses the same fetched-instruction execution as the
    function proof. Its readiness and write footprint are physical predicates;
    their concrete instantiations must be part of the witnessed entry domain. -/
def ServiceReturns (fetch : Int64 → Option Decoded) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop) : Prop :=
  ∀ s returnAddress, s.pc = address → ready s → EntryFrame s returnAddress →
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧
        effect s t.machine ∧ NoAnchoredReentry t.history)
      ⟨s, [s]⟩

def preemptCountAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c8
def currentTaskAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c0
def softirqPendingAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85e0

inductive KcovKind where
  | pc | cmp1 | cmp4 | cmp8 | constCmp4 | constCmp1
  deriving DecidableEq

structure WordWrite where
  address : BitVec 64
  value : BitVec 64

def load64 (memory : Mem 64) (address : BitVec 64) : Option (BitVec 64) :=
  (memory.loadInt address 8).map (.ofInt 64)

def load32 (memory : Mem 64) (address : BitVec 64) : Option (BitVec 32) :=
  (memory.loadInt address 4).map (.ofInt 32)

/-- Physical callback metadata, fixed during an anchored call except for the
    separately balanced preempt count. Capacity is a count of 64-bit words. -/
structure KcovLayout where
  task : BitVec 64
  area : BitVec 64
  capacity : BitVec 32
  mode : BitVec 32
  softirqEnabled : BitVec 32

/-- Exact runtime metadata reads, not the ELF's initial global bytes. -/
def KcovMetadata (layout : KcovLayout) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some layout.task ∧
  load32 memory (layout.task + 0x6e0) = some layout.mode ∧
  load32 memory (layout.task + 0x6e4) = some layout.capacity ∧
  load64 memory (layout.task + 0x6e8) = some layout.area ∧
  load32 memory (layout.task + 0x704) = some layout.softirqEnabled

/-- Mapped buffer and bounded runtime header. A full buffer is allowed; no
    callback is required to have room for a record. This predicate says
    nothing about the peer state or the lookup result. -/
def KcovBuffer (layout : KcovLayout) (memory : Mem 64) : Prop :=
  (∀ word < layout.capacity.toNat,
    (memory.loadInt (layout.area + .ofNat 64 (8 * word)) 8).isSome = true) ∧
  ∃ count : Nat, count ≤ layout.capacity.toNat ∧
    load64 memory layout.area = some (.ofNat 64 count)

def KcovBufferBytes (layout : KcovLayout) : BitVec 64 → Prop :=
  InRange layout.area (8 * layout.capacity.toNat)

/-- Storage read by an active callback. Even capacity zero still requires
    the header; caller writes must preserve it as well as the buffer words. -/
def KcovStorageBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  InRange layout.area 8 address ∨ KcovBufferBytes layout address

def KcovMetadataBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 address ∨
  InRange (layout.task + 0x6e0) 4 address ∨
  InRange (layout.task + 0x6e4) 4 address ∨
  InRange (layout.task + 0x6e8) 8 address ∨
  InRange (layout.task + 0x704) 4 address

/-- Physical disjointness from protected memory (metadata, live stack and
    represented objects). Readiness is proved from this, not assumed at
    every callback. The caller chooses the actual protected footprint. -/
def KcovSeparated (layout : KcovLayout) (protectedBytes : BitVec 64 → Prop) : Prop :=
  ∀ address, KcovBufferBytes layout address → ¬protectedBytes address

/-- Physical state carried between callbacks. Disabled tracing requires no
    mapped coverage area; the mode field itself still belongs to the task. -/
def KcovState (layout : KcovLayout) (preempt : BitVec 32) (memory : Mem 64) : Prop :=
  KcovMetadata layout memory ∧
  load32 memory preemptCountAddress = some preempt ∧
  (layout.mode = 2 ∨ layout.mode = 3 → KcovBuffer layout memory)

/-- Bytes that caller stores must preserve. Buffer storage is needed only
    in an active mode; metadata and preemption state are always physical. -/
def KcovStateBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  KcovMetadataBytes layout address ∨ InRange preemptCountAddress 4 address ∨
    ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout address)

/-- KCOV comparison record encoding: width in bits 1..2, constant bit 0. -/
def KcovRecordTag : KcovKind → BitVec 64
  | .pc => 0 | .cmp1 => 0 | .cmp4 => 4 | .cmp8 => 6
  | .constCmp4 => 5 | .constCmp1 => 1

/-- Callback argument width is fixed by the called entry point. -/
def KcovArgument (kind : KcovKind) (s : MachineState) (reg : Reg64) : BitVec 64 :=
  if kind = .constCmp1 ∨ kind = .cmp1 then (s.data.regs.get (.low reg .W8)).setWidth 64
  else if kind = .cmp8 then s.data.regs.get64 reg
  else (s.data.regs.get (.low reg .W32)).setWidth 64

/-- Physical KCOV callback specification, with the actual early-return read
    dependencies and machine-width arithmetic. It is not a proof checker. -/
def KcovPlan (kind : KcovKind) (s : MachineState) : Option (List WordWrite) := do
  let memory := s.data.dmem
  let preempt ← load32 memory preemptCountAddress
  let returnPC ← load64 memory s.data.regs.rsp.toBitVec
  let task ← load64 memory currentTaskAddress
  if preempt &&& 0xff0100 != 0 then
    if preempt &&& 0x100 == 0 || preempt &&& 0xff0000 != 0 then return []
    let softirqEnabled ← load32 memory (task + 0x704)
    if softirqEnabled == 0 then return []
  let mode ← load32 memory (task + 0x6e0)
  if mode != (if kind = .pc then 2 else 3) then return []
  let area ← load64 memory (task + 0x6e8)
  let capacity ← load32 memory (task + 0x6e4)
  let count ← load64 memory area
  if kind = .pc then
    let next := count + 1
    if next.toNat ≥ capacity.toNat then return []
    return [⟨area, next⟩, ⟨area + 8 * next, returnPC⟩]
  else
    let slot := 4 * count
    let ending := 8 * slot + 40
    if 8 * (capacity.setWidth 64) < ending then return []
    let tag := KcovRecordTag kind
    let arg1 := KcovArgument kind s .rdi
    let arg2 := KcovArgument kind s .rsi
    return [⟨area, count + 1⟩, ⟨area + ending - 32, tag⟩,
      ⟨area + ending - 24, arg1⟩, ⟨area + ending - 16, arg2⟩,
      ⟨area + ending - 8, returnPC⟩]

/-- Planned destinations are mapped and do not overwrite the return word.
    Separation from all represented objects is an additional entry obligation. -/
def KcovReady (kind : KcovKind) (s : MachineState) : Prop :=
  ∃ stores, KcovPlan kind s = some stores ∧
    ∀ write ∈ stores,
      (s.data.dmem.loadInt write.address 8).isSome = true ∧
      ∀ address, InRange write.address 8 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

def KcovWrites (kind : KcovKind) (s : MachineState) (address : BitVec 64) : Prop :=
  ∃ stores, KcovPlan kind s = some stores ∧
    ∃ write ∈ stores, InRange write.address 8 address

/-- Exact callback stores keep repeated-call buffer readiness provable;
    allowing arbitrary corruption of the coverage buffer would not suffice. -/
def KcovEffect (kind : KcovKind) (before after : MachineState) : Prop :=
  ∃ stores, KcovPlan kind before = some stores ∧
    after.data.dmem = stores.foldl
      (fun memory write => memory.storeInt write.address 8 write.value.toInt) before.data.dmem

/-- KCOV PC callback: only its physically planned stores may occur. -/
def TracePcContract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)

/-- KCOV variable/variable 32-bit comparison callback. -/
def TraceCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4)

/-- KCOV constant/variable 32-bit comparison callback. -/
def TraceConstCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4)
    (KcovWrites .constCmp4) (KcovEffect .constCmp4)

/-- KCOV constant/variable 8-bit comparison callback used by peer-get. -/
def TraceConstCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1)
    (KcovWrites .constCmp1) (KcovEffect .constCmp1)

/-- The actual no-work BH-enable path, including nested disable counts.
    The softirq word is needed only on the branch that reads it. -/
def BhEnableReady (s : MachineState) : Prop :=
  ∃ count : BitVec 32,
    s.data.dmem.loadInt preemptCountAddress 4 = some (count.toNat : Int) ∧
    count &&& 0x000f0000 = 0 ∧
    ((count + 1 - s.data.regs.get (.low .rsi .W32)) &&& 0x00ffff00 = 0 →
      s.data.dmem.loadInt softirqPendingAddress 2 = some 0) ∧
    ∀ address, InRange preemptCountAddress 4 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

/-- BH enable balances the actual low-32-bit count argument, modulo 2^32.
    Readiness must justify that its softirq path runs no pending work. -/
def BhEnableContract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810732c0) BhEnableReady
    (fun _ => InRange preemptCountAddress 4)
    (fun before after => ∀ old : BitVec 32,
      before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) →
      after.data.dmem.loadInt preemptCountAddress 4 =
        some ((old - before.data.regs.get (.low .rsi .W32)).toNat : Int))

/-- Additional anchored decoder domain for M2; M1 agreement is separate
    because peer-get is shared. The linked-label interpretation is unchanged. -/
def AllowedipsDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, AllowedipsImage.fetch pc = some instruction → fetch pc = some instruction

/-- A callback's interior is not another anchored M2 invocation. -/
def NoAllowedipsReentry (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, AllowedipsImage.fetch s.pc = none

/-- M2 uses the same physical callback specification, with its additional
    anchored ranges excluded from callback interiors. The original M1
    contracts and their hypotheses remain unchanged. -/
def AllowedipsServiceReturns (fetch : Int64 → Option Decoded) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop) : Prop :=
  ∀ s returnAddress, s.pc = address → ready s → EntryFrame s returnAddress →
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧
        effect s t.machine ∧ NoAnchoredReentry t.history ∧ NoAllowedipsReentry t.history)
      ⟨s, [s]⟩

def AllowedipsTracePcContract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3100)
    (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)

def AllowedipsTraceCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3e40)
    (KcovReady .cmp1) (KcovWrites .cmp1) (KcovEffect .cmp1)

def AllowedipsTraceCmp8Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3ea0)
    (KcovReady .cmp8) (KcovWrites .cmp8) (KcovEffect .cmp8)

def AllowedipsTraceConstCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3ec0)
    (KcovReady .constCmp1) (KcovWrites .constCmp1) (KcovEffect .constCmp1)

def AllowedipsTraceConstCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3f00)
    (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4)

/-- As in M1, this contract covers the no-pending-work BH-enable path.
    M2's Pre must justify the actual read conditions and stack separation. -/
def AllowedipsBhEnableContract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810732c0) BhEnableReady
    (fun _ => InRange preemptCountAddress 4)
    (fun before after => ∀ old : BitVec 32,
      before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) →
      after.data.dmem.loadInt preemptCountAddress 4 =
        some ((old - before.data.regs.get (.low .rsi .W32)).toNat : Int))

/-- Whether the actual callback reads softirqEnabled before its mode test. -/
def LookupSoftRead (preempt : BitVec 32) : Prop :=
  preempt &&& 0xff0100 ≠ 0 ∧
  ¬(preempt &&& 0x100 = 0 ∨ preempt &&& 0xff0000 ≠ 0)

/-- The callback reaches its mode read only after the preemption/softirq gate. -/
def LookupModeRead (coverage : KcovLayout) (preempt : BitVec 32) : Prop :=
  if preempt &&& 0xff0100 ≠ 0 then
    ¬(preempt &&& 0x100 = 0 ∨ preempt &&& 0xff0000 ≠ 0) ∧ coverage.softirqEnabled ≠ 0
  else True

/-- PC callbacks occur before and after BH-disable. Comparisons occur only
    with a nonempty selected bucket, after the actual modular increment. -/
def LookupBufferNeeded (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) : Prop :=
  (coverage.mode = 2 ∧ (LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt))) ∨
  (coverage.mode = 3 ∧ v.bucket ≠ [] ∧ LookupModeRead coverage (512+preempt))

/-- Only callback metadata reached in one of this lookup's two contexts.
    Unused layout values impose no equality on memory. The active coverage
    allocation is mapped uniformly; a full buffer is permitted. -/
def LookupCoverageAt (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some coverage.task ∧
  ((LookupSoftRead preempt ∨ LookupSoftRead (512+preempt)) →
    load32 memory (coverage.task+0x704) = some coverage.softirqEnabled) ∧
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt)) →
    load32 memory (coverage.task+0x6e0) = some coverage.mode) ∧
  (LookupBufferNeeded coverage preempt v →
    load32 memory (coverage.task+0x6e4) = some coverage.capacity ∧
    load64 memory (coverage.task+0x6e8) = some coverage.area ∧ KcovBuffer coverage memory)

def LookupMetadataBytes (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨
  ((LookupSoftRead preempt ∨ LookupSoftRead (512+preempt)) ∧ InRange (coverage.task+0x704) 4 a) ∨
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt)) ∧ InRange (coverage.task+0x6e0) 4 a) ∨
  (LookupBufferNeeded coverage preempt v ∧
    (InRange (coverage.task+0x6e4) 4 a ∨ InRange (coverage.task+0x6e8) 8 a))

def LookupCoverageWrites (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupBufferNeeded coverage preempt v ∧ KcovBufferBytes coverage a

def LookupServiceBytes (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupMetadataBytes coverage preempt v a ∨ InRange preemptCountAddress 4 a ∨
  (LookupBufferNeeded coverage preempt v ∧ KcovStorageBytes coverage a)

/-- The helper is called for a selected owner even when its peer word is NULL. -/
def LookupStackWords (c : LookupRelation.Config) : Nat := if c.focus.owner.isSome then 13 else 6

def LookupStackWrites (c : LookupRelation.Config) (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c)

def LookupLiveStack (c : LookupRelation.Config) (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c+8)

def LookupBucketBytes (c : LookupRelation.Config) (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  InRange (c.table + .ofNat 64 (8*(c.query%8192))) 8 a ∨
  ∃ e ∈ v.bucket, BucketShapeReads (LookupRelation.ownerAddress c e.owner) a

def LookupOwnerBytes (c : LookupRelation.Config) (a : BitVec 64) : Prop :=
  ∃ owner, c.focus.owner = some owner ∧ InRange (LookupRelation.ownerAddress c owner) 8 a

def LookupCountBytes (c : LookupRelation.Config) (a : BitVec 64) : Prop :=
  ∃ pid, c.focus.peer = some pid ∧ InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a

def LookupDataWrites (c : LookupRelation.Config) (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupOwnerBytes c a ∨ ((∃ n, v.count = some n ∧ n ≠ 0) ∧ LookupCountBytes c a)

/-- A conditional output requirement, not a count bound on the entry domain.
    Dead, NULL, miss and rejected-saturation inputs need no output storage. -/
def LookupOutputNeeded (v : LookupRelation.View) : Prop :=
  ∃ n, v.count = some n ∧ n ≠ 0 ∧ n+1 < 2^31

def LookupOutputWrites (v : LookupRelation.View) (s : MachineState) (a : BitVec 64) : Prop :=
  LookupOutputNeeded v ∧ InRange s.data.regs.rcx.toBitVec 8 a

def LookupPendingRead (preempt : BitVec 32) : Prop := (preempt+1) &&& 0x00ffff00 = 0

/-- Named physical entry obligations. Separation is an explicit allocation
    discipline, not a claim that every safe x86 alias is admitted. No live-
    peer or positive-count invariant is imposed. Every byte range belongs
    to lookup, its helper, its stack or its named service callbacks. -/
structure LookupEntry (c : LookupRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState)
    (world : Leanux.World) (v : LookupRelation.View) : Prop where
  pc : s.pc = Image.Lookup.entry
  frame : EntryFrame s returnAddress
  table : s.data.regs.rdi.toBitVec = c.table
  query : (s.data.regs.get (.low .rdx .W32)).toNat = c.query
  kinds : KindMask (s.data.regs.get (.low .rsi .W32)) c.kinds
  projected : LookupRelation.project c world = some v
  focus : LookupRelation.EntryFocus c v
  physical : LookupRelation.Physical c [s] [LookupObservation.call "wg_index_hashtable_lookup" s] s v
  steps : world.steps.toList = c.incomingSteps
  rxSection : world.netRxSection = c.rxSection
  coverageAt : LookupCoverageAt coverage preempt v s.data.dmem
  preemptAt : load32 s.data.dmem preemptCountAddress = some preempt
  stackMapped : ∀ n < LookupStackWords c,
    (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true
  outputMapped : LookupOutputNeeded v → (s.data.dmem.loadInt s.data.regs.rcx.toBitVec 8).isSome = true
  bhHardirq : (512+preempt) &&& 0x000f0000 = 0
  bhPending : LookupPendingRead preempt → s.data.dmem.loadInt softirqPendingAddress 2 = some 0
  readsScratch : ∀ a, LookupRelation.Reads c v a →
    ¬(LookupStackWrites c s a ∨ LookupCoverageWrites coverage preempt v a ∨ InRange preemptCountAddress 4 a)
  serviceStack : ∀ a, LookupServiceBytes coverage preempt v a → ¬LookupStackWrites c s a
  coverageStack : ∀ a, LookupCoverageWrites coverage preempt v a → ¬LookupLiveStack c s a
  coverageMetadata : ∀ a, LookupCoverageWrites coverage preempt v a → ¬LookupMetadataBytes coverage preempt v a
  coveragePreempt : ∀ a, LookupCoverageWrites coverage preempt v a → ¬InRange preemptCountAddress 4 a
  bhStack : ∀ a, InRange preemptCountAddress 4 a → ¬LookupLiveStack c s a
  bhMetadata : ∀ a,
    (LookupMetadataBytes coverage preempt v a ∨
      (LookupBufferNeeded coverage preempt v ∧ KcovStorageBytes coverage a)) →
    ¬InRange preemptCountAddress 4 a
  dataService : ∀ a, LookupServiceBytes coverage preempt v a → ¬LookupDataWrites c v a
  dataReturn : ∀ a, InRange s.data.regs.rsp.toBitVec 8 a → ¬LookupDataWrites c v a
  dataBucket : ∀ a, LookupBucketBytes c v a → ¬LookupDataWrites c v a
  ownerCount : ∀ a, LookupCountBytes c a → ¬LookupOwnerBytes c a
  outputProtected : ∀ a, LookupOutputWrites v s a →
    ¬(LookupRelation.Reads c v a ∨ LookupServiceBytes coverage preempt v a ∨
      InRange (s.data.regs.rsp.toBitVec-48) 56 a ∨ LookupCoverageWrites coverage preempt v a)
  pendingFrame : LookupPendingRead preempt → ∀ a, InRange softirqPendingAddress 2 a →
    ¬(LookupStackWrites c s a ∨ LookupCoverageWrites coverage preempt v a ∨
      LookupDataWrites c v a ∨ LookupOutputWrites v s a)

/-- Entry domain relative to the supplied source World and fixed ABI/address
    interpretation. Its machine-side domain existentially closes world and
    these interpretation parameters. No execution or R-preservation premise
    occurs here; LookupWitness supplies a concrete inhabitant and its test
    executes that exact state to the recorded return. -/
def Pre_lookup (c : LookupRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState) (world : Leanux.World) : Prop :=
  ∃ v, LookupEntry c coverage preempt returnAddress s world v


/-- M2 calls PC and comparison instrumentation in both BH phases. Buffer
    metadata is required only when the physical callback reads it. -/
def AllowedipsCoverageNeeded (coverage : KcovLayout) (preempt : BitVec 32) : Prop :=
  LookupModeRead coverage preempt ∧ (coverage.mode = 2 ∨ coverage.mode = 3)

def AllowedipsCoverageAt (coverage : KcovLayout) (preempt : BitVec 32) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some coverage.task ∧
  (LookupSoftRead preempt → load32 memory (coverage.task+0x704) = some coverage.softirqEnabled) ∧
  (LookupModeRead coverage preempt → load32 memory (coverage.task+0x6e0) = some coverage.mode) ∧
  (AllowedipsCoverageNeeded coverage preempt →
    load32 memory (coverage.task+0x6e4) = some coverage.capacity ∧
    load64 memory (coverage.task+0x6e8) = some coverage.area ∧ KcovBuffer coverage memory)

def AllowedipsCoverageWrites (coverage : KcovLayout) (preempt : BitVec 32)
    (a : BitVec 64) : Prop :=
  (AllowedipsCoverageNeeded coverage preempt ∨ AllowedipsCoverageNeeded coverage (preempt+512)) ∧
    KcovBufferBytes coverage a

def AllowedipsMetadata (coverage : KcovLayout) (preempt : BitVec 32) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨
  ((LookupSoftRead preempt ∨ LookupSoftRead (preempt+512)) ∧ InRange (coverage.task+0x704) 4 a) ∨
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (preempt+512)) ∧ InRange (coverage.task+0x6e0) 4 a) ∨
  ((AllowedipsCoverageNeeded coverage preempt ∨ AllowedipsCoverageNeeded coverage (preempt+512)) ∧
    (InRange (coverage.task+0x6e4) 4 a ∨ InRange (coverage.task+0x6e8) 8 a)) ∨
  (LookupPendingRead preempt ∧ InRange softirqPendingAddress 2 a)

def AllowedipsServiceBytes (coverage : KcovLayout) (preempt : BitVec 32) (a : BitVec 64) : Prop :=
  AllowedipsMetadata coverage preempt a ∨
  ((AllowedipsCoverageNeeded coverage preempt ∨ AllowedipsCoverageNeeded coverage (preempt+512)) ∧
    KcovStorageBytes coverage a)

/-- Outer saves/local words, the shared call slot, and the deepest peer-get
    saves/call: every word of this interval is used on a covered path. -/
def AllowedipsStackWrites (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec-144) 144

def AllowedipsLiveStack (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec-144) 152

def AllowedipsCountWrites (c : AllowedipsRelation.Config) (v : AllowedipsRelation.View)
    (a : BitVec 64) : Prop :=
  ∃ pid count, c.focus.peer = some pid ∧ v.count = some count ∧ count ≠ 0 ∧
    InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a

/-- Physical entry domain for both IP families. Focus is a total pure source
    selection, not an assumption that the binary or mirror terminates; a
    refused source search gives no selected node. No peer positivity premise.
    Both address families have executed concrete witnesses in AllowedipsWitnessPre. -/
structure AllowedipsEntry (c : AllowedipsRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState)
    (world : Leanux.World) (v : AllowedipsRelation.View) : Prop where
  pc : s.pc = AllowedipsImage.Lookup.entry
  entry : EntryFrame s returnAddress
  root : s.data.regs.rdi.toBitVec = AllowedipsRelation.pointer c.nodes c.root
  bits : s.data.regs.get (.low .rsi .W8) = .ofNat 8 c.bits
  projection : AllowedipsRelation.project c world = some v
  related : AllowedipsRelation.R c [s] [LookupObservation.call "lookup" s] s world
  focusNode : c.focus.node = (AllowedipsSource.select v.nodes c.root c.bits c.key).join
  focusPeer : c.focus.peer = c.focus.node.bind (fun id => (v.nodes id).bind (·.peer))
  input : Allowedips.NetworkKey s.data.dmem s.data.regs.rdx.toBitVec c.bits c.key
  stack : ∀ i < 18,
    (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec-.ofNat 64 ((i+1)*8)) 8).isSome = true
  preemptField : load32 s.data.dmem preemptCountAddress = some preempt
  coverageBefore : AllowedipsCoverageAt coverage preempt s.data.dmem
  coverageDuring : AllowedipsCoverageAt coverage (preempt+512) s.data.dmem
  hardirq : (preempt+512) &&& 0x000f0000 = 0
  pending : LookupPendingRead preempt → s.data.dmem.loadInt softirqPendingAddress 2 = some 0
  stackData : ∀ a, AllowedipsRelation.Reads c v a → ¬AllowedipsStackWrites s a
  stackInput : ∀ a, Allowedips.NetworkReads s.data.regs.rdx.toBitVec c.bits a → ¬AllowedipsStackWrites s a
  stackServices : ∀ a, (AllowedipsServiceBytes coverage preempt a ∨ InRange preemptCountAddress 4 a) →
    ¬AllowedipsStackWrites s a
  bufferData : ∀ a, AllowedipsRelation.Reads c v a → ¬AllowedipsCoverageWrites coverage preempt a
  bufferInput : ∀ a, Allowedips.NetworkReads s.data.regs.rdx.toBitVec c.bits a →
    ¬(AllowedipsCoverageNeeded coverage preempt ∧ KcovBufferBytes coverage a)
  bufferStack : ∀ a, AllowedipsCoverageWrites coverage preempt a → ¬AllowedipsLiveStack s a
  bufferMetadata : ∀ a, AllowedipsCoverageWrites coverage preempt a →
    ¬AllowedipsMetadata coverage preempt a
  bufferPreempt : ∀ a, AllowedipsCoverageWrites coverage preempt a → ¬InRange preemptCountAddress 4 a
  countStack : ∀ a, AllowedipsCountWrites c v a → ¬AllowedipsLiveStack s a
  countTrie : ∀ a, AllowedipsCountWrites c v a →
    ¬AllowedipsRelation.TrieReads c.nodes v.nodes c.root c.bits c.key a
  countServices : ∀ a, AllowedipsCountWrites c v a →
    ¬(AllowedipsServiceBytes coverage preempt a ∨ InRange preemptCountAddress 4 a)
  preemptData : ∀ a, AllowedipsRelation.Reads c v a → ¬InRange preemptCountAddress 4 a
  preemptStack : ∀ a, AllowedipsLiveStack s a → ¬InRange preemptCountAddress 4 a
  preemptServices : ∀ a, AllowedipsServiceBytes coverage preempt a → ¬InRange preemptCountAddress 4 a

/-- The function's named machine-entry domain, witnessed before it lands. -/
def Pre_allowedips (c : AllowedipsRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState) (world : Leanux.World) : Prop :=
  ∃ v, AllowedipsEntry c coverage preempt returnAddress s world v

end Binary.TrustBase
