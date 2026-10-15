import History
import Image
import ServiceImage
import Memory

/-! Named trust surface for the pinned lookup proof, under construction.
    These are explicit hypotheses, not globally asserted facts. No declaration
    here assumes the lookup result, a region's R-preservation, or a mirror run.
    Pre_lookup will be added together with its concrete satisfying witness.
    The final milestone report must reproduce this file verbatim.

    External interpretation: binutils 2.42 supplied the literal AST and DWARF
    layouts from the ELF below. Lean checks execution of those terms, not the
    binutils decoder, DWARF producer, SHA computation or correspondence of
    Kraken's model with x86 hardware. The loader checks identity and branch
    encodings. Mutable runtime globals are NOT assumed equal to ELF initial
    bytes at a function entry; their current values belong in Pre_lookup.
-/
namespace Binary.TrustBase

def krakenCommit : String := "e033e3dac812a576881a329b2d4c174364f3d44c"
def kernelIdentity : String := "6b2018b9"
def elfSha256 : String := "16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774"
def decoderVersion : String := "GNU objdump (GNU Binutils for Ubuntu) 2.42"

local instance : Labels := Image.linkedLabels

/-- The partial linked decoder for both anchored functions and all reached
    service bodies. A rejected instruction remains a failing fetch; neither
    its semantics nor successful execution is assumed by this definition. -/
def pinnedFetch (pc : Int64) : Option Decoded :=
  (Image.fetch pc).orElse (fun _ => ServiceImage.fetch pc)

/-- The ambient instruction image is this fixed ELF-derived listing,
    including service bytes. This is the external bytes-to-AST assumption. -/
def WholeImageDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  fetch = pinnedFetch

/-- The ambient decoder agrees with the pinned literal instructions/lengths.
    Interpreting those literals as this ELF is the external decoding assumption. -/
def AnchoredDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, Image.fetch pc = some instruction → fetch pc = some instruction

/-- No alternatives/static-key text change in a certified anchored range. -/
def AnchoredTextStable (fetchAt : Nat → Int64 → Option Decoded) : Prop :=
  ∀ time pc instruction, Image.fetch pc = some instruction → fetchAt time pc = some instruction

/-- Read-only image bytes remain the linked bytes. `linked` is the loader's
    fixed ELF projection; it is not chosen independently at each proof point. -/
def ReadOnlyImage (linked : Mem 64) (readOnly : BitVec 64 → Prop) (memory : Mem 64) : Prop :=
  ∀ address, readOnly address → memory.get? address = linked.get? address

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
  | pc | cmp4 | constCmp4 | constCmp1
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
    let tag : BitVec 64 := match kind with
      | .pc => 0
      | .cmp4 => 4
      | .constCmp4 => 5
      | .constCmp1 => 1
    let arg1 := if kind = .constCmp1 then (s.data.regs.get (.low .rdi .W8)).setWidth 64
      else (s.data.regs.get (.low .rdi .W32)).setWidth 64
    let arg2 := if kind = .constCmp1 then (s.data.regs.get (.low .rsi .W8)).setWidth 64
      else (s.data.regs.get (.low .rsi .W32)).setWidth 64
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

end Binary.TrustBase
