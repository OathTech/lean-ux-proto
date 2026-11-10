import CallbackCmp8Image
import CallbackLeafHistory

/-! The rules for the KCOV callbacks as conclusions of image execution, stated once.

Interface propositions only (`def … : Prop`), and what follows from them without
executing anything. Their proofs are work package 1 of result C2 (file prefix
`CallbackCmp8`, root `CallbackCmp8`); the C1 branch takes this module and
`CallbackCmp8Image` unchanged and uses `Cmp8Rule` through `cmp8_kcov` below. Each
8-byte rule asks for agreement on its own entry only: C1's image terms hold
`__sanitizer_cov_trace_cmp8` and not the constant form.

A rule here differs from the landed `Callback.LeafService` in one respect: the interior
of the call is confined to the callbacks' own text (`Interior`), not only kept out of
the lookup image. A caller needs that to show that no state inside a callback is at one
of its own cut or exit addresses. -/
namespace Binary.Callback.Cmp8
open TrustBase
local instance : Labels := Image.linkedLabels

/-- The stores of an 8-byte comparison callback whose entry passes `tag` to
`write_comp_data`: the comparison branch of `TrustBase.KcovPlan`, with both arguments at
full width. `recordPlan 6` is `KcovPlan .cmp8` (`recordPlan_cmp8`); `KcovKind` has no
constructor for the constant form, whose tag is 7. -/
def recordPlan (tag : BitVec 64) (s : MachineState) : Option (List WordWrite) := do
  let memory := s.data.dmem
  let preempt ← load32 memory preemptCountAddress
  let returnPC ← load64 memory s.data.regs.rsp.toBitVec
  let task ← load64 memory currentTaskAddress
  if preempt &&& 0xff0100 != 0 then
    if preempt &&& 0x100 == 0 || preempt &&& 0xff0000 != 0 then return []
    let softirqEnabled ← load32 memory (task + 0x704)
    if softirqEnabled == 0 then return []
  let mode ← load32 memory (task + 0x6e0)
  if mode != 3 then return []
  let area ← load64 memory (task + 0x6e8)
  let capacity ← load32 memory (task + 0x6e4)
  let count ← load64 memory area
  let slot := 4 * count
  let ending := 8 * slot + 40
  if 8 * (capacity.setWidth 64) < ending then return []
  return [⟨area, count + 1⟩, ⟨area + ending - 32, tag⟩,
    ⟨area + ending - 24, s.data.regs.get64 .rdi⟩, ⟨area + ending - 16, s.data.regs.get64 .rsi⟩,
    ⟨area + ending - 8, returnPC⟩]

/-- `TrustBase.KcovReady`, for any plan. -/
def Ready (plan : MachineState → Option (List WordWrite)) (s : MachineState) : Prop :=
  ∃ stores, plan s = some stores ∧
    ∀ write ∈ stores,
      (s.data.dmem.loadInt write.address 8).isSome = true ∧
      ∀ address, InRange write.address 8 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

/-- `TrustBase.KcovWrites`, for any plan. -/
def Writes (plan : MachineState → Option (List WordWrite)) (s : MachineState)
    (address : BitVec 64) : Prop :=
  ∃ stores, plan s = some stores ∧ ∃ write ∈ stores, InRange write.address 8 address

/-- `TrustBase.KcovEffect`, for any plan: exactly the planned stores, in order. -/
def Effect (plan : MachineState → Option (List WordWrite)) (before after : MachineState) : Prop :=
  ∃ stores, plan before = some stores ∧
    after.data.dmem = stores.foldl
      (fun memory write => memory.storeInt write.address 8 write.value.toInt) before.data.dmem

/-- A callback's text: the shared service bodies and the two 8-byte entries. -/
def Text (pc : Int64) : Prop :=
  (ServiceImage.fetch pc).isSome = true ∨ (Cmp8.fetch pc).isSome = true

/-- What holds of every state inside a callback: the stack pointer is the one at its
entry, and the instruction executed is the callbacks' own. -/
def Interior (rsp : UInt64) (q : MachineState) : Prop :=
  leafGuard rsp q ∧ Text q.pc

/-- A callback at `address` whose stores are `plan`: entered ready, with the return
address on the stack, it returns to its caller with the callee-saved registers kept,
having made exactly the planned stores, and every state before the return is inside the
callbacks' text. -/
def Leaf (fetch : Int64 → Option Decoded) (address : Int64)
    (plan : MachineState → Option (List WordWrite)) : Prop :=
  ∀ s ra, s.pc = address → Ready plan s → EntryFrame s ra →
    Eventually (historyStep fetch) (fun t =>
      Returned s t.machine ra ∧ EqualOutside (Writes plan s) s.data.dmem t.machine.data.dmem ∧
      Effect plan s t.machine ∧ ∀ q ∈ t.history.dropLast, Interior s.data.regs.rsp q) ⟨s, [s]⟩

/-! ## The interface propositions (work package 1 proves these) -/

/-- RULE, the PC callback `__sanitizer_cov_trace_pc`. The landed `Callback.pc_run` with
the interior confined to the callbacks' text. -/
def PcRule : Prop :=
  ∀ fetch, ServiceDecoderAgreement fetch →
    Leaf fetch (.ofNat 0xffffffff810f31f0) (KcovPlan .pc)

/-- RULE, `__sanitizer_cov_trace_cmp8`, from the image: its five instructions and the
landed proof of `write_comp_data` (`Callback.cmp_run`). -/
def Cmp8Rule : Prop :=
  ∀ fetch, ServiceDecoderAgreement fetch → Cmp8Agreement fetch →
    Leaf fetch cmp8Entry (recordPlan 6)

/-- RULE, `__sanitizer_cov_trace_const_cmp8`, from the image. -/
def ConstCmp8Rule : Prop :=
  ∀ fetch, ServiceDecoderAgreement fetch → ConstCmp8Agreement fetch →
    Leaf fetch constCmp8Entry (recordPlan 7)

/-! ## What follows without executing anything -/

theorem recordPlan_cmp8 (s : MachineState) : recordPlan 6 s = KcovPlan .cmp8 s := by
  simp [recordPlan, KcovPlan, KcovArgument, KcovRecordTag]

theorem ready_kcov (kind : KcovKind) (s : MachineState) :
    Ready (KcovPlan kind) s = KcovReady kind s := rfl

theorem writes_kcov (kind : KcovKind) (s : MachineState) :
    Writes (KcovPlan kind) s = KcovWrites kind s := rfl

theorem effect_kcov (kind : KcovKind) (s t : MachineState) :
    Effect (KcovPlan kind) s t = KcovEffect kind s t := rfl

/-- The 8-byte comparison rule in the vocabulary of `TrustBase` (what the landed
`Kcov` lemmas and the C1 contracts consume). -/
theorem cmp8_kcov (rule : Cmp8Rule) (fetch : Int64 → Option Decoded)
    (services : ServiceDecoderAgreement fetch) (stub : Cmp8Agreement fetch) :
    Leaf fetch cmp8Entry (KcovPlan .cmp8) := by
  have same : recordPlan 6 = KcovPlan .cmp8 := funext recordPlan_cmp8
  rw [← same]
  exact rule fetch services stub

/-- A rule gives the landed leaf-service form, forgetting the text confinement. -/
theorem Leaf.service {fetch address} {kind : KcovKind} (leaf : Leaf fetch address (KcovPlan kind)) :
    LeafService fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind) := by
  intro s ra pc ready frame
  apply eventually_weaken (historyStep fetch) _ _ _ _ (leaf s ra pc ready frame)
  rintro t ⟨returned, framed, effect, interior⟩
  exact ⟨returned, framed, effect, fun q member => (interior q member).1⟩

#print axioms cmp8_kcov
#print axioms Leaf.service
end Binary.Callback.Cmp8
