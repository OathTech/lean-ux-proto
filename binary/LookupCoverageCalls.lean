import LookupCoverage
import ServiceComposition

namespace Binary.LookupCoverage
open TrustBase
local instance : Labels := Image.linkedLabels

def Context.metadataBytes (c : Context) :=
  LookupMetadataBytes c.coverage c.entryPreempt c.entryView

def Context.Separated (c : Context) (protectedBytes : BitVec 64 → Prop) : Prop :=
  ∀ a, c.writes a → ¬protectedBytes a

def Context.CompareAllowed (c : Context) (current : BitVec 32) : Prop :=
  current = 512+c.entryPreempt ∧ c.entryView.bucket ≠ []

/-- Physical call invariant. Comparison eligibility is deliberately absent:
    an empty bucket needs PC callbacks but has no comparison calls. -/
structure CallsReady (c : Context) (current : BitVec 32) (s : MachineData) : Prop where
  state : c.At current s.dmem
  phase : current = c.entryPreempt ∨ current = 512+c.entryPreempt
  aligned : s.regs.rsp.toNat % 8 = 0
  mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true
  pushSeparate : ∀ a, c.bytes a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a
  returnSeparate : c.Separated (InRange (s.regs.rsp.toBitVec-8) 8)
  metadataSeparate : c.Separated c.metadataBytes
  preemptSeparate : c.Separated (InRange preemptCountAddress 4)

theorem CallsReady.congr {c : Context} {current : BitVec 32}
    {before after : MachineData} (ready : CallsReady c current before)
    (memory : after.dmem = before.dmem) (stack : after.regs.rsp = before.regs.rsp) :
    CallsReady c current after := by
  exact {
    state := by simpa only [memory] using ready.state
    phase := ready.phase
    aligned := by simpa only [stack] using ready.aligned
    mapped := by simpa only [memory, stack] using ready.mapped
    pushSeparate := by simpa only [stack] using ready.pushSeparate
    returnSeparate := by simpa only [stack] using ready.returnSeparate
    metadataSeparate := ready.metadataSeparate
    preemptSeparate := ready.preemptSeparate }

theorem CallsReady.pc_allowed {c current s} (ready : CallsReady c current s) :
    c.Allowed current .pc := .inl ⟨rfl, ready.phase⟩

theorem compare_allowed {c current kind} (comparison : Context.CompareAllowed c current)
    (different : kind ≠ .pc) : c.Allowed current kind :=
  .inr ⟨different, comparison⟩

/-- The existing named service contract, instantiated using conditional
    physical readiness. No new service or R-preservation assumption. -/
theorem callback (fetch : Int64 → Option Decoded) (address : Int64) (kind : KcovKind)
    (contract : ServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (c : Context) (current : BitVec 32) (s : MachineState) (returnAddress : UInt64)
    (atEntry : s.pc = address) (entry : EntryFrame s returnAddress)
    (state : c.At current s.data.dmem) (allowed : c.Allowed current kind)
    (stack : c.Separated (InRange s.data.regs.rsp.toBitVec 8))
    (metadata : c.Separated c.metadataBytes)
    (preemptFrame : c.Separated (InRange preemptCountAddress 4)) :
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        c.At current t.machine.data.dmem ∧
        EqualOutside c.writes s.data.dmem t.machine.data.dmem ∧
        NoAnchoredReentry t.history) ⟨s, [s]⟩ := by
  have returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnAddress.toBitVec := by
    simp only [load64, entry.2, Option.map_some, BitVec.ofInt_natCast]
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    simp
  have run := contract s returnAddress atEntry
    (ready c kind current s returnAddress.toBitVec state allowed returnRead stack) entry
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨returned, frame, effect, noReentry⟩
  have preserved := state_preserved c kind current s t.machine returnAddress.toBitVec
    state allowed returnRead metadata preemptFrame effect frame
  exact ⟨returned, preserved.1, preserved.2, noReentry⟩

#print axioms CallsReady.congr
#print axioms CallsReady.pc_allowed
#print axioms compare_allowed
#print axioms callback
end Binary.LookupCoverage
