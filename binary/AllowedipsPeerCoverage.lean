import CommonBitsCoverage
import AllowedipsPeerObservation
namespace Binary.AllowedipsPeerCoverage
open TrustBase
local instance : Labels := Image.linkedLabels
abbrev Context := CommonBitsCoverage.Context
/-- The current argument is a compatibility index for the old physical
region lemmas; all actual reads use the fixed context's preempt word. -/
def Context.At (c : Context) (_current : BitVec 32) (memory : Mem 64) := CommonBitsCoverage.Context.At c memory
def Context.writes (c : Context) := CommonBitsCoverage.Context.writes c
def Context.bytes (c : Context) := CommonBitsCoverage.Context.bytes c
def Context.metadataBytes (c : Context) := CommonBitsCoverage.Context.metadataBytes c
def Context.Allowed (_c : Context) (_current : BitVec 32) (kind : KcovKind) : Prop :=
  (kind = .pc ∧ True) ∨ (kind ≠ .pc ∧ True)

theorem state_frame (c : Context) (current : BitVec 32) (before after : Mem 64)
    (state : Context.At c current before) (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes before after)
    (apart : ∀ a, Context.bytes c a → ¬writes a) : Context.At c current after :=
  CommonBitsCoverage.state_frame c before after state writes frame apart
def Context.Separated (c : Context) (protectedBytes : BitVec 64 → Prop) : Prop :=
  ∀ a, c.writes a → ¬protectedBytes a

def Context.CompareAllowed (_c : Context) (_current : BitVec 32) : Prop :=
  True

/-- Physical callback invariant. The fixed coverage context already carries
    eligibility; the phase field is an inert compatibility index. -/
structure CallsReady (c : Context) (current : BitVec 32) (s : MachineData) : Prop where
  state : Context.At c current s.dmem
  phase : True
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
    Context.Allowed c current .pc := .inl ⟨rfl, ready.phase⟩

theorem compare_allowed {c current kind} (comparison : Context.CompareAllowed c current)
    (different : kind ≠ .pc) : Context.Allowed c current kind :=
  .inr ⟨different, comparison⟩


theorem callback (fetch : Int64 → Option Decoded) (address : Int64) (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (c : Context) (current : BitVec 32) (s : MachineState) (returnAddress : UInt64)
    (atEntry : s.pc = address) (entry : EntryFrame s returnAddress)
    (state : Context.At c current s.data.dmem) (_allowed : Context.Allowed c current kind)
    (stack : Context.Separated c (InRange s.data.regs.rsp.toBitVec 8))
    (metadata : Context.Separated c (Context.metadataBytes c))
    (preemptFrame : Context.Separated c (InRange preemptCountAddress 4)) :
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        Context.At c current t.machine.data.dmem ∧
        EqualOutside (Context.writes c) s.data.dmem t.machine.data.dmem ∧
        NoAnchoredReentry t.history ∧ NoAllowedipsReentry t.history) ⟨s, [s]⟩ :=
  CommonBitsCoverage.callback fetch address kind contract c s returnAddress atEntry entry
    state stack metadata preemptFrame
end Binary.AllowedipsPeerCoverage
