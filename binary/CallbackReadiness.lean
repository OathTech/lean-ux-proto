import TrustBase

namespace Binary
open TrustBase

/-- Physical callback obligations with a context-specific memory invariant
and eligibility phase. The footprints are supplied by the existing context;
this representation adds no separation or eligibility premise. -/
structure CallbackReady (State : Mem 64 → Prop) (Phase : Prop)
    (bytes writes metadata : BitVec 64 → Prop) (s : MachineData) : Prop where
  state : State s.dmem
  phase : Phase
  aligned : s.regs.rsp.toNat % 8 = 0
  mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true
  pushSeparate : ∀ a, bytes a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a
  returnSeparate : ∀ a, writes a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a
  metadataSeparate : ∀ a, writes a → ¬metadata a
  preemptSeparate : ∀ a, writes a → ¬InRange preemptCountAddress 4 a

/-- Readiness at the next call follows from its restored stack, mapped slot
and the service's proved memory invariant. Address-only premises transport. -/
theorem CallbackReady.restore {State Phase bytes writes metadata before after}
    (ready : CallbackReady State Phase bytes writes metadata before)
    (state : State after.dmem) (stack : after.regs.rsp = before.regs.rsp)
    (mapped : (after.dmem.loadInt (after.regs.rsp.toBitVec-8) 8).isSome = true) :
    CallbackReady State Phase bytes writes metadata after := {
  state := state
  phase := ready.phase
  aligned := by simpa only [stack] using ready.aligned
  mapped := mapped
  pushSeparate := by simpa only [stack] using ready.pushSeparate
  returnSeparate := by simpa only [stack] using ready.returnSeparate
  metadataSeparate := ready.metadataSeparate
  preemptSeparate := ready.preemptSeparate }

theorem CallbackReady.congr {State Phase bytes writes metadata before after}
    (ready : CallbackReady State Phase bytes writes metadata before)
    (memory : after.dmem = before.dmem) (stack : after.regs.rsp = before.regs.rsp) :
    CallbackReady State Phase bytes writes metadata after :=
  ready.restore (by simpa only [memory] using ready.state) stack
    (by simpa only [memory, stack] using ready.mapped)

end Binary
