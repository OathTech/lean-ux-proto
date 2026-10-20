import TrustBase

namespace Binary
local instance : Labels := Image.linkedLabels

/-- Insert the actual local service run into the caller history. The service
    assumption is the named physical contract in TrustBase; no R assertion
    or expected mirror sequence is supplied by it. -/
theorem service_in_context (fetch : Int64 → Option Decoded) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop)
    (contract : TrustBase.ServiceReturns fetch address ready writes effect)
    (s : MachineState) (returnAddress : UInt64) (front : List MachineState)
    (atEntry : s.pc = address) (isReady : ready s)
    (frame : TrustBase.EntryFrame s returnAddress) :
    Eventually (historyStep fetch)
      (fun t => ∃ localHistory,
        t.history = front ++ localHistory ∧
        TrustBase.Returned s t.machine returnAddress ∧
        EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧
        effect s t.machine ∧ TrustBase.NoAnchoredReentry localHistory)
      ⟨s, front ++ [s]⟩ := by
  have run := history_prepend fetch _ _ (contract s returnAddress atEntry isReady frame) front
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨localState, returned, machine, history⟩
  exact ⟨localState.history, history, machine.symm ▸ returned⟩

/-- The physical frame contract entails exact preservation of every caller
    field whose bytes are outside the callee's permitted writes. -/
theorem service_preserves_word (before after : MachineState)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes before.data.dmem after.data.dmem)
    (address : BitVec 64) (width : Nat) (value : Int)
    (disjoint : ∀ i < width, ¬writes (address + .ofNat 64 i))
    (field : before.data.dmem.loadInt address width = some value) :
    after.data.dmem.loadInt address width = some value :=
  (frame.loadInt address width disjoint).symm.trans field

#print axioms service_in_context
#print axioms service_preserves_word
end Binary
