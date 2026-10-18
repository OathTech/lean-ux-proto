import PairIndexCallMemory

namespace Binary.Pair.Index
open TrustBase CommonBitsCoverage

/-- A CALL overwrites its own scratch return word. Saved registers, caller
return word and service inputs survive by the checked physical geometry. -/
theorem MemoryReady.call_store {n o c initial ra words values disabled m}
    (facts : CallFacts n o c initial ra words)
    (ready : MemoryReady c initial ra words values disabled m)
    (size : words<2^60) (positive : 0<words) (value : BitVec 64) :
    MemoryReady c initial ra words values disabled
      (m.storeInt (Stack.slot initial.data.regs.rsp.toBitVec words) 8 value.toInt) := by
  have frame := storeInt_frame m (Stack.slot initial.data.regs.rsp.toBitVec words) 8 value.toInt
  have state := state_frame (phase c disabled) _ _ ⟨ready.covered _,ready.preempt⟩ _ frame (by
    intro a read written
    exact facts.geometry.serviceStack a (phase_bytes c disabled a read)
      (Stack.scratch _ words words positive (by omega) a written))
  apply ready.callback facts.geometry size positive state
  · rw [load64_store]
    rfl
  · intro a outside
    exact frame a (fun inside => outside (.inl inside))

#print axioms MemoryReady.call_store
end Binary.Pair.Index
