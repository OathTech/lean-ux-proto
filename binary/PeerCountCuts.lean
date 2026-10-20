import PeerPhaseSchedule

namespace Binary.PeerCountPhase
open PeerGet

/-- Every appended correspondence cut of a live helper represents the
    old source count until its final RET, then the committed successor.
    The frame split and phase split share the very same raw prefix. -/
theorem IncrementingReturnAt.count_cuts
    (first middle tail : List MachineState) (address : Address) (old : BitVec 32)
    (phase : IncrementingReturnAt first (first ++ middle) (first ++ middle ++ tail) address old)
    (initial : scan none first = none) (memory : Mem 64) (writes : Address → Prop)
    (field : memory.loadInt address 4 = some (old.toNat : Int))
    (apart : ∀ j < 4, ¬writes (address + .ofNat 64 j))
    (bound : old.toNat+1 < 2^32)
    (oldFrames : ∀ q ∈ middle, q.pc ∈ Image.cutPoints → EqualOutside writes memory q.data.dmem)
    (newFrames : ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
      EqualOutside writes (memory.storeInt address 4 (old+1).toInt) q.data.dmem)
    (i : Nat) (current : MachineState)
    (present : (first ++ middle ++ tail)[i]? = some current)
    (later : first.length ≤ i) (cut : current.pc ∈ Image.cutPoints) :
    At (scan none ((first ++ middle ++ tail).take (i+1))) current.data.dmem address
      (if (first ++ middle ++ tail).length ≤ i+1 then old.toNat+1 else old.toNat) := by
  obtain ⟨_, grows, schedule⟩ := phase.schedule initial
  rw [schedule (i+1) (by omega)]
  rcases phase.cut_boundary i current present cut with earlier | updated
  · have notEnded : ¬(first ++ middle ++ tail).length ≤ i+1 := by omega
    have beforeStore : i+1 ≤ (first ++ middle).length+2 := by omega
    simp only [notEnded, beforeStore, ite_false, ite_true, At]
    have found : middle[i-first.length]? = some current := by
      simpa only [List.getElem?_append_left earlier, List.getElem?_append_right later] using present
    exact ((oldFrames current (List.mem_of_getElem? found) cut).loadInt address 4 apart).symm.trans field
  · have boundaryLe : (first ++ middle).length ≤ i := by omega
    have found : tail[i-(first ++ middle).length]? = some current := by
      simpa only [List.getElem?_append_right boundaryLe] using present
    have stored : current.data.dmem.loadInt address 4 = some ((old+1).toNat : Int) :=
      ((newFrames current (List.mem_of_getElem? found) cut).loadInt address 4 apart).symm.trans
        (load32_store memory address (old+1))
    by_cases finished : (first ++ middle ++ tail).length ≤ i+1
    · simp only [finished, ite_true, At]
      rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl,
        Nat.mod_eq_of_lt bound] at stored
      exact stored
    · simp only [finished, show ¬i+1 ≤ (first ++ middle).length+2 by omega,
        ite_false, At, ite_true]
      exact ⟨True.intro, stored⟩

/-- NULL and zero-count paths never create a pending increment. -/
theorem ReturningExtension.count_cuts
    (first tail : List MachineState) (phase : ReturningExtension first (first ++ tail))
    (initial : scan none first = none) (memory : Mem 64) (writes : Address → Prop)
    (address : Address) (count : Nat) (field : At none memory address count)
    (apart : ∀ j < 4, ¬writes (address + .ofNat 64 j))
    (frames : ∀ q ∈ tail, q.pc ∈ Image.cutPoints → EqualOutside writes memory q.data.dmem)
    (i : Nat) (current : MachineState) (present : (first ++ tail)[i]? = some current)
    (later : first.length ≤ i) (cut : current.pc ∈ Image.cutPoints) :
    At (scan none ((first ++ tail).take (i+1))) current.data.dmem address count := by
  have noPhase : scan none ((first ++ tail).take (i+1)) = none := by
    rw [phase.at_prefix none (i+1) (by omega), initial]
    split <;> rfl
  rw [noPhase]
  have found : tail[i-first.length]? = some current := by
    simpa only [List.getElem?_append_right later] using present
  exact At.frame (frames current (List.mem_of_getElem? found) cut) apart field

#print axioms IncrementingReturnAt.count_cuts
#print axioms ReturningExtension.count_cuts
end Binary.PeerCountPhase
