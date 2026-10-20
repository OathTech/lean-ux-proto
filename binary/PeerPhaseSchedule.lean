import PeerPhaseExceptions

namespace Binary.PeerCountPhase
open PeerGet

private theorem take_prefixed {α : Type} {first last : List α}
    (prefixed : first.IsPrefix last) (n : Nat) (bound : n ≤ first.length) :
    last.take n = first.take n := by
  obtain ⟨tail, recorded⟩ := prefixed
  rw [← recorded]
  exact List.take_append_of_le_length bound

theorem StableExtension.at_prefix {before after : List MachineState}
    (stable : StableExtension before after) (seed : Option Pending) (n : Nat)
    (bound : before.length ≤ n) :
    scan seed (after.take n) = scan seed before := by
  obtain ⟨tail, recorded, phases⟩ := stable
  rw [recorded, List.take_append, List.take_of_length_le bound, phases]

theorem ReturningExtension.prefix {before after : List MachineState}
    (returned : ReturningExtension before after) : before.IsPrefix after := by
  obtain ⟨tail, _, recorded, _⟩ := returned
  exact ⟨tail, recorded.symm⟩

theorem ReturningExtension.at_prefix {before after : List MachineState}
    (returned : ReturningExtension before after) (seed : Option Pending) (n : Nat)
    (bound : before.length ≤ n) :
    scan seed (after.take n) = if n < after.length then scan seed before else none := by
  obtain ⟨tail, _, recorded, phases⟩ := returned
  rw [recorded, List.take_append, List.take_of_length_le bound, phases]
  have same : n-before.length < tail.length ↔ n < (before++tail).length := by simp; omega
  simp only [same]

theorem scan_increment_appended (seed : Option Pending) (history : List MachineState)
    (body : MachineData) (af : Bool) (n : Nat)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x44⟩) :
    scan seed (history ++ (incrementStates body af).take n) =
      if n ≤ 2 then scan seed history else
        some ⟨body.regs.r13.toBitVec, body.regs.get (.low .rbp .W32)⟩ := by
  rw [scan_append _ _ _ _ last]
  have phase := scan_increment_prefix (scan seed history) body af (n+1)
  simpa only [List.take_succ_cons, show n+1 ≤ 3 ↔ n ≤ 2 by omega] using phase

/-- The exact scanner value at every raw prefix of a live helper. The
    two pre-CMPXCHG successors remain in the old phase; the final RET
    successor clears it. No correspondence-point assumption is used here. -/
theorem IncrementingReturnAt.schedule_seed {before history after : List MachineState} {address old}
    (run : IncrementingReturnAt before history after address old) (seed : Option Pending) :
    before.length ≤ history.length ∧ history.length+7 < after.length ∧
      ∀ n, before.length ≤ n →
        scan seed (after.take n) =
          if after.length ≤ n then none else
            if n ≤ history.length+2 then scan seed before else some ⟨address, old⟩ := by
  obtain ⟨body, af, stable, last, addr, count, returned⟩ := run
  have oldPhase : scan seed history = scan seed before := stable.final seed
  have grows : (history ++ incrementStates body af).length < after.length := by
    obtain ⟨tail, nonempty, recorded, _⟩ := returned
    simp only [recorded, List.length_append]
    have positive := List.length_pos_iff.mpr nonempty
    omega
  have size : (incrementStates body af).length = 7 := rfl
  have bound : history.length+7 < after.length := by simpa only [List.length_append, size] using grows
  refine ⟨stable.prefix.length_le, bound, ?_⟩
  intro n initialBound
  by_cases late : (history ++ incrementStates body af).length ≤ n
  · have finalPhase : scan seed (history ++ incrementStates body af) = some ⟨address, old⟩ := by
      have h := scan_increment_appended seed history body af 7 last
      have all : (incrementStates body af).take 7 = incrementStates body af :=
        List.take_of_length_le (by rw [size]; exact Nat.le_refl _)
      simpa only [all, show ¬7 ≤ 2 by decide,
        ite_false, addr, count] using h
    rw [returned.at_prefix seed n late, finalPhase]
    have beyond : ¬n ≤ history.length+2 := by
      simp only [List.length_append, size] at late
      omega
    simp only [beyond, ite_false]
    by_cases endReached : after.length ≤ n
    · simp only [endReached, show ¬n < after.length by omega, ite_true, ite_false]
    · simp only [endReached, show n < after.length by omega, ite_true, ite_false]
  · have early : n ≤ (history ++ incrementStates body af).length := by omega
    have notEnded : ¬after.length ≤ n := by omega
    rw [ite_eq_right notEnded, take_prefixed returned.prefix n early]
    by_cases prior : n ≤ history.length
    · rw [List.take_append_of_le_length prior, stable.at_prefix seed n initialBound]
      simp only [show n ≤ history.length+2 by omega, ite_true]
    · have afterBoundary : history.length ≤ n := by omega
      rw [List.take_append, List.take_of_length_le afterBoundary,
        scan_increment_appended seed history body af (n-history.length) last, oldPhase, addr, count]
      have same : n-history.length ≤ 2 ↔ n ≤ history.length+2 := by omega
      simp only [same]

theorem IncrementingReturnAt.schedule {before history after : List MachineState} {address old}
    (run : IncrementingReturnAt before history after address old) (initial : scan none before = none) :
    before.length ≤ history.length ∧ history.length+7 < after.length ∧
      ∀ n, before.length ≤ n →
        scan none (after.take n) =
          if after.length ≤ n then none else
            if n ≤ history.length+2 then none else some ⟨address, old⟩ := by
  simpa only [initial] using run.schedule_seed none

theorem IncrementingReturn.schedule {before after : List MachineState} {address old}
    (run : IncrementingReturn before after address old) (initial : scan none before = none) :
    ∃ boundary : Nat, before.length ≤ boundary ∧ boundary+7 < after.length ∧
      ∀ n, before.length ≤ n →
        scan none (after.take n) =
          if after.length ≤ n then none else
            if n ≤ boundary+2 then none else some ⟨address, old⟩ := by
  obtain ⟨body, history, af, stable, last, addr, count, returned⟩ := run
  exact ⟨history.length, (show IncrementingReturnAt before history after address old from
    ⟨body, af, stable, last, addr, count, returned⟩).schedule initial⟩

/-- The two successors before the physical count store are not cuts.
    This fact connects the raw phase schedule to the old/new cut frames. -/
theorem IncrementingReturnAt.cut_boundary {before boundary after : List MachineState}
    {address old} (run : IncrementingReturnAt before boundary after address old)
    (i : Nat) (current : MachineState) (present : after[i]? = some current)
    (cut : current.pc ∈ Image.cutPoints) :
    i < boundary.length ∨ boundary.length+2 ≤ i := by
  by_cases early : i < boundary.length
  · exact .inl early
  right
  by_cases late : boundary.length+2 ≤ i
  · exact late
  exfalso
  have casesIndex : i = boundary.length ∨ i = boundary.length+1 := by omega
  obtain ⟨body, af, _, _, _, _, returned⟩ := run
  obtain ⟨tail, _, recorded, _⟩ := returned
  rw [recorded, List.getElem?_append_left (by simp [incrementStates]; omega),
    List.getElem?_append_right (by omega)] at present
  rcases casesIndex with rfl | rfl
  · simp only [Nat.sub_self, incrementStates, List.getElem?_cons_zero, Option.some.injEq] at present
    subst current
    exact (by decide : Image.PeerGet.entry+0x48 ∉ Image.cutPoints) cut
  · simp only [Nat.add_sub_cancel_left, incrementStates, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at present
    subst current
    exact (by decide : Image.PeerGet.entry+0x4a ∉ Image.cutPoints) cut

/-- A nonempty seed survives every proper prefix of the helper, provided
    the actual incoming history also preserves it. -/
theorem IncrementingReturnAt.nonempty_before_return
    {first boundary final : List MachineState} {address old}
    (phase : IncrementingReturnAt first boundary final address old)
    (seed : Pending) (incoming : ∀ n, scan (some seed) (first.take n) ≠ none)
    (n : Nat) (proper : n < final.length) : scan (some seed) (final.take n) ≠ none := by
  have schedule := phase.schedule_seed (some seed)
  obtain ⟨body, af, stable, last, addr, count, returned⟩ := phase
  have prefixed : first.IsPrefix final := stable.prefix.trans
    ((List.prefix_append boundary (incrementStates body af)).trans returned.prefix)
  by_cases early : n ≤ first.length
  · rw [take_prefixed prefixed n early]
    exact incoming n
  · rw [schedule.2.2 n (by omega)]
    simp only [show ¬final.length ≤ n by omega, ite_false]
    split
    · simpa only [List.take_length] using incoming first.length
    · simp

/-- Neutral prefixes, including the lookup's bucket loop and the CALL,
    retain a nonempty test seed at every raw prefix. -/
theorem StableExtension.nonempty_prefixes {first final : List MachineState}
    (stable : StableExtension first final) (seed : Pending)
    (incoming : ∀ n, scan (some seed) (first.take n) ≠ none) :
    ∀ n, scan (some seed) (final.take n) ≠ none := by
  intro n
  by_cases early : n ≤ first.length
  · rw [take_prefixed stable.prefix n early]
    exact incoming n
  · rw [stable.at_prefix (some seed) n (by omega)]
    simpa only [List.take_length] using incoming first.length

theorem IncrementingReturnAt.final {first boundary final : List MachineState} {address old}
    (phase : IncrementingReturnAt first boundary final address old) (seed : Option Pending) :
    scan seed final = none := by
  obtain ⟨_, _, _, _, _, _, returned⟩ := phase
  exact returned.final seed

theorem ReturningExtension.nonempty_before_return {first final : List MachineState}
    (phase : ReturningExtension first final) (seed : Pending)
    (incoming : ∀ n, scan (some seed) (first.take n) ≠ none)
    (n : Nat) (proper : n < final.length) : scan (some seed) (final.take n) ≠ none := by
  by_cases early : n ≤ first.length
  · rw [take_prefixed phase.prefix n early]
    exact incoming n
  · rw [phase.at_prefix (some seed) n (by omega), ite_eq_left proper]
    simpa only [List.take_length] using incoming first.length

#print axioms IncrementingReturnAt.final
#print axioms ReturningExtension.nonempty_before_return
#print axioms IncrementingReturnAt.nonempty_before_return
#print axioms StableExtension.nonempty_prefixes
#print axioms IncrementingReturnAt.cut_boundary
#print axioms IncrementingReturnAt.schedule_seed
#print axioms IncrementingReturnAt.schedule
#print axioms StableExtension.at_prefix
#print axioms ReturningExtension.at_prefix
#print axioms scan_increment_appended
#print axioms IncrementingReturn.schedule
end Binary.PeerCountPhase
