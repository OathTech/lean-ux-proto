import Leanux.Proofs.WG.Queues.RingGeometry

/-! Exact original one-step laws for the physical stale/live representation.
Production is guarded by physical occupancy. Consumption retires at the
original batch threshold or ring end; batch zero and oversized batches are
included. These pure laws do not yet compose the recorded scheduler. -/
namespace Leanux.Proofs.WG.Queues.Ring
open Leanux Leanux.WG
variable {α : Type} {stale live xs : List α} {x : α}

theorem produce_bounds (hb : Bounds n t stale live)
    (hfree : stale.length + live.length < n) (x : α) :
    Bounds n t stale (live ++ [x]) := by
  simp only [Bounds, List.length_append, List.length_singleton]
  exact ⟨hb.1, by omega⟩

theorem produce (hb : Bounds n t stale live)
    (hfree : stale.length + live.length < n) (x : α) :
    (ringOf n batch t stale live).produce x = ringOf n batch t stale (live ++ [x]) := by
  have ht : t < n := by have := hb.1; omega
  have hp := loc_lt ht (Nat.le_of_lt hfree)
  have hnext : (if loc n t (stale.length + live.length) + 1 ≥ n then 0
      else loc n t (stale.length + live.length) + 1) =
      loc n t (stale.length + (live.length + 1)) := by
    unfold loc; split <;> split <;> split <;> omega
  simp only [ringOf, PtrRing.produce, List.length_append, List.length_singleton]
  congr 1
  apply Array.ext_getElem?
  intro j
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    Array.size_ofFn, Array.getElem?_ofFn]
  by_cases hj : j < n
  · have ho := offset_lt ht hj
    have he : loc n t (stale.length + live.length) = j ↔
        offset n t j = stale.length + live.length := by
      constructor
      · intro h; rw [← h, offset_loc ht hfree]
      · intro h; rw [← h, loc_offset ht hj]
    by_cases heq : loc n t (stale.length + live.length) = j
    · have hoff := he.mp heq
      simp [heq, hj, ← List.append_assoc, hoff]
    · have hne := fun h => heq (he.mpr h)
      simp only [heq, ↓reduceIte, hj, ↓reduceDIte, ← List.append_assoc]
      congr 1
      symm
      rw [List.getElem?_append]
      split
      · rfl
      · rename_i h
        have hg : stale.length + live.length < offset n t j := by
          simp only [List.length_append] at h; omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  · simp [hj, show loc n t (stale.length + live.length) ≠ j by omega]

theorem tryProduce_eq (hb : Bounds n t stale live) (x : α) :
    tryProduce (ringOf n batch t stale live) x =
      if stale.length + live.length = n then (false, ringOf n batch t stale live)
      else (true, ringOf n batch t stale (live ++ [x])) := by
  unfold tryProduce
  rw [full hb]
  by_cases he : stale.length + live.length = n
  · simp [he]
  · simp [he, produce hb (by have := hb.2; omega) x]

/-- Clearing a finite list of physical indices has the expected pointwise
effect. Only the queried slot needs an in-bounds premise; set! already ignores
out-of-bounds writes. -/
theorem fold_clear (s : Array (Option α)) (is : List Nat) (hj : j < s.size) :
    ((is.foldl (fun a i => a.set! i none) s)[j]?).getD none =
      if j ∈ is then none else (s[j]?).getD none := by
  induction is generalizing s with
  | nil => simp
  | cons i is ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simpa using hj)]
    by_cases he : i = j
    · subst i
      simp [Array.set!_eq_setIfInBounds, hj]
    · simp [List.mem_cons, Array.set!_eq_setIfInBounds, he]
      by_cases hm : j ∈ is <;> simp [hm, Ne.symm he]

theorem clear_slot (s : Array (Option α)) (ht : t ≤ h) (hj : j < s.size) :
    ((PtrRing.discardOne.clear s h t)[j]?).getD none =
      if t ≤ j ∧ j ≤ h then none else (s[j]?).getD none := by
  unfold PtrRing.discardOne.clear
  have he : (List.range (h + 1 - t)).foldl (fun a i => a.set! (h - i) none) s =
      ((List.range (h + 1 - t)).map (fun i => h - i)).foldl (fun a i => a.set! i none) s := by
    rw [List.foldl_map]
  rw [he, fold_clear _ _ hj]
  have hm : j ∈ (List.range (h + 1 - t)).map (fun i => h - i) ↔ t ≤ j ∧ j ≤ h := by
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · rintro ⟨hl, hu⟩
      exact ⟨h - j, by omega, by omega⟩
  simp only [hm]

theorem clear_size (s : Array (Option α)) (h t : Nat) :
    (PtrRing.discardOne.clear s h t).size = s.size := by
  unfold PtrRing.discardOne.clear
  generalize List.range (h + 1 - t) = is
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp

theorem consume_empty (hb : Bounds n t stale ([] : List α)) :
    (ringOf n batch t stale []).consume = (none, ringOf n batch t stale []) := by
  simp [PtrRing.consume, peek hb]

theorem retain_bounds (hb : Bounds n t stale (x :: xs))
    (hend : t + (stale.length + 1) < n) :
    Bounds n t (stale ++ [x]) xs := by
  have hl := hb.2
  simp only [Bounds, List.length_append, List.length_singleton]
  simp only [List.length_cons] at hl
  exact ⟨hend, by omega⟩

theorem consume_retain (hb : Bounds n t stale (x :: xs))
    (hbatch : stale.length + 1 < batch) (hend : t + (stale.length + 1) < n) :
    (ringOf n batch t stale (x :: xs)).consume =
      (some x, ringOf n batch t (stale ++ [x]) xs) := by
  rw [PtrRing.consume, peek hb]
  simp only [List.head?_cons]
  simp [PtrRing.discardOne, ringOf, show ¬n ≤ t + (stale.length + 1) by omega,
    show ¬batch ≤ stale.length + 1 by omega,
    Nat.add_assoc, List.append_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The post-retirement tail is the advanced head, wrapping exactly at n. -/
theorem retire_bounds (hb : Bounds n t stale (x :: xs)) :
    Bounds n (loc n t (stale.length + 1)) [] xs := by
  have ht : t < n := by have := hb.1; omega
  have hl := hb.2
  simp only [List.length_cons] at hl
  have hp := loc_lt ht (show stale.length + 1 ≤ n by omega)
  simp only [Bounds, List.length_nil, Nat.add_zero, Nat.zero_add]
  exact ⟨hp, by omega⟩

theorem retire_lookup (hb : Bounds n t stale (x :: xs)) (hj : j < n) :
    (if t ≤ j ∧ j ≤ t + stale.length then none
      else (stale ++ x :: xs)[offset n t j]?) =
      xs[offset n (loc n t (stale.length + 1)) j]? := by
  have hs := hb.1
  have hl := hb.2
  simp only [List.length_cons] at hl
  by_cases hc : t ≤ j ∧ j ≤ t + stale.length
  · rw [if_pos hc]
    symm
    apply List.getElem?_eq_none
    unfold offset loc
    split <;> split <;> omega
  · rw [if_neg hc]
    have ho : stale.length + 1 ≤ offset n t j ∧
        offset n (loc n t (stale.length + 1)) j = offset n t j - (stale.length + 1) := by
      unfold offset loc
      split <;> split <;> split <;> omega
    have he : stale ++ x :: xs = (stale ++ [x]) ++ xs := by simp
    rw [he, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_singleton, ho.2]

theorem retire_slots (hb : Bounds n t stale (x :: xs)) :
    PtrRing.discardOne.clear (ringOf n batch t stale (x :: xs)).slots
      (t + stale.length) t =
      (ringOf n batch (loc n t (stale.length + 1)) [] xs).slots := by
  apply Array.ext_getElem?
  intro j
  have hsize : (PtrRing.discardOne.clear (ringOf n batch t stale (x :: xs)).slots
      (t + stale.length) t).size = n := by rw [clear_size]; simp [ringOf]
  by_cases hj : j < n
  · have hh := clear_slot (ringOf n batch t stale (x :: xs)).slots
      (show t ≤ t + stale.length by omega) (show j < (ringOf n batch t stale (x :: xs)).slots.size by simpa [ringOf] using hj)
    rw [slot hj, retire_lookup hb hj] at hh
    rw [Array.getElem?_eq_getElem (by omega)] at hh
    simp only [Option.getD_some] at hh
    rw [Array.getElem?_eq_getElem (by omega)]
    simp only [ringOf, Array.getElem?_ofFn, hj, ↓reduceDIte, List.nil_append]
    exact congrArg some hh
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by simpa [ringOf] using Nat.le_of_not_gt hj)]

theorem consume_retire (hb : Bounds n t stale (x :: xs))
    (hr : batch ≤ stale.length + 1 ∨ n ≤ t + (stale.length + 1)) :
    (ringOf n batch t stale (x :: xs)).consume =
      (some x, ringOf n batch (loc n t (stale.length + 1)) [] xs) := by
  have hs := hb.1
  have hl := hb.2
  simp only [List.length_cons] at hl
  have ht : t < n := by omega
  have hprod : loc n t (stale.length + (xs.length + 1)) =
      loc n (loc n t (stale.length + 1)) xs.length := by
    unfold loc
    split <;> split <;> split <;> omega
  have htail : (if n ≤ t + (stale.length + 1) then 0 else t + (stale.length + 1)) =
      loc n t (stale.length + 1) := by unfold loc; split <;> split <;> omega
  rw [PtrRing.consume, peek hb]
  simp only [List.head?_cons]
  have hslots := retire_slots (batch := batch) hb
  simp only [ringOf] at hslots
  simp only [PtrRing.discardOne, ringOf, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_sub_cancel_left,
    decide_eq_true_eq, Bool.or_eq_true, ge_iff_le, hr, ↓reduceIte,
    hslots, hprod]
  by_cases hend : n ≤ t + (stale.length + 1)
  · simp [hend] at htail ⊢
    exact htail
  · simp [hend] at htail ⊢
    exact htail

/-- One consume removes precisely the live head. This complete equation covers
empty, retained-stale, retired-stale and ring-end cases for every batch. -/
theorem consume_eq (hb : Bounds n t stale live) :
    (ringOf n batch t stale live).consume =
      match live with
      | [] => (none, ringOf n batch t stale [])
      | x :: xs =>
        if stale.length + 1 < batch ∧ t + (stale.length + 1) < n then
          (some x, ringOf n batch t (stale ++ [x]) xs)
        else (some x, ringOf n batch (loc n t (stale.length + 1)) [] xs) := by
  cases live with
  | nil => exact consume_empty hb
  | cons x xs =>
    simp only
    by_cases h : stale.length + 1 < batch ∧ t + (stale.length + 1) < n
    · rw [if_pos h]; exact consume_retain hb h.1 h.2
    · rw [if_neg h]; exact consume_retire hb (by omega)

/-- A successor representation is derived from the entry bounds and the
original consume result. Its live FIFO is precisely the old FIFO's tail. -/
theorem consume_preserves (hb : Bounds n t stale live) :
    ∃ t' stale', Bounds n t' stale' live.tail ∧
      (ringOf n batch t stale live).consume =
        (live.head?, ringOf n batch t' stale' live.tail) := by
  cases live with
  | nil => exact ⟨t, stale, hb, consume_empty hb⟩
  | cons x xs =>
    by_cases h : stale.length + 1 < batch ∧ t + (stale.length + 1) < n
    · exact ⟨t, stale ++ [x], retain_bounds hb h.2, consume_retain hb h.1 h.2⟩
    · exact ⟨loc n t (stale.length + 1), [], retire_bounds hb,
        consume_retire hb (by omega)⟩

end Leanux.Proofs.WG.Queues.Ring
