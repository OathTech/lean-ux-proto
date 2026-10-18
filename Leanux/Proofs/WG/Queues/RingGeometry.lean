import Leanux.Proofs.WG.Queues.PtrRing
import Lean.Elab.Tactic.Omega

/-! A physical ring consists of a consumed, still occupied prefix and a live
FIFO. Neither list is required to have distinct values. The tail-to-head stale
interval does not wrap; the occupied stale/live interval may wrap once. -/
namespace Leanux.Proofs.WG.Queues.Ring
open Leanux Leanux.WG
variable {α : Type}

def loc (n t k : Nat) : Nat := if t + k < n then t + k else t + k - n
def offset (n t j : Nat) : Nat := if t ≤ j then j - t else j + n - t

def Bounds (n t : Nat) (stale live : List α) : Prop :=
  t + stale.length < n ∧ stale.length + live.length ≤ n

def ringOf (n batch t : Nat) (stale live : List α) : PtrRing α :=
  { size := n, batch, consumerTail := t, consumerHead := t + stale.length,
    producer := loc n t (stale.length + live.length),
    slots := Array.ofFn fun j : Fin n => (stale ++ live)[offset n t j.val]? }

theorem loc_lt (ht : t < n) (hk : k ≤ n) : loc n t k < n := by
  unfold loc; split <;> omega

theorem offset_lt (ht : t < n) (hj : j < n) : offset n t j < n := by
  unfold offset; split <;> omega

theorem offset_loc (ht : t < n) (hk : k < n) : offset n t (loc n t k) = k := by
  unfold loc offset; split <;> split <;> omega

theorem loc_offset (ht : t < n) (hj : j < n) : loc n t (offset n t j) = j := by
  unfold loc offset; split <;> split <;> omega

theorem loc_eq_mod (ht : t < n) (hk : k ≤ n) : loc n t k = (t + k) % n := by
  unfold loc
  split
  · rename_i h; exact (Nat.mod_eq_of_lt h).symm
  · rename_i h
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem slot (hj : j < n) :
    ((ringOf n batch t stale live).slots[j]?).getD none =
      (stale ++ live)[offset n t j]? := by
  simp [ringOf, hj]

theorem init_eq (hn : 0 < n) :
    (PtrRing.init n : PtrRing α) = ringOf n (PtrRing.init (α := α) n).batch 0 [] [] := by
  simp only [PtrRing.init, ringOf, List.length_nil, Nat.zero_add, loc, hn,
    ↓reduceIte, List.nil_append, List.getElem?_nil]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp [Array.getElem?_replicate, Array.getElem?_ofFn]

theorem peek (hb : Bounds n t stale live) :
    (ringOf n batch t stale live).peek = live.head? := by
  have hn : n ≠ 0 := by obtain ⟨_, _⟩ := hb; omega
  have hz : (n == 0) = false := by simp [hn]
  change (if n == 0 then none else ((ringOf n batch t stale live).slots[t + stale.length]?).getD none) = _
  simp only [hz, Bool.false_eq_true, ↓reduceIte]
  rw [slot hb.1]
  have ho : offset n t (t + stale.length) = stale.length := by simp [offset]
  rw [ho, List.getElem?_append_right (by omega)]
  cases live <;> simp

theorem full (hb : Bounds n t stale live) :
    (ringOf n batch t stale live).full = (stale.length + live.length == n) := by
  have ht : t < n := by have := hb.1; omega
  have hn : n ≠ 0 := by omega
  have hp := loc_lt ht hb.2
  have hz : (n == 0) = false := by simp [hn]
  have hl := hb.2
  change ((n == 0) || (((ringOf n batch t stale live).slots[loc n t (stale.length + live.length)]?).getD none).isSome) = _
  rw [hz, Bool.false_or, slot hp]
  by_cases he : stale.length + live.length = n
  · have ho : offset n t (loc n t n) = 0 := by
      simp [loc, offset, show ¬ t + n < n by omega]
    rw [he, ho]
    simp [show 0 < stale.length + live.length by omega]
  · rw [offset_loc ht (by omega)]
    simp [he]

theorem count (hb : Bounds n t stale live) :
    (ringOf n batch t stale live).count = live.length := by
  have ht : t < n := by have := hb.1; omega
  have hs := hb.1
  have hl := hb.2
  have hn : n ≠ 0 := by omega
  simp only [PtrRing.count, show (ringOf n batch t stale live).size = n from rfl,
    show (n == 0) = false from by simp [hn], Bool.false_eq_true, ↓reduceIte, peek hb]
  change (if loc n t (stale.length + live.length) == t + stale.length then
    (if live.head?.isSome then n else 0)
    else (loc n t (stale.length + live.length) + n - (t + stale.length)) % n) = live.length
  by_cases hz : live = []
  · subst live
    simp [loc, hs]
  · have hpos : 0 < live.length := List.length_pos_iff.mpr hz
    have hsome : live.head?.isSome = true := by cases live <;> simp_all
    rw [hsome]
    unfold loc
    split
    · rename_i hw
      have he : ¬ t + (stale.length + live.length) = t + stale.length := by omega
      simp only [beq_iff_eq, he, ↓reduceIte]
      have har : t + (stale.length + live.length) + n - (t + stale.length) = n + live.length := by omega
      rw [har, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · rename_i hw
      by_cases he : t + (stale.length + live.length) - n = t + stale.length
      · simp only [beq_iff_eq, he, ↓reduceIte]; omega
      · simp only [beq_iff_eq, he, ↓reduceIte]
        have har : t + (stale.length + live.length) - n + n - (t + stale.length) = live.length := by omega
        rw [har, Nat.mod_eq_of_lt (by omega)]

theorem live_slot (hb : Bounds n t stale live) (hi : i < live.length) :
    ((ringOf n batch t stale live).slots[((ringOf n batch t stale live).consumerHead + i) % n]?).getD none = live[i]? := by
  have ht : t < n := by have := hb.1; omega
  have hk : stale.length + i < n := by have := hb.2; omega
  change ((ringOf n batch t stale live).slots[(t + stale.length + i) % n]?).getD none = _
  rw [Nat.add_assoc, ← loc_eq_mod ht (Nat.le_of_lt hk), slot (loc_lt ht (Nat.le_of_lt hk)),
    offset_loc ht hk, List.getElem?_append_right (by omega)]
  congr 1; omega

theorem range_filter_get (xs : List α) :
    (List.range xs.length).filterMap (fun i => xs[i]?) = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.filterMap_cons,
      List.getElem?_cons_zero, List.filterMap_map, List.getElem?_cons_succ,
      Function.comp_def, ih]

theorem items (hb : Bounds n t stale live) :
    (ringOf n batch t stale live).items = live := by
  unfold PtrRing.items
  rw [count hb]
  calc
    _ = (List.range live.length).filterMap (fun i => live[i]?) := by
      have congrOn {β : Type} (xs : List Nat) (f g : Nat → Option β)
          (h : ∀ i ∈ xs, f i = g i) : xs.filterMap f = xs.filterMap g := by
        induction xs with
        | nil => rfl
        | cons i xs ih =>
          simp only [List.filterMap_cons]
          rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]
      apply congrOn
      intro i hi
      exact live_slot hb (List.mem_range.mp hi)
    _ = live := range_filter_get live

/-- Zero size is treated separately: every guarded produce refuses and every
consume returns none. No positive-size representation premise is fabricated. -/
theorem zero_size (r : PtrRing α) (h : r.size = 0) (x : α) :
    r.full = true ∧ r.peek = none ∧ r.consume = (none, r) ∧
      r.count = 0 ∧ r.items = [] ∧ tryProduce r x = (false, r) := by
  simp [PtrRing.full, PtrRing.peek, PtrRing.consume, PtrRing.count, PtrRing.items,
    tryProduce, h]

end Leanux.Proofs.WG.Queues.Ring
