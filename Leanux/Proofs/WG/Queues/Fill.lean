import Leanux.Proofs.WG.Queues.PtrRing
import Lean.Elab.Tactic.Omega

/-! A symbolic no-wrap fill segment. Slots below the producer are occupied;
the consumer cursors and retirement batch remain independent parameters. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG

def filled (size batch head tail n : Nat) (label : Nat → α) : PtrRing α :=
  { size, batch, consumerHead := head, consumerTail := tail,
    producer := if n < size then n else 0,
    slots := Array.ofFn fun i : Fin size => if i.val < n then some (label i.val) else none }

theorem init_filled (size : Nat) (label : Nat → α) :
    PtrRing.init size = filled size (PtrRing.init (α := α) size).batch 0 0 0 label := by
  simp only [PtrRing.init, filled, Nat.not_lt_zero, ↓reduceIte, ite_self]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp [Array.getElem?_replicate, Array.getElem?_ofFn]

/-- A consume before either retirement threshold advances only the head;
the returned item remains physically present in its old slot. -/
theorem filled_consume_unretired (size batch head tail n : Nat) (label : Nat → α)
    (hh : head < n) (hend : head + 1 < size)
    (hbatch : head + 1 - tail < batch) :
    (filled size batch head tail n label).consume =
      (some (label head), filled size batch (head + 1) tail n label) := by
  have hs : size ≠ 0 := by omega
  have hi : head < size := by omega
  simp [PtrRing.consume, PtrRing.peek, PtrRing.discardOne, filled,
    hs, hi, hh, show ¬head + 1 ≥ size by omega,
    show ¬head + 1 - tail ≥ batch by omega]

theorem filled_full_false (size batch head tail n : Nat) (label : Nat → α)
    (hn : n < size) : (filled size batch head tail n label).full = false := by
  have hs : size ≠ 0 := by omega
  simp [filled, PtrRing.full, hn, hs]

theorem filled_produce (size batch head tail n : Nat) (label : Nat → α)
    (hn : n < size) :
    (filled size batch head tail n label).produce (label n) =
      filled size batch head tail (n + 1) label := by
  have hc : (if n + 1 ≥ size then 0 else n + 1) =
      (if n + 1 < size then n + 1 else 0) := by
    by_cases h : n + 1 < size
    · simp [h, show ¬ n + 1 ≥ size by omega]
    · simp [h, show n + 1 ≥ size by omega]
  simp only [filled, PtrRing.produce, hn, ↓reduceIte, hc]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    Array.size_ofFn, Array.getElem?_ofFn]
  by_cases he : n = i
  · subst i
    simp [hn]
  · by_cases hi : i < size
    · by_cases hlt : i < n
      · simp [he, hi, hlt, show i < n + 1 by omega]
      · simp [he, hi, hlt, show ¬i < n + 1 by omega]
    · simp [he, hi]

theorem produceMany_append (r : PtrRing α) (xs ys : List α) :
    produceMany r (xs ++ ys) =
      let first := produceMany r xs
      let last := produceMany first.2 ys
      (first.1 ++ last.1, last.2) := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, produceMany, ih, List.cons_append]

theorem produceMany_filled (size batch head tail : Nat) (label : Nat → α)
    (n count : Nat) (hb : n + count ≤ size) :
    produceMany (filled size batch head tail n label)
      ((List.range' n count).map label) =
      (List.replicate count true, filled size batch head tail (n + count) label) := by
  induction count generalizing n with
  | zero => simp [produceMany]
  | succ count ih =>
    have hn : n < size := by omega
    simp only [List.range'_succ, List.map_cons, produceMany,
      tryProduce_free _ _ (filled_full_false size batch head tail n label hn),
      filled_produce size batch head tail n label hn]
    rw [ih (n + 1) (by omega)]
    simp [List.replicate_succ, Nat.add_comm, Nat.add_left_comm]

end Leanux.Proofs.WG.Queues
