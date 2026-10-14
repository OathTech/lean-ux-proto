import Leanux.Proofs.WG.Queues.RingSteps

/-! Payload mapping commutes with the original physical-ring operations on
every ring, including malformed geometry. No injectivity is required. -/
namespace Leanux.Proofs.WG.Queues.Ring
open Leanux Leanux.WG

def mapRing (f : α → β) (r : PtrRing α) : PtrRing β :=
  { size := r.size, batch := r.batch, producer := r.producer,
    consumerHead := r.consumerHead, consumerTail := r.consumerTail,
    slots := r.slots.map (Option.map f) }

theorem map_slot (f : α → β) (s : Array (Option α)) (i : Nat) :
    ((s.map (Option.map f))[i]?).getD none = ((s[i]?).getD none).map f := by
  simp only [Array.getElem?_map]
  cases s[i]? <;> rfl

theorem full_map (f : α → β) (r : PtrRing α) : (mapRing f r).full = r.full := by
  simp only [PtrRing.full, mapRing, map_slot]
  cases (r.slots[r.producer]?).getD none <;> rfl

theorem peek_map (f : α → β) (r : PtrRing α) : (mapRing f r).peek = r.peek.map f := by
  simp only [PtrRing.peek, mapRing]
  by_cases h : (r.size == 0) = true
  · simp only [h, ↓reduceIte, Option.map_none]
  · simp only [h]; exact map_slot f r.slots r.consumerHead

theorem map_set (f : α → β) (s : Array (Option α)) (i : Nat) (x : Option α) :
    (s.set! i x).map (Option.map f) = (s.map (Option.map f)).set! i (x.map f) := by
  apply Array.ext_getElem?
  intro j
  simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]

theorem produce_map (f : α → β) (r : PtrRing α) (x : α) :
    mapRing f (r.produce x) = (mapRing f r).produce (f x) := by
  simp [mapRing, PtrRing.produce]

theorem clear_map (f : α → β) (s : Array (Option α)) (h t : Nat) :
    (PtrRing.discardOne.clear s h t).map (Option.map f) =
      PtrRing.discardOne.clear (s.map (Option.map f)) h t := by
  unfold PtrRing.discardOne.clear
  generalize List.range (h + 1 - t) = is
  induction is generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.foldl_cons]; rw [ih, map_set]; rfl

theorem discard_map (f : α → β) (r : PtrRing α) :
    mapRing f r.discardOne = (mapRing f r).discardOne := by
  by_cases h : r.consumerHead + 1 - r.consumerTail ≥ r.batch <;>
    by_cases e : r.consumerHead + 1 ≥ r.size <;>
    simp [PtrRing.discardOne, mapRing, h, e, clear_map]

theorem consume_map (f : α → β) (r : PtrRing α) :
    (mapRing f r).consume = (r.consume.1.map f, mapRing f r.consume.2) := by
  simp only [PtrRing.consume, peek_map]
  cases r.peek <;> simp [discard_map]

theorem count_map (f : α → β) (r : PtrRing α) : (mapRing f r).count = r.count := by
  simp only [PtrRing.count, peek_map]
  cases r.peek <;> rfl

theorem items_map (f : α → β) (r : PtrRing α) :
    (mapRing f r).items = r.items.map f := by
  unfold PtrRing.items
  rw [count_map]
  simp only [mapRing, map_slot, List.map_filterMap]

theorem tryProduce_map (f : α → β) (r : PtrRing α) (x : α) :
    tryProduce (mapRing f r) (f x) = ((tryProduce r x).1, mapRing f (tryProduce r x).2) := by
  simp only [tryProduce, full_map]
  split <;> simp [produce_map]

theorem init_map (f : α → β) (n : Nat) :
    mapRing f (PtrRing.init n) = PtrRing.init n := by
  simp [mapRing, PtrRing.init]

end Leanux.Proofs.WG.Queues.Ring
