import Leanux.Proofs.WG.Queues.Fill

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

/-! A closed witness over the original 1024-slot ring. It models two earlier
produce/consume pairs followed by a producer-only segment. The witness itself
is not a recorded scheduler run or a packet-delivery theorem. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG

/-- The keepalive and one earlier item have each been produced and consumed;
neither consumed slot has reached the batch-retirement threshold. -/
def carriedTwo : PtrRing (List SkbId) :=
  let r := (PtrRing.init 1024).produce [0]
  let r := r.consume.2
  let r := r.produce [1]
  r.consume.2

def wrapItems : List (List SkbId) := (List.range 1024).map (fun i => [i + 2])

def wrapRun : List Bool × PtrRing (List SkbId) := produceMany carriedTwo wrapItems

theorem carriedTwo_eq_filled :
    carriedTwo = filled 1024 16 2 0 2 (fun i : Nat => [i]) := by
  have hinit : (PtrRing.init 1024 : PtrRing (List SkbId)) =
      filled 1024 16 0 0 0 (fun i : Nat => [i]) := init_filled 1024 _
  unfold carriedTwo
  rw [hinit, filled_produce 1024 16 0 0 0 _ (by decide)]
  dsimp only
  rw [filled_consume_unretired 1024 16 0 0 1 _ (by decide) (by decide) (by decide)]
  dsimp only
  rw [filled_produce 1024 16 1 0 1 _ (by decide)]
  rw [filled_consume_unretired 1024 16 1 0 2 _ (by decide) (by decide) (by decide)]

theorem wrapItems_split :
    wrapItems = (List.range' 2 1022).map (fun i : Nat => [i]) ++ [[1024], [1025]] := by
  have hlast : (List.range' 1024 2).map (fun i : Nat => [i]) = [[1024], [1025]] := rfl
  rw [← hlast, ← List.map_append]
  have hr : List.range' 2 1022 ++ List.range' 1024 2 = List.range' 2 1024 :=
    List.range'_append_1
  rw [hr, List.range'_eq_map_range, List.map_map]
  simp [wrapItems, Function.comp_def, Nat.add_comm]

theorem wrapRun_result :
    wrapRun = (List.replicate 1022 true ++ [false, false],
      filled 1024 16 2 0 1024 (fun i : Nat => [i])) := by
  unfold wrapRun
  rw [carriedTwo_eq_filled, wrapItems_split, produceMany_append,
    produceMany_filled 1024 16 2 0 (fun i : Nat => [i]) 2 1022 (by decide)]
  have hf : (filled 1024 16 2 0 1024 (fun i : Nat => [i])).full = true := by
    simp [filled, PtrRing.full]
  dsimp only
  rw [produceMany_full _ _ hf]
  rfl

theorem carriedTwo_geometry :
    carriedTwo.producer = 2 ∧ carriedTwo.consumerHead = 2 ∧
    carriedTwo.consumerTail = 0 ∧ carriedTwo.count = 0 ∧
    carriedTwo.slots[0]? = some (some [0]) ∧
    carriedTwo.slots[1]? = some (some [1]) := by
  rw [carriedTwo_eq_filled]
  simp [filled, PtrRing.count, PtrRing.peek]

theorem wrapRun_outcomes :
    wrapRun.1 = List.replicate 1022 true ++ [false, false] := by rw [wrapRun_result]

theorem wrapRun_geometry :
    wrapRun.2.producer = 0 ∧ wrapRun.2.consumerHead = 2 ∧
    wrapRun.2.consumerTail = 0 ∧ wrapRun.2.full = true ∧
    wrapRun.2.count = 1022 ∧
    wrapRun.2.slots[0]? = some (some [0]) ∧
    wrapRun.2.slots[1]? = some (some [1]) := by
  rw [wrapRun_result]
  simp [filled, PtrRing.full, PtrRing.count]

theorem wrapRun_items :
    wrapRun.2.items = (List.range 1022).map (fun i => [i + 2]) := by
  have hc : wrapRun.2.count = 1022 := wrapRun_geometry.2.2.2.2.1
  unfold PtrRing.items
  rw [hc, wrapRun_result]
  change (List.range 1022).filterMap _ = _
  have congrOn (xs : List Nat) (f g : Nat → Option (List Nat))
      (h : ∀ i ∈ xs, f i = g i) : xs.filterMap f = xs.filterMap g := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      simp only [List.filterMap_cons]
      rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]
  calc
    _ = (List.range 1022).filterMap (fun i => some [i + 2]) := by
      apply congrOn
      intro i hi
      have hn : i < 1022 := List.mem_range.mp hi
      have hb' : i + 2 < 1024 := by omega
      simp [filled, Nat.mod_eq_of_lt hb', hb', Nat.add_comm]
    _ = _ := by simp only [List.filterMap_eq_map']

end Leanux.Proofs.WG.Queues
