import Leanux.Proofs.WG.Queues.RingSteps
import Leanux.Proofs.WG.Queues.Fill

/-! Payload-generic source geometry for a producer-only segment. Repeated
payloads are permitted; this is not a scheduler-reachability or delivery claim. -/
namespace Leanux.Proofs.WG.Queues.FullRingGeometry
open Leanux Leanux.WG
variable {α : Type}

/-- Two actual produce/consume pairs. -/
def pairs (r : PtrRing α) (first second : α) : PtrRing α :=
  (((r.produce first).consume.2).produce second).consume.2

theorem pairs_empty (n batch : Nat) (hn : 2<n) (hb : 2<batch) (first second : α) :
    pairs (Ring.ringOf n batch 0 [] []) first second =
      Ring.ringOf n batch 0 [first,second] [] := by
  unfold pairs
  rw [Ring.produce (stale:=[]) (live:=[]) (by simp [Ring.Bounds]; omega) (by simp; omega) first]
  simp only [List.nil_append]
  rw [Ring.consume_retain (stale:=[]) (xs:=[]) (by simp [Ring.Bounds]; omega)
    (by simp; omega) (by simp; omega)]
  simp only [List.nil_append]
  rw [Ring.produce (stale:=[first]) (live:=[]) (by simp [Ring.Bounds]; omega) (by simp; omega) second]
  simp only [List.nil_append]
  rw [Ring.consume_retain (stale:=[first]) (xs:=[]) (by simp [Ring.Bounds]; omega)
    (by simp; omega) (by simp; omega)]
  rfl

/-- Every offered item fits when the initial occupied interval plus this
source list fits. Consumer cursors and stale slots retain their original role. -/
theorem produceMany_fits (n batch tail : Nat) (stale live xs : List α)
    (bounds : Ring.Bounds n tail stale live)
    (room : stale.length+live.length+xs.length≤n) :
    produceMany (Ring.ringOf n batch tail stale live) xs =
      (List.replicate xs.length true,Ring.ringOf n batch tail stale (live++xs)) := by
  induction xs generalizing live with
  | nil => simp only [produceMany,List.length_nil,List.replicate_zero,List.append_nil]
  | cons x xs ih =>
    have free : stale.length+live.length<n := by simp only [List.length_cons] at room; omega
    have next := Ring.produce_bounds bounds free x
    have fits : stale.length+(live++[x]).length+xs.length≤n := by
      simp only [List.length_append,List.length_cons,List.length_nil] at room ⊢
      omega
    have notFull : (Ring.ringOf n batch tail stale live).full=false := by
      rw [Ring.full bounds]
      simp [show stale.length+live.length≠n by omega]
    simp only [produceMany,tryProduce_free _ _ notFull,Ring.produce bounds free x]
    rw [ih (live++[x]) next fits]
    simp only [List.length_cons,List.replicate_succ,List.append_assoc,List.singleton_append]

/-- Once the exact successful prefix fills the physical ring, every remaining
source offer refuses without moving its producer or replacing a slot. -/
theorem produceMany_fill_then_refuse (n batch tail : Nat) (stale live accepted rejected : List α)
    (bounds : Ring.Bounds n tail stale live)
    (filled : stale.length+live.length+accepted.length=n) :
    produceMany (Ring.ringOf n batch tail stale live) (accepted++rejected) =
      (List.replicate accepted.length true ++ List.replicate rejected.length false,
        Ring.ringOf n batch tail stale (live++accepted)) := by
  have next : Ring.Bounds n tail stale (live++accepted) := by
    exact ⟨bounds.1,by simp only [List.length_append]; omega⟩
  have full : (Ring.ringOf n batch tail stale (live++accepted)).full=true := by
    rw [Ring.full next]
    simp only [List.length_append]
    have eq : stale.length+(live.length+accepted.length)=n := by omega
    simp only [eq,beq_self_eq_true]
  rw [produceMany_append,produceMany_fits n batch tail stale live accepted bounds (by omega)]
  dsimp only
  rw [produceMany_full _ rejected full]

/-- The carried geometry is derived from the two original source pairs,
not assumed at the start of the 1024-offer segment. -/
theorem two_carried (first second : α) :
    pairs (PtrRing.init 1024) first second=Ring.ringOf 1024 16 0 [first,second] [] := by
  have initial : (PtrRing.init 1024 : PtrRing α)=Ring.ringOf 1024 16 0 [] [] :=
    Ring.init_eq (by decide)
  rw [initial]
  exact pairs_empty 1024 16 (by decide) (by decide) first second

/-- Arbitrary 1024 offered payloads produce exactly 1022 successful source
positions and two refusals. The final physical ring is computed from the source. -/
theorem w7_result (first second : α) (offered : List α) (size : offered.length=1024) :
    produceMany (pairs (PtrRing.init 1024) first second) offered =
      (List.replicate 1022 true ++ [false,false],
        Ring.ringOf 1024 16 0 [first,second] (offered.take 1022)) := by
  have taken : (offered.take 1022).length=1022 := by simp only [List.length_take,size]; rfl
  have dropped : (offered.drop 1022).length=2 := by simp only [List.length_drop,size]
  have full := produceMany_fill_then_refuse 1024 16 0 [first,second] []
    (offered.take 1022) (offered.drop 1022)
    (by simp [Ring.Bounds]) (by simp only [List.length_cons,List.length_nil,taken])
  rw [List.take_append_drop] at full
  rw [two_carried]
  simpa only [List.nil_append,taken,dropped,
    show List.replicate 2 false=[false,false] from rfl] using full

theorem w7_outcomes (first second : α) (offered : List α) (size : offered.length=1024) :
    (produceMany (pairs (PtrRing.init 1024) first second) offered).1 =
      List.replicate 1022 true ++ [false,false] := by
  rw [w7_result first second offered size]

/-- The live FIFO consists exactly of the accepted prefix. The two consumed
occurrences remain only in stale physical slots; equal payload values may
recur among the newly accepted occurrences. -/
theorem w7_items (first second : α) (offered : List α) (size : offered.length=1024) :
    (produceMany (pairs (PtrRing.init 1024) first second) offered).2.items=offered.take 1022 := by
  rw [w7_result first second offered size]
  exact Ring.items (by simp [Ring.Bounds,List.length_take,size])

theorem w7_geometry (first second : α) (offered : List α) (size : offered.length=1024) :
    let final := (produceMany (pairs (PtrRing.init 1024) first second) offered).2
    final.producer=0 ∧ final.consumerHead=2 ∧ final.consumerTail=0 ∧
    final.full=true ∧ final.count=1022 ∧
    final.slots[0]?=some (some first) ∧ final.slots[1]?=some (some second) := by
  rw [w7_result first second offered size]
  have taken : (offered.take 1022).length=1022 := by simp only [List.length_take,size]; rfl
  have bounds : Ring.Bounds 1024 0 [first,second] (offered.take 1022) := by
    simp [Ring.Bounds,taken]
  dsimp only
  rw [Ring.full bounds,Ring.count bounds]
  simp only [taken,Ring.ringOf,Ring.loc,Ring.offset,List.length_cons,List.length_nil,
    Nat.zero_add,Array.getElem?_ofFn,List.cons_append]
  simp

/-- In particular, all offered items may be singleton actual packet IDs.
The IDs and the two earlier carried items are arbitrary. -/
theorem w7_singletons (first second : List SkbId) (ids : List SkbId) (size : ids.length=1024) :
    (produceMany (pairs (PtrRing.init 1024) first second) (ids.map fun id=>[id])).1 =
      List.replicate 1022 true ++ [false,false] ∧
    (produceMany (pairs (PtrRing.init 1024) first second) (ids.map fun id=>[id])).2.items =
      (ids.take 1022).map (fun id=>[id]) := by
  have length : (ids.map fun id=>[id]).length=1024 := by simp only [List.length_map,size]
  refine ⟨w7_outcomes first second _ length,?_⟩
  rw [w7_items first second _ length,←List.map_take]

end Leanux.Proofs.WG.Queues.FullRingGeometry
