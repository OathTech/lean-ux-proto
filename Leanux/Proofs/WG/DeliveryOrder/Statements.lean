import Leanux.Proofs.WG.Queues.FullRing
import Leanux.Proofs.WG.Queues.Enqueue

/-! R4's full-ring component. These statements concern a producer-only ring
segment and the original enqueue helper. Whole recorded-schedule delivery,
pipeline conservation, and callback/scheduler ownership are separate obligations. -/
namespace Leanux.Proofs.WG.DeliveryOrder
open Leanux Leanux.WG

/-- Any finite sequence of production attempts against an already full ring
rejects every item and leaves the complete ring unchanged. -/
theorem full_ring_stalls (r : PtrRing α) (xs : List α) (hf : r.full = true) :
    Queues.produceMany r xs = (List.replicate xs.length false, r) :=
  Queues.produceMany_full r xs hf

/-- Two literal produce/consume pairs leave an empty logical queue with both
consumed slots still occupied below the original batch threshold. -/
theorem two_carried_slots_initial :
    Queues.carriedTwo.producer = 2 ∧ Queues.carriedTwo.consumerHead = 2 ∧
    Queues.carriedTwo.consumerTail = 0 ∧ Queues.carriedTwo.count = 0 ∧
    Queues.carriedTwo.slots[0]? = some (some [0]) ∧
    Queues.carriedTwo.slots[1]? = some (some [1]) :=
  Queues.carriedTwo_geometry

/-- From those two carried slots, the next 1024 producer-only attempts accept
exactly the first 1022 and reject the last two, in that order. This closed ring
witness is not a replay of an entire recorded scheduler execution. -/
theorem two_carried_slots_outcomes :
    Queues.wrapRun.1 = List.replicate 1022 true ++ [false, false] :=
  Queues.wrapRun_outcomes

/-- The final wrapped producer slot is full. The logical count is 1022,
while the old slots 0 and 1 remain physically occupied. -/
theorem two_carried_slots_final :
    Queues.wrapRun.2.producer = 0 ∧ Queues.wrapRun.2.consumerHead = 2 ∧
    Queues.wrapRun.2.consumerTail = 0 ∧ Queues.wrapRun.2.full = true ∧
    Queues.wrapRun.2.count = 1022 ∧
    Queues.wrapRun.2.slots[0]? = some (some [0]) ∧
    Queues.wrapRun.2.slots[1]? = some (some [1]) :=
  Queues.wrapRun_geometry

/-- The final logical FIFO contains exactly the accepted new items in order;
the two previously consumed items and the two rejected items are absent. -/
theorem two_carried_slots_fifo :
    Queues.wrapRun.2.items = (List.range 1022).map (fun i => [i + 2]) :=
  Queues.wrapRun_items

/-- Every ordinary return of the complete original enqueue is success,
peer-queue refusal, or physical ring refusal with the corresponding exact
ring effect. Original missing-object and queue-work Stops are not ruled out. -/
theorem original_enqueue_result (pid : PeerId) (item : List SkbId)
    (w v : World) (ret : Int)
    (hr : (enqueuePerDeviceAndPeer pid item).run w = .ok (ret, v)) :
    Queues.EnqueueResult (Queues.encryptRing w) item ret (Queues.encryptRing v) :=
  Queues.enqueue_ring_result pid item w v ret hr

/-- An original -EPIPE return means the entry encrypt ring was physically
full and is unchanged at return. Earlier peer-queue and packet-state updates
may have occurred; no ownership or well-formedness premise is imposed. -/
theorem original_enqueue_epipe (pid : PeerId) (item : List SkbId) (w v : World)
    (hr : (enqueuePerDeviceAndPeer pid item).run w = .ok (-WG.EPIPE, v)) :
    Queues.encryptRing v = Queues.encryptRing w ∧
      ∃ r, Queues.encryptRing w = some r ∧ r.full = true :=
  Queues.enqueue_epipe pid item w v hr

end Leanux.Proofs.WG.DeliveryOrder
