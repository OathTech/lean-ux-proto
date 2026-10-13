import Leanux.Proofs.WG.Queues.FullRing
import Leanux.Proofs.WG.Queues.Enqueue
import Leanux.Proofs.WG.Queues.PrevQueue
import Leanux.Proofs.WG.Queues.RxHelperFrames

/-! R4 queue components: physical-ring refusal, original prev_queue FIFO laws,
and successful-endpoint receive-queue helper frames. Whole recorded-schedule delivery,
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

/-- Original enqueue appends after all logically held items, including a
cached peek. It does not itself perform the caller's capacity check. -/
theorem original_prev_enqueue (q : PrevQueue α) (x : α) :
    (q.enqueue x).all = q.all ++ [x] := Queues.prev_enqueue_all q x

/-- Every normal original dequeue removes the first underlying item and
preserves the cached peek and Kernel. No queue-validity premise is imposed. -/
theorem original_prev_dequeue (q : PrevQueue α) (w v : World)
    (head : Option α) (q' : PrevQueue α)
    (hr : q.dequeue.run w = .ok ((head, q'), v)) :
    head = q.items.head? ∧ q'.items = q.items.tail ∧
      q'.peeked = q.peeked ∧ v.k = w.k :=
  Queues.prev_dequeue_normal q w v head q' hr

/-- A normal original peek returns the logical first item and preserves all
logical contents. Its cached result agrees with that item. -/
theorem original_prev_peek (q : PrevQueue α) (w v : World)
    (head : Option α) (q' : PrevQueue α)
    (hr : q.peek.run w = .ok ((head, q'), v)) :
    head = q.all.head? ∧ q'.all = q.all ∧ q'.peeked = head ∧ v.k = w.k :=
  Queues.prev_peek_normal q w v head q' hr

/-- Peeking a present item and dropping the peek removes exactly the logical
head. This local queue statement does not yet describe original rxPoll. -/
theorem original_prev_peek_drop (q : PrevQueue α) (w v : World)
    (x : α) (q' : PrevQueue α)
    (hr : q.peek.run w = .ok ((some x, q'), v)) :
    q.all = x :: q'.dropPeeked.all := Queues.prev_peek_then_drop q w v x q' hr

/-- Structurally coherent queues have ordinary dequeue and peek results. -/
theorem original_prev_total (q : PrevQueue α) (w : World) (hc : Queues.PrevCoherent q) :
    (∃ head q' v, q.dequeue.run w = .ok ((head, q'), v)) ∧
    (∃ head q' v, q.peek.run w = .ok ((head, q'), v)) :=
  ⟨Queues.prev_dequeue_total q w hc, Queues.prev_peek_total q w hc⟩

/-- The malformed nonstub empty queue fails at the original invariant,
unless an existing cached peek avoids the dequeue. -/
theorem original_prev_malformed (q : PrevQueue α) (w : World)
    (hp : q.peeked = none) (ht : q.tailIsStub = false) (hi : q.items = []) :
    q.peek.run w = .error (.invariant "prev_queue: a tail item without an entry") :=
  Queues.prev_peek_malformed q w hp ht hi

/-- Complete original reference-acquisition, keypair-release and RX-free
helpers preserve every peer's full receive queue with its epoch and identity.
These are successful-endpoint frames, not internal access-history claims. -/
theorem original_reference_queue_frames (pid : PeerId) (peer : Option PeerId)
    (kp : Option KeypairId) (now : Bool) (id : SkbId) :
    Framing.SameView Queues.rxQueues (peerGet pid) ∧
    Framing.SameView Queues.rxQueues (peerGetMaybeZero peer) ∧
    Framing.SameView Queues.rxQueues (keypairGet kp) ∧
    Framing.SameView Queues.rxQueues (keypairPut kp now) ∧
    Framing.SameView Queues.rxQueues (freeRxSkb id) :=
  ⟨Queues.peerGet_rxQueues pid, Queues.peerGetMaybeZero_rxQueues peer,
    Queues.keypairGet_rxQueues kp, Queues.keypairPut_rxQueues kp now,
    Queues.freeRxSkb_rxQueues id⟩

/-- Peer release may delete an entry; every surviving entry retains its exact
queue, peer identity and device epoch. No reference-ownership premise is used. -/
theorem original_peer_release_retains_queues (peer : Option PeerId) :
    Queues.RetainsRx (peerPut peer) := Queues.peerPut_rxQueues peer

/-- Replay validation and key confirmation preserve the full receive-queue
view on normal return. Malformed replay bitmaps remain admitted and may Stop. -/
theorem original_validation_queue_frames (pid : PeerId) (kp : KeypairId) (nonce : Nat) :
    Framing.SameView Queues.rxQueues (counterValidate kp nonce) ∧
    Framing.SameView Queues.rxQueues (receivedWithKeypair pid kp) :=
  ⟨Queues.counterValidate_rxQueues kp nonce, Queues.receivedWithKeypair_rxQueues pid kp⟩

end Leanux.Proofs.WG.DeliveryOrder
