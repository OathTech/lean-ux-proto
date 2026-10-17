import Leanux.Proofs.WG.Queues.HandshakeWorker
import Leanux.Proofs.WG.Queues.DeviceBoundary
import Leanux.Proofs.WG.Queues.HolderInitial
import Leanux.Proofs.WG.Queues.HolderStopPhysical
import Leanux.Proofs.WG.Queues.CreationLoan
import Leanux.Proofs.WG.Queues.HolderAuxScheduler
import Leanux.Proofs.WG.Queues.AdmissionOutcome
import Leanux.Proofs.WG.Queues.SetPeerBoundary
import Leanux.Proofs.WG.Queues.HolderDeviceCreate
import Leanux.Proofs.WG.Queues.AdmissionJournal
import Leanux.Proofs.WG.Queues.AdmissionPath
import Leanux.Proofs.WG.Queues.HandshakeAfterMac
import Leanux.Proofs.WG.Queues.HandshakeReception
import Leanux.Proofs.WG.Queues.HolderAuxiliary
import Leanux.Proofs.WG.Queues.HolderConfigUpdate
import Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration
import Leanux.Proofs.WG.Queues.CurrentSlotHistory
import Leanux.Proofs.WG.Queues.HandshakeEntry
import Leanux.Proofs.WG.Queues.HolderTxActivation
import Leanux.Proofs.WG.Queues.HolderTimerPhysical
import Leanux.Proofs.WG.Queues.BaseLookupRemoval
import Leanux.Proofs.WG.Queues.HolderAllowedIps
import Leanux.Proofs.WG.Queues.HandshakeReceive
import Leanux.Proofs.WG.Queues.HolderCreation
import Leanux.Proofs.WG.Queues.HolderBaseRetirement
import Leanux.Proofs.WG.Queues.TxHolderStep
import Leanux.Proofs.WG.Queues.DumpCallers
import Leanux.Proofs.WG.Queues.HolderEncryptHistory
import Leanux.Proofs.WG.Queues.SessionCarrier
import Leanux.Proofs.WG.Queues.HolderSingleRetirement
import Leanux.Proofs.WG.Queues.HolderTimers
import Leanux.Proofs.WG.Queues.HolderTxHistory
import Leanux.Proofs.WG.Queues.HolderPollBoundary
import Leanux.Proofs.WG.Queues.HolderDecryptHistory
import Leanux.Proofs.WG.Queues.HolderAdmission
import Leanux.Proofs.WG.Queues.HolderSendDispatch
import Leanux.Proofs.WG.Queues.HolderClearDispatch
import Leanux.Proofs.WG.Queues.HolderDrains
import Leanux.Proofs.WG.Queues.DumpSerialization
import Leanux.Proofs.WG.Queues.DumpSockets
import Leanux.Proofs.WG.Queues.CryptedTxDebit
import Leanux.Proofs.WG.Queues.TxCompletionQueues
import Leanux.Proofs.WG.Queues.BaseCreation
import Leanux.Proofs.WG.Queues.BaseRemoval
import Leanux.Proofs.WG.Queues.DurableHolders
import Leanux.Proofs.WG.Queues.HolderCallbacks
import Leanux.Proofs.WG.Queues.HolderPollCallbacks
import Leanux.Proofs.WG.Queues.TxQueueDebit
import Leanux.Proofs.WG.Queues.TxFreshReservation
import Leanux.Proofs.WG.Queues.DumpReservation
import Leanux.Proofs.WG.Queues.DecryptConcrete
import Leanux.Proofs.WG.Queues.RxPollBoundary
import Leanux.Proofs.WG.Queues.CurrentSlotCompletion
import Leanux.Proofs.WG.Queues.SendWork
import Leanux.Proofs.WG.Queues.EnvClearDispatch
import Leanux.Proofs.WG.Queues.SendEnvironment
import Leanux.Proofs.WG.Queues.NapiCarrier
import Leanux.Proofs.WG.Queues.RxCarrierInitial
import Leanux.Proofs.WG.Queues.RxDrainBoundary
import Leanux.Proofs.WG.Queues.DecryptStable
import Leanux.Proofs.WG.Queues.RxClearQueue
import Leanux.Proofs.WG.Queues.CurrentSlots
import Leanux.Proofs.WG.Queues.NapiFrames
import Leanux.Proofs.WG.Queues.RxStableFrames

import Leanux.Proofs.WG.Queues.RxIngressStable
import Leanux.Proofs.WG.Queues.RxConsumeProtection
import Leanux.Proofs.WG.Queues.RxCleanupFindings
import Leanux.Proofs.WG.Queues.RxPollCarrier
import Leanux.Proofs.WG.Queues.RxIngressProtection
import Leanux.Proofs.WG.Queues.RxLinkRunner
import Leanux.Proofs.WG.Queues.RxPollReceiptLink
import Leanux.Proofs.WG.Queues.RxPollDisposition
import Leanux.Proofs.WG.Queues.RxRunnerHistory
import Leanux.Proofs.WG.Queues.FullRing
import Leanux.Proofs.WG.Queues.RingOccurrences
import Leanux.Proofs.WG.Queues.EnqueueAdmission
import Leanux.Proofs.WG.Queues.Enqueue
import Leanux.Proofs.WG.Queues.PrevQueue
import Leanux.Proofs.WG.Queues.RxCompletionFrame
import Leanux.Proofs.WG.Queues.RxPollOrder
import Leanux.Proofs.WG.Queues.RxPollGroOrder
import Leanux.Proofs.WG.Queues.SelectedGro
import Leanux.Proofs.WG.Queues.RxPollProjection
import Leanux.Proofs.WG.Queues.RxPollProvenance
import Leanux.Proofs.WG.Queues.RxRingWorker
import Leanux.Proofs.WG.Queues.TxRingWorker
import Leanux.Proofs.WG.Queues.RxRingTrials
import Leanux.Proofs.WG.Queues.RxBorrow
import Leanux.Proofs.WG.Queues.TxDispositionStep
import Leanux.Proofs.WG.Queues.TxDispositionEndpoints
import Leanux.Proofs.WG.Queues.RxCompletionRunner

import Leanux.Proofs.WG.Queues.RxPollStampPhase
import Leanux.Proofs.WG.Queues.RxPollComposition
import Leanux.Proofs.WG.Queues.RxPollCompletion
import Leanux.Proofs.WG.Queues.RxNapiHistory
import Leanux.Proofs.WG.Queues.RxActivationHistory
import Leanux.Proofs.WG.Queues.RxScheduleHistory
import Leanux.Proofs.WG.Queues.RxEnvBatchHistory
import Leanux.Proofs.WG.Queues.RxEnvControlsHistory

/-! R4 queue components: physical-ring refusal, original prev_queue FIFO laws,
and successful-endpoint receive-queue helper frames. Whole recorded-schedule delivery,
pipeline conservation, and callback/scheduler ownership are separate obligations. -/
namespace Leanux.Proofs.WG.DeliveryOrder
open Leanux Leanux.WG

/-- Every positive-size original initialization is represented with empty
stale and live lists and the original batch. Zero size is separate below. -/
theorem initialized_ring_representation (n : Nat) (hn : 0 < n) :
    (PtrRing.init n : PtrRing α) =
      Queues.Ring.ringOf n (PtrRing.init (α := α) n).batch 0 [] [] ∧
    Queues.Ring.Bounds n 0 ([] : List α) [] :=
  ⟨Queues.Ring.init_eq hn, by simp [Queues.Ring.Bounds, hn]⟩

/-- Physical fullness counts both stale occupied slots and live items; peek,
logical count and items see exactly the live FIFO, including multiplicity. -/
theorem represented_ring_geometry (n batch t : Nat) (stale live : List α)
    (hb : Queues.Ring.Bounds n t stale live) :
    let r := Queues.Ring.ringOf n batch t stale live
    r.full = (stale.length + live.length == n) ∧ r.peek = live.head? ∧
      r.count = live.length ∧ r.items = live :=
  ⟨Queues.Ring.full hb, Queues.Ring.peek hb, Queues.Ring.count hb, Queues.Ring.items hb⟩

/-- An original physically free producer appends one live occurrence and
preserves the representation bounds. Values need not be distinct. -/
theorem represented_ring_produce (n batch t : Nat) (stale live : List α) (x : α)
    (hb : Queues.Ring.Bounds n t stale live)
    (hf : (Queues.Ring.ringOf n batch t stale live).full = false) :
    (Queues.Ring.ringOf n batch t stale live).produce x =
      Queues.Ring.ringOf n batch t stale (live ++ [x]) ∧
    Queues.Ring.Bounds n t stale (live ++ [x]) := by
  rw [Queues.Ring.full hb] at hf
  have hfree : stale.length + live.length < n := by
    have := hb.2
    simp only [beq_eq_false_iff_ne] at hf
    omega
  exact ⟨Queues.Ring.produce hb hfree x, Queues.Ring.produce_bounds hb hfree x⟩

/-- Complete original consume geometry: empty consumes do nothing; a live
head either joins the stale prefix or retires that prefix at the batch/end
threshold. This includes batch zero, oversized batches and end wrap. -/
theorem represented_ring_consume (n batch t : Nat) (stale live : List α)
    (hb : Queues.Ring.Bounds n t stale live) :
    (Queues.Ring.ringOf n batch t stale live).consume =
      match live with
      | [] => (none, Queues.Ring.ringOf n batch t stale [])
      | x :: xs =>
        if stale.length + 1 < batch ∧ t + (stale.length + 1) < n then
          (some x, Queues.Ring.ringOf n batch t (stale ++ [x]) xs)
        else (some x, Queues.Ring.ringOf n batch
          (Queues.Ring.loc n t (stale.length + 1)) [] xs) :=
  by
    cases live with
    | nil => exact Queues.Ring.consume_empty hb
    | cons x xs => simpa only using Queues.Ring.consume_eq (batch := batch) hb

/-- The successor bounds are proved, not assumed: original consume returns
the live head and a represented ring whose live FIFO is exactly the tail. -/
theorem represented_ring_consume_preserves (n batch t : Nat) (stale live : List α)
    (hb : Queues.Ring.Bounds n t stale live) :
    ∃ t' stale', Queues.Ring.Bounds n t' stale' live.tail ∧
      (Queues.Ring.ringOf n batch t stale live).consume =
        (live.head?, Queues.Ring.ringOf n batch t' stale' live.tail) :=
  Queues.Ring.consume_preserves hb

/-- Every size-zero ring refuses guarded production and consumes nothing,
independently of its other fields. No positive-size premise is imposed. -/
theorem zero_size_ring_no_progress (r : PtrRing α) (hz : r.size = 0) (x : α) :
    r.full = true ∧ r.peek = none ∧ r.consume = (none, r) ∧
      r.count = 0 ∧ r.items = [] ∧ Queues.tryProduce r x = (false, r) :=
  Queues.Ring.zero_size r hz x

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
    (w v : WGWorld) (ambient ambient' : Ambient) (ret : Int)
    (hr : ((enqueuePerDeviceAndPeer pid item).run w).run ambient = .ok ((ret, v), ambient')) :
    Queues.EnqueueResult (Queues.encryptRing w) item ret (Queues.encryptRing v) :=
  Queues.enqueue_ring_result pid item w v ambient ambient' ret hr

/-- An original -EPIPE return means the entry encrypt ring was physically
full and is unchanged at return. Earlier peer-queue and packet-state updates
may have occurred; no ownership or well-formedness premise is imposed. -/
theorem original_enqueue_epipe (pid : PeerId) (item : List SkbId)
    (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeer pid item).run w).run ambient = .ok ((-WG.EPIPE, v), ambient')) :
    Queues.encryptRing v = Queues.encryptRing w ∧
      ∃ r, Queues.encryptRing w = some r ∧ r.full = true :=
  Queues.enqueue_epipe pid item w v ambient ambient' hr

/-- Original enqueue appends after all logically held items, including a
cached peek. It does not itself perform the caller's capacity check. -/
theorem original_prev_enqueue (q : PrevQueue α) (x : α) :
    (q.enqueue x).all = q.all ++ [x] := Queues.prev_enqueue_all q x

/-- Every normal original dequeue removes the first underlying item and
preserves the cached peek and WG state. No queue-validity premise is imposed. -/
theorem original_prev_dequeue (q : PrevQueue α) (w v : WGWorld)
    (ambient ambient' : Ambient) (head : Option α) (q' : PrevQueue α)
    (hr : (q.dequeue.run w).run ambient = .ok (((head, q'), v), ambient')) :
    head = q.items.head? ∧ q'.items = q.items.tail ∧
      q'.peeked = q.peeked ∧ v = w :=
  Queues.prev_dequeue_normal q w v ambient ambient' head q' hr

/-- A normal original peek returns the logical first item and preserves all
logical contents. Its cached result agrees with that item. -/
theorem original_prev_peek (q : PrevQueue α) (w v : WGWorld)
    (ambient ambient' : Ambient) (head : Option α) (q' : PrevQueue α)
    (hr : (q.peek.run w).run ambient = .ok (((head, q'), v), ambient')) :
    head = q.all.head? ∧ q'.all = q.all ∧ q'.peeked = head ∧ v = w :=
  Queues.prev_peek_normal q w v ambient ambient' head q' hr

/-- Peeking a present item and dropping the peek removes exactly the logical
head. This local queue statement does not yet describe original rxPoll. -/
theorem original_prev_peek_drop (q : PrevQueue α) (w v : WGWorld)
    (ambient ambient' : Ambient) (x : α) (q' : PrevQueue α)
    (hr : (q.peek.run w).run ambient = .ok (((some x, q'), v), ambient')) :
    q.all = x :: q'.dropPeeked.all := Queues.prev_peek_then_drop q w v ambient ambient' x q' hr

/-- Structurally coherent queues have ordinary dequeue and peek results. -/
theorem original_prev_total (q : PrevQueue α) (w : WGWorld) (ambient : Ambient)
    (hc : Queues.PrevCoherent q) :
    (∃ head q' v ambient', (q.dequeue.run w).run ambient = .ok (((head, q'), v), ambient')) ∧
    (∃ head q' v ambient', (q.peek.run w).run ambient = .ok (((head, q'), v), ambient')) :=
  ⟨Queues.prev_dequeue_total q w ambient hc, Queues.prev_peek_total q w ambient hc⟩

/-- The malformed nonstub empty queue fails at the original invariant,
unless an existing cached peek avoids the dequeue. -/
theorem original_prev_malformed (q : PrevQueue α) (w : WGWorld) (ambient : Ambient)
    (hp : q.peeked = none) (ht : q.tailIsStub = false) (hi : q.items = []) :
    (q.peek.run w).run ambient = .error (.invariant "prev_queue: a tail item without an entry") :=
  Queues.prev_peek_malformed q w ambient hp ht hi

/-- Complete original reference-acquisition and keypair-release
helpers preserve every peer's full receive queue with its epoch and identity.
These are successful-endpoint frames, not internal access-history claims. -/
theorem original_reference_queue_frames (pid : PeerId) (peer : Option PeerId)
    (kp : Option KeypairId) (now : Bool) :
    Framing.SameView Queues.rxQueues (peerGet pid) ∧
    Framing.SameView Queues.rxQueues (peerGetMaybeZero peer) ∧
    Framing.SameView Queues.rxQueues (keypairGet kp) ∧
    Framing.SameView Queues.rxQueues (keypairPut kp now) :=
  ⟨Queues.peerGet_rxQueues pid, Queues.peerGetMaybeZero_rxQueues peer,
    Queues.keypairGet_rxQueues kp, Queues.keypairPut_rxQueues kp now⟩

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

/-- Original endpoint and receive-timer maintenance preserve every complete
receive queue, its epoch and peer identity on normal return. -/
theorem original_receive_maintenance_queue_frames (pid : PeerId) (endpoint : Endpoint)
    (site : HiddenSite) :
    Framing.SameView Queues.rxQueues (setPeerEndpoint pid endpoint) ∧
    Framing.SameView Queues.rxQueues (timersHandshakeComplete pid site) ∧
    Framing.SameView Queues.rxQueues (timersAnyAuthenticatedPacketReceived pid) ∧
    Framing.SameView Queues.rxQueues (timersDataReceived pid) ∧
    Framing.SameView Queues.rxQueues (timersTraversal pid) :=
  ⟨Queues.setPeerEndpoint_rxQueues pid endpoint,
    Queues.timersHandshakeComplete_rxQueues pid site,
    Queues.timersAnyAuthenticatedPacketReceived_rxQueues pid,
    Queues.timersDataReceived_rxQueues pid, Queues.timersTraversal_rxQueues pid⟩

/-- Complete original staged transmission and receive-side key refresh retain
the exact old receive-queue cell of every post-state resident. They may delete
peers; no reference-ownership premise is added. -/
theorem original_transmit_retains_receive_queues (pid : PeerId) :
    Queues.RetainsRx (sendStagedPackets pid) ∧ Queues.RetainsRx (keepKeyFreshRx pid) :=
  ⟨Queues.sendStagedPackets_rxQueues pid, Queues.keepKeyFreshRx_rxQueues pid⟩

/-- Complete original receive completion retains the exact queue, epoch and
peer identity of every post-state resident. This normal-return projection
does not yet establish poll order, delivery or packet conservation. -/
theorem original_receive_completion_retains_queues (pid : PeerId) (pkt : RxPacket)
    (endpoint : Endpoint) : Queues.RetainsRx (consumeDataDone pid pkt endpoint) :=
  Queues.consumeDataDone_rxQueues pid pkt endpoint

/-- The complete poll's failure-retaining removal observer has exactly the
original result, full success World and Stop for every input and callback. -/
theorem original_poll_removal_erasure (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit) :
    Logged.ErasesPrefix (Queues.rxPollRemovals pid budget callback) (rxPoll pid budget callback) :=
  Queues.rxPollRemovals_erases pid budget callback

/-- The outer poll body removes an initial segment of the current resident's exact
entry queue, in order, even when a later helper or callback stops. Events are
emitted after the original two-getter drop. Repeated entry IDs remain possible;
callback-internal removals are outside this log. Successful batch callbacks
must explicitly retain surviving queues. This theorem does not assert
packet ownership or stack delivery. -/
theorem original_poll_removal_prefix (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit) (w : World) (cell : Queues.RxQueueCell)
    (hcallback : ∀ bytes, Queues.ProductRetainsRx (callback bytes))
    (hc : Queues.rxQueues w.wg pid = some cell) :
    Queues.RemovalPrefix cell.queue.all
      (Logged.runPrefix (Queues.rxPollRemovals pid budget callback) w []).2 :=
  Queues.rxPollRemovals_prefix pid budget callback w cell hcallback hc

/-- At the outer poll's original two-getter drop site, normal completion
appends exactly its one skb ID, while a failed update appends nothing. -/
theorem original_poll_drop_observation (pid : PeerId) (id : SkbId)
    (w : World) (h : List SkbId) :
    Logged.runPrefix (Queues.dropRxPrefix pid id) w h =
      match (liftWG (Queues.dropRxQueue pid)).run w with
      | .error stop => (.error stop, h)
      | .ok (_, v) => (.ok ((), v), h ++ [id]) :=
  Queues.dropRxPrefix_run pid id w h

/-- Tagged GRO buffering and entry observations for the actual stack callback
erase to the complete original poll, including every original World and Stop. -/
theorem original_poll_gro_erasure (pid : PeerId) (budget : Nat) :
    Logged.ErasesPrefix (Queues.rxPollGro pid budget)
      (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) :=
  Queues.rxPollGro_erases pid budget

/-- Only an original completion returning bytes emits a buffered occurrence,
carrying those exact bytes and the caller's explicit ordinal and skb ID.
Keepalives and other none returns emit none; failures retain the old history. -/
theorem original_poll_completion_buffer (pid : PeerId) (occurrence : Nat) (id : SkbId)
    (pkt : RxPacket) (endpoint : Endpoint) (w : World) (h : List Queues.GroEvent) :
    Logged.runPrefix (Queues.consumeGro pid occurrence id pkt endpoint) w h =
      match (liftWG (consumeDataDone pid pkt endpoint)).run w with
      | .error stop => (.error stop, h)
      | .ok (none, v) => (.ok (none, v), h)
      | .ok (some bytes, v) =>
        (.ok (some ⟨occurrence, id, bytes⟩, v), h ++ [.buffered ⟨occurrence, id, bytes⟩]) :=
  Queues.consumeGro_run pid occurrence id pkt endpoint w h

/-- The former `original_poll_callback_prefix` (2c7a076) is false after real
GRO landed in f45bde8; GroSafe retains its chronological meaning. This original
helper equation identifies the cause: a held packet then a normal packet are
passed to the actual callback in reverse order. ReplayGro separately checks an
accepted original runner witness. No universal selected-order or conservation
replacement is claimed by this equation. -/
theorem original_gro_held_then_normal (callback : List (List UInt8) → Leanux.M Unit)
    (held normal : List UInt8) (hh : groTakenAtOnce held = false)
    (hn : groTakenAtOnce normal = true) :
    (do let g ← napiGroReceive callback {} held
        let g ← napiGroReceive callback g normal
        napiGroFlushAll callback g) = callback [normal, held] :=
  Queues.held_then_normal callback held normal hh hn

/-- The actual stack forM visits a prefix of its supplied tagged occurrences;
a failed call retains its own entry event and leaves the suffix unvisited.
A normal callback-list return has no unvisited remainder. -/
theorem original_stack_callback_visited_prefix (entries : List Queues.GroEntry)
    (w : World) (h : List Queues.GroEvent) :
    ∃ visited remaining, entries = visited ++ remaining ∧
      (Logged.runPrefix (Queues.flushGro entries) w h).2 = h ++ visited.map Queues.GroEvent.entered ∧
      (∀ x v, (Logged.runPrefix (Queues.flushGro entries) w h).1 = .ok (x, v) → remaining = []) :=
  Queues.flushGro_prefix entries w h

/-- For one complete original poll's exact observer, callback entries form a
prefix of normal completion offers followed by held offers, preserving each
class's order. This holds for every input World, including every Stop and the
entry of a callback which fails. History starts empty for this poll; the result
does not assert chronological order, completed delivery or source-tag uniqueness. -/
theorem original_poll_selected_callback_prefix (pid : PeerId) (budget : Nat) (w : World) :
    Queues.SelectedGroSafe (Logged.runPrefix (Queues.rxPollGro pid budget) w []).2 :=
  Queues.rxPollGro_selected_prefix pid budget w

/-- If the actual original poll with the concrete stack callback returns
normally, every buffered completion offer has exactly its callback entry in
the selected normal-then-held order, including multiplicity. The premise is
the original run, not observer success or a caller-supplied history invariant.
This is per-poll callback-entry conservation, not completed stack delivery,
receive-queue occurrence provenance or whole-schedule conservation. -/
theorem original_poll_selected_callback_complete (pid : PeerId) (budget : Nat)
    (w v : World) (n : Nat)
    (hr : (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)).run w = .ok (n, v)) :
    Queues.selectedEntries (Queues.bufferedEntries
      (Logged.runPrefix (Queues.rxPollGro pid budget) w []).2) =
      Queues.enteredEntries (Logged.runPrefix (Queues.rxPollGro pid budget) w []).2 :=
  Queues.rxPollGro_selected_complete pid budget w v n hr

/-- In one poll starting with empty observation history, every buffered
completion's exact ordinal/skb tag is a subsequence occurrence of an outer
queue removal. Buffered ordinals are distinct even on failure, including a
second held offer rejected by GRO. Repeated skb IDs remain possible; these
local ordinals are neither allocation identities nor completed deliveries. -/
theorem original_poll_buffered_tag_provenance (pid : PeerId) (budget : Nat) (w : World) :
    let h := (Logged.runPrefix (Queues.rxPollGro pid budget) w []).2
    (Queues.bufferedTags h).Sublist (Queues.removedTags h) ∧
      ((Queues.bufferedEntries h).map Queues.GroEntry.occurrence).Nodup := by
  have hs := Queues.rxPollGro_tags_properties pid budget w
  exact ⟨hs.1, hs.2.2⟩

/-- Successful outer drops receive consecutive local ordinals starting at
zero, even if the poll later stops before incrementing its local workDone.
This all-input statement counts observed drops, not successful delivery. -/
theorem original_poll_removal_ordinals (pid : PeerId) (budget : Nat) (w : World) :
    let h := (Logged.runPrefix (Queues.rxPollGro pid budget) w []).2
    (Queues.removedTags h).map Prod.fst = List.range (Queues.removedTags h).length :=
  (Queues.rxPollGro_tags_properties pid budget w).2.1

/-- The two existing complete-poll observers have exactly the same result,
full successful World and Stop, and their outer-removal logs agree after
discarding tag ordinals and non-removal events. This includes every actual
GRO callback and its failures, with no queue-retention or input-state premise. -/
theorem original_poll_removal_projection (pid : PeerId) (budget : Nat) (w : World) :
    Logged.runPrefix (Queues.rxPollRemovals pid budget
      (fun bytes => bytes.forM Leanux.Env.deliverInner)) w [] =
      ((Logged.runPrefix (Queues.rxPollGro pid budget) w []).1,
       (Queues.removedTags (Logged.runPrefix (Queues.rxPollGro pid budget) w []).2).map Prod.snd) :=
  Queues.rxPollGro_removals_agree pid budget w

/-- Every normal return of the actual packet-list stack callback retains
the exact receive queue, epoch and peer identity of every surviving resident.
IPv4 TCP replies may re-enter transmit and delete peers during cleanup; this
contract permits deletion and requires no packet-validity or ownership premise. -/
theorem original_stack_callback_retains_receive_queues (packets : List (List UInt8)) :
    Queues.ProductRetainsRx (packets.forM Leanux.Env.deliverInner) :=
  Queues.stackForM_rxQueues packets

/-- With the concrete stack callback, outer removals are a prefix of the
initial resident's exact entry queue for every normal or stopped poll.
The initial cell identifies that queue; no callback frame, live-peer or
packet-ID-validity assumption is required from the caller. -/
theorem original_poll_concrete_removal_prefix (pid : PeerId) (budget : Nat)
    (w : World) (cell : Queues.RxQueueCell) (hc : Queues.rxQueues w.wg pid = some cell) :
    Queues.RemovalPrefix cell.queue.all
      ((Queues.removedTags (Logged.runPrefix (Queues.rxPollGro pid budget) w []).2).map Prod.snd) :=
  Queues.rxPollGro_entry_prefix pid budget w cell hc

/-- Callback entries within one poll have distinct local ordinals, and each
is an exact buffered completion entry whose ordinal/skb tag came from an outer
queue removal. This includes entry into a failing callback, on arbitrary
Worlds and Stops. It asserts neither completed delivery, allocation identity,
chronological callback order nor uniqueness across separate polls. -/
theorem original_poll_callback_occurrence_provenance (pid : PeerId) (budget : Nat) (w : World) :
    let h := (Logged.runPrefix (Queues.rxPollGro pid budget) w []).2
    ((Queues.enteredEntries h).map Queues.GroEntry.occurrence).Nodup ∧
      ∀ e ∈ Queues.enteredEntries h,
        e ∈ Queues.bufferedEntries h ∧ (e.occurrence, e.skb) ∈ Queues.removedTags h :=
  Queues.rxPollGro_callback_provenance pid budget w

/-- Buffered completion skb occurrences form a subsequence of the initial
resident's exact entry queue under the actual stack callback, even if the poll
stops. Repeated skb IDs remain possible; GRO may later select callback entries
in another order. This is an occurrence/order statement, not no-loss delivery. -/
theorem original_poll_buffered_entry_subsequence (pid : PeerId) (budget : Nat)
    (w : World) (cell : Queues.RxQueueCell) (hc : Queues.rxQueues w.wg pid = some cell) :
    ((Queues.bufferedEntries (Logged.runPrefix (Queues.rxPollGro pid budget) w []).2).map
      Queues.GroEntry.skb).Sublist cell.queue.all :=
  Queues.rxPollGro_buffered_sublist pid budget w cell hc

/-- Every finite sequence of guarded offers and polls preserves the exact
physical representation and both conservation equations. The entry invariant
is explicit; batch is arbitrary, including zero and values above size. -/
theorem original_ring_journal_preserves (n batch : Nat)
    (h : List (Queues.Ring.Journal.Event α)) (r : PtrRing α)
    (cs : List (Queues.Ring.Journal.Command α))
    (hi : Queues.Ring.Journal.Inv n batch h r) :
    Queues.Ring.Journal.Inv n batch
      (h ++ (Queues.Ring.Journal.run r cs).1) (Queues.Ring.Journal.run r cs).2 :=
  Queues.Ring.Journal.run_inv hi cs

/-- Starting from the original initializer, admissions are exactly consumed
occurrences followed by live items, for every size. Positive size additionally
retains a physical retired/stale/live witness at the initializer's actual batch.
This is a finite pure ring journal, not whole-pipeline or eventual delivery. -/
theorem original_initialized_ring_journal_conservation (n : Nat)
    (cs : List (Queues.Ring.Journal.Command α)) :
    let out := Queues.Ring.Journal.run (PtrRing.init n) cs
    Queues.Ring.Journal.admitted out.1 = Queues.Ring.Journal.consumed out.1 ++ out.2.items ∧
      (0 < n → Queues.Ring.Journal.Inv n (PtrRing.init (α := α) n).batch out.1 out.2) :=
  ⟨Queues.Ring.Journal.conservation_all n cs, fun hn => Queues.Ring.Journal.initialized hn cs⟩

/-- A zero-size ring refuses every offer and returns none for every poll,
recording every outcome and preserving the complete arbitrary starting ring. -/
theorem original_zero_size_ring_journal (r : PtrRing α) (hz : r.size = 0)
    (cs : List (Queues.Ring.Journal.Command α)) :
    Queues.Ring.Journal.run r cs = (cs.map Queues.Ring.Journal.zeroEvent, r) :=
  Queues.Ring.Journal.run_zero r hz cs

/-- Forgetting occurrence ordinals preserves all original guarded offer and
consume outcomes and the full physical ring. This erasure holds on arbitrary
starting rings; no freshness or injectivity is assumed for their contents. -/
theorem original_tagged_ring_journal_erasure (r : PtrRing (Nat × α)) (next : Nat)
    (cs : List (Queues.Ring.Journal.Command α)) :
    Queues.Ring.Journal.run (Queues.Ring.mapRing Prod.snd r) cs =
      ((Queues.Ring.Journal.run r (Queues.Ring.Journal.tagCommands next cs)).1.map
        (Queues.Ring.Journal.Event.map Prod.snd),
       Queues.Ring.mapRing Prod.snd
        (Queues.Ring.Journal.run r (Queues.Ring.Journal.tagCommands next cs)).2) :=
  Queues.Ring.Journal.tagged_erasure r next cs

/-- Every offer receives the next ordinal, including refusals. From an empty
initialized ring, consumed and live occurrences partition admissions and their
joint ordinal list is duplicate-free. Payload duplication remains unrestricted;
these tags are local journal occurrences, not allocation identities. -/
theorem original_tagged_ring_journal_occurrences (n next : Nat)
    (cs : List (Queues.Ring.Journal.Command α)) :
    let out := Queues.Ring.Journal.run (PtrRing.init n) (Queues.Ring.Journal.tagCommands next cs)
    (Queues.Ring.Journal.offered out.1).map Prod.fst =
        List.range' next (Queues.Ring.Journal.inputs cs).length ∧
      Queues.Ring.Journal.admitted out.1 = Queues.Ring.Journal.consumed out.1 ++ out.2.items ∧
      ((Queues.Ring.Journal.consumed out.1 ++ out.2.items).map Prod.fst).Nodup :=
  ⟨Queues.Ring.Journal.tagged_offers (PtrRing.init n) next cs,
    Queues.Ring.Journal.tagged_conservation n next cs⟩

/-- Original TX enqueue returning zero independently establishes that its
entry physical ring existed and was not full. EnqueueResult remains unchanged.
No admitted event is inferred from a guard followed by a queue-work Stop. -/
theorem original_tx_admission_not_full (pid : PeerId) (item : List SkbId)
    (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeer pid item).run w).run ambient = .ok ((0, v), ambient')) :
    ∃ r, Queues.encryptRing w = some r ∧ r.full = false :=
  Queues.enqueue_success_free pid item w v ambient ambient' hr

/-- The same independent successful-admission guard for original RX enqueue,
without queue geometry, ownership or packet-ID validity assumptions. -/
theorem original_rx_admission_not_full (id : SkbId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((enqueuePerDeviceAndPeerRx id).run w).run ambient = .ok ((0, v), ambient')) :
    ∃ r, Queues.decryptRing w = some r ∧ r.full = false :=
  Queues.enqueue_rx_success_free id w v ambient ambient' hr

/-- The complete original RX enqueue and consumeData retain their exact
result, World on success and Stop on failure, for every input and history.
The ring log records admission/refusal only at the corresponding source cut. -/
theorem original_rx_ring_entry_erasure (id : SkbId) (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Logged.ErasesPrefix (Queues.RxRing.enqueue id) (liftWG (enqueuePerDeviceAndPeerRx id)) ∧
      Logged.ErasesPrefix (Queues.RxRing.consume msg src ds) (liftWG (consumeData msg src ds)) :=
  ⟨Queues.RxRing.enqueue_erases id, Queues.RxRing.consume_erases msg src ds⟩

/-- Every reached RX entry prefix refines original finite ring operations.
The actual full device-index/ring cell is linked only on normal return;
ENOSPC and pre-install Stops emit no offer, while EPIPE records a refusal. -/
theorem original_rx_ring_entry_prefix_refinement (deviceIndex : Nat) (initial : PtrRing SkbId)
    (id : SkbId) (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex initial) (Queues.RxRing.Safe initial)
      (Queues.RxRing.enqueue id) ∧
    Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex initial) (Queues.RxRing.Safe initial)
      (Queues.RxRing.consume msg src ds) :=
  ⟨Queues.RxRing.enqueue_preserves id, Queues.RxRing.consume_preserves msg src ds⟩

/-- Original decrypt step/iteration erasure is unconditional on World and
queue validity; the explicitly supplied observers must erase their callbacks.
Softirq runs before the ring read, and every original later Stop is preserved. -/
theorem original_decrypt_ring_worker_erasure
    (hs : Logged.ErasesPrefix softirq originalSoftirq)
    (hi : Logged.ErasesPrefix irq originalIrq)
    (hr : Logged.ErasesPrefix resched originalResched) :
    Logged.ErasesPrefix (Queues.RxRing.step softirq irq) (decryptStep originalSoftirq originalIrq) ∧
    Logged.ErasesPrefix (Queues.RxRing.iter softirq irq resched)
      (decryptIter originalSoftirq originalIrq originalResched) :=
  ⟨Queues.RxRing.step_erases hs hi, Queues.RxRing.iter_erases hs hi hr⟩

/-- Callback preservation allows their own refined ring operations. The poll
is recorded after installed consumption and before packet lookup/decryption;
a later Stop keeps the reached log without asserting a failed World. -/
theorem original_decrypt_ring_worker_prefix_refinement
    (hs : Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex initial) (Queues.RxRing.Safe initial) softirq)
    (hi : Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex initial) (Queues.RxRing.Safe initial) irq)
    (hr : Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex initial) (Queues.RxRing.Safe initial) resched) :
    Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex initial) (Queues.RxRing.Safe initial)
      (Queues.RxRing.step softirq irq) ∧
    Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex initial) (Queues.RxRing.Safe initial)
      (Queues.RxRing.iter softirq irq resched) :=
  ⟨Queues.RxRing.step_preserves hs hi, Queues.RxRing.iter_preserves hs hi hr⟩

/-- From an initialized physical ring, each of the four observed source calls
has admission/consumed/live conservation and an erased ordinal refinement with
joint consumed/live ordinal uniqueness, including size zero. Positive size
also retains retired/stale physical conservation. Only successful completion
links the replay endpoint to the actual returned device-index/ring cell.
Callback contracts are explicit; no saved-packet ownership, lifecycle-reset
identity, real scheduler closure or eventual delivery is asserted. -/
theorem original_rx_ring_initialized_conservation (c : Queues.RxRing.Call α)
    (hs : Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex (PtrRing.init n))
      (Queues.RxRing.Safe (PtrRing.init n)) softirq)
    (hi : Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex (PtrRing.init n))
      (Queues.RxRing.Safe (PtrRing.init n)) irq)
    (hr : Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex (PtrRing.init n))
      (Queues.RxRing.Safe (PtrRing.init n)) resched)
    (hc : Queues.RxRing.cell w = some (deviceIndex, PtrRing.init n)) :
    let out := Logged.runPrefix (c.observe softirq irq resched) w []
    ∃ r, Queues.RxRing.Initialized n out.2 r ∧
      match out.1 with
      | .error _ => True
      | .ok (_, v) => Queues.RxRing.cell v = some (deviceIndex, r) :=
  c.initialized hs hi hr hc

/-- Complete original TX enqueue/createData erasure preserves every result,
successful World and exact Stop, with no queue or packet validity premise. -/
theorem original_tx_ring_entry_erasure (pid : PeerId) (item : List SkbId) :
    Logged.ErasesPrefix (Queues.TxRing.enqueue pid item) (liftWG (enqueuePerDeviceAndPeer pid item)) ∧
      Logged.ErasesPrefix (Queues.TxRing.create pid item) (liftWG (createData pid item)) :=
  ⟨Queues.TxRing.enqueue_erases pid item, Queues.TxRing.create_erases pid item⟩

/-- TX admission/refusal events refine original finite ring operations.
The full device-index/ring cell is linked on normal return; later createData
Stops retain prior events. ENOSPC and pre-install queue-work Stops emit none. -/
theorem original_tx_ring_entry_prefix_refinement (deviceIndex : Nat)
    (initial : PtrRing (List SkbId)) (pid : PeerId) (item : List SkbId) :
    Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex initial) (Queues.TxRing.Safe initial)
      (Queues.TxRing.enqueue pid item) ∧
    Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex initial) (Queues.TxRing.Safe initial)
      (Queues.TxRing.create pid item) :=
  ⟨Queues.TxRing.enqueue_preserves pid item, Queues.TxRing.create_preserves pid item⟩

/-- Encryption and its complete step/iteration preserve exact original
behavior for arbitrary Worlds and callback implementations. The ring is consumed
and installed before softirq; checksum remains between its original guards and later reads. -/
theorem original_encrypt_ring_worker_erasure
    (hc : ∀ p, Logged.ErasesPrefix (checksum p) (originalChecksum p))
    (hs : Logged.ErasesPrefix softirq originalSoftirq)
    (hr : Logged.ErasesPrefix resched originalResched) (kp : KeypairId) (pkt : DataPacket) :
    Logged.ErasesPrefix (Queues.TxRing.packet checksum kp pkt) (encryptPacket originalChecksum kp pkt) ∧
    Logged.ErasesPrefix (Queues.TxRing.step checksum softirq) (encryptStep originalChecksum originalSoftirq) ∧
    Logged.ErasesPrefix (Queues.TxRing.iter checksum softirq resched)
      (encryptIter originalChecksum originalSoftirq originalResched) :=
  ⟨Queues.TxRing.packet_erases hc kp pkt, Queues.TxRing.step_erases hc hs,
    Queues.TxRing.iter_erases hc hs hr⟩

/-- Each consumed whole-list occurrence is recorded after installation and
before malformed-list, packet lookup, encryption or publication Stops. Explicit
callback contracts allow further ring mutations with their own journal events;
no NAPI/stack callback is silently assumed to preserve the entry ring. -/
theorem original_encrypt_ring_worker_prefix_refinement
    (hc : ∀ p, Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex initial)
      (Queues.TxRing.Safe initial) (checksum p))
    (hs : Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex initial) (Queues.TxRing.Safe initial) softirq)
    (hr : Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex initial) (Queues.TxRing.Safe initial) resched)
    (kp : KeypairId) (pkt : DataPacket) :
    Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex initial) (Queues.TxRing.Safe initial)
      (Queues.TxRing.packet checksum kp pkt) ∧
    Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex initial) (Queues.TxRing.Safe initial)
      (Queues.TxRing.step checksum softirq) ∧
    Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex initial) (Queues.TxRing.Safe initial)
      (Queues.TxRing.iter checksum softirq resched) :=
  ⟨Queues.TxRing.packet_preserves hc kp pkt, Queues.TxRing.step_preserves hc hs,
    Queues.TxRing.iter_preserves hc hs hr⟩

/-- Initialized conservation and fresh offer ordinals apply to occurrences of
whole TX ring batches, permitting duplicate/empty payload lists. Positive size
retains retired/stale physical contents, and size zero is covered. A Stop yields
an existential replay ring, without a failed World. Only successful completion
links the endpoint to the actual cell. This is neither constituent-packet
uniqueness nor lifecycle, peer-queue or concrete scheduler closure. -/
theorem original_tx_ring_initialized_conservation (c : Queues.TxRing.Call α)
    (hc : ∀ p, Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex (PtrRing.init n))
      (Queues.TxRing.Safe (PtrRing.init n)) (checksum p))
    (hs : Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex (PtrRing.init n))
      (Queues.TxRing.Safe (PtrRing.init n)) softirq)
    (hr : Logged.PrefixPreserves (Queues.TxRing.Inv deviceIndex (PtrRing.init n))
      (Queues.TxRing.Safe (PtrRing.init n)) resched)
    (hw : Queues.TxRing.cell w = some (deviceIndex, PtrRing.init n)) :
    let out := Logged.runPrefix (c.observe checksum softirq resched) w []
    ∃ r, Queues.TxRing.Initialized n out.2 r ∧
      match out.1 with
      | .error _ => True
      | .ok (_, v) => Queues.TxRing.cell v = some (deviceIndex, r) :=
  c.initialized hc hs hr hw

/-- Concrete NAPI/IRQ and non-decrypt activations retain the complete RX ring
cell on normal return. Non-decrypt work includes actual cryptAhead, stack/TX
callbacks and handshake receive. These frames assert no failed World. -/
theorem original_rx_scheduler_callback_frames :
    Framing.SameView Queues.RxRing.cell Leanux.Env.napiSoftirq ∧
    Framing.SameView Queues.RxRing.cell Leanux.Env.napiIrqExit ∧
    ∀ a : Activation, a.worker ≠ .decryptWorker →
      Framing.SameView Queues.RxRing.cell (Leanux.Env.Activation.iter a) :=
  ⟨Queues.RxRing.napiSoftirq_cell, Queues.RxRing.napiIrqExit_cell, Queues.RxRing.otherIter_cell⟩

/-- ConsumeData and original scheduler iteration/run/dispatch/schedule/nested
rescheduling have unconditional result/World/Stop erasure. This includes eager
pending-NAPI reads, cryptAhead, ambiguity and record/occupancy-bound failures. -/
theorem original_rx_scheduler_erasure (c : Queues.RxRing.SchedulerCall α) :
    Logged.ErasesPrefix c.observe c.original := c.erases

/-- All actual callbacks are discharged for this RX-ring invariant. Reached
committed prefixes refine finite original ring executions, including Stops;
normal returns additionally identify the physical ring. This is a scheduler
call contract, not a packet-carrier or enclosing runner theorem. -/
theorem original_rx_scheduler_prefix_refinement (c : Queues.RxRing.SchedulerCall α) :
    Logged.PrefixPreserves (Queues.RxRing.Inv deviceIndex initial)
      (Queues.RxRing.Safe initial) c.observe := c.preserves

/-- A prior initialized journal may already describe a nonempty current ring.
The concrete scheduler extends its conservation and ordinal refinement, with
no duplicate-skb restriction. Failed outcomes have only a replay endpoint;
normal outcomes link it to the actual device-index/ring cell. -/
theorem original_rx_scheduler_initialized_conservation (c : Queues.RxRing.SchedulerCall α)
    (hi : Queues.RxRing.Inv deviceIndex (PtrRing.init n) h w) :
    let out := Logged.runPrefix c.observe w h
    ∃ r, Queues.RxRing.Initialized n out.2 r ∧
      match out.1 with
      | .error _ => True
      | .ok (_, v) => Queues.RxRing.cell v = some (deviceIndex, r) := c.initialized hi

/-- Original copied-world trials retain the caller history, discard their
Worlds, and reproduce ordered filter decisions including hidden rejection and
the first non-hidden Stop. These equations hold without an invariant premise. -/
theorem original_rx_consistency_trials (a : Activation) (xs : List Activation)
    (w : World) (h : List Queues.RxRing.Event) :
    Logged.runPrefix (Logged.liftPrefix (Leanux.Env.Activation.consistent a) : Queues.RxRing.Obs Bool) w h =
      ((match (Logged.runPrefix (Queues.RxRing.activationRun a) w h).1 with
        | .ok _ => .ok (true, w)
        | .error (.hidden _) => .ok (false, w)
        | .error e => .error e), h) ∧
    (xs.filterM Leanux.Env.Activation.consistent).run w =
      (xs.filterM (fun a => Queues.RxRing.trialDecision a w h)).map (fun ys => (ys, w)) :=
  ⟨Queues.RxRing.activationConsistent_trial a w h, Queues.RxRing.trials_filter xs w h⟩

/-- Every candidate has a separately conserved reached trial prefix, even if
it would reject or Stop. This certifies potentially evaluated candidates; it
neither commits their events nor asserts that every listed candidate ran. -/
theorem original_rx_consistency_trial_conservation (xs : List Activation) (w : World)
    (h : List Queues.RxRing.Event) (hi : Queues.RxRing.Inv deviceIndex (PtrRing.init n) h w) :
    ∀ a ∈ xs, ∃ r, Queues.RxRing.Initialized n
      (Logged.runPrefix (Queues.RxRing.activationRun a) w h).2 r :=
  Queues.RxRing.trials_initialized xs w h hi

/-- The adjacent original lookupSrc/peerPut cut returns the lookup's actual
result and restores the outside-peer WG stores and all complete peer records.
A Some result derives a positive pre-acquisition count in Borrowed. No initial
liveness, represented-trie or ownership premise is required. This is normal
partial correctness, not a total-repayment theorem. -/
theorem original_lookup_source_reference_restoration (protocol : Nat) (bytes : List UInt8)
    (w v : WGWorld) (ambient ambient' : Ambient) (result : Option PeerId)
    (hr : ((Queues.RxBorrow.source protocol bytes).run w).run ambient = .ok ((result, v), ambient')) :
    ∃ acquired acquiredAmbient, ((lookupSrc protocol bytes).run w).run ambient =
      .ok ((result, acquired), acquiredAmbient) ∧
      Framing.PeerBorrow.Borrowed (Framing.wgStoreView w) result (Framing.wgStoreView acquired) ∧
      Framing.PeerBorrow.view v = Framing.PeerBorrow.view w :=
  Queues.RxBorrow.repayLookup_normal _ (Queues.RxBorrow.lookupSrc_spec protocol bytes)
    w v ambient ambient' result hr

/-- The existing lookup/acquisition/release observers compose with exact
result, full successful World and Stop erasure on all inputs. -/
theorem original_lookup_repayment_access_erasure (protocol : Nat) (bytes : List UInt8) :
    Logged.ErasesStatePrefix (Queues.RxBorrow.observed protocol bytes)
      (Queues.RxBorrow.source protocol bytes) := Queues.RxBorrow.observed_erases protocol bytes

/-- Real accesses preceding any Stop remain in the safe history under the
existing concrete allocation invariant; no failed World is manufactured. -/
theorem original_lookup_repayment_allocation_access_preserves (protocol : Nat) (bytes : List UInt8) :
    Logged.StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Queues.RxBorrow.observed protocol bytes) := Queues.RxBorrow.observed_preserves protocol bytes

/-- Normal repayment retains exact RX queues, resident NAPI flags and all
three key slots. It also preserves bounded slot affiliation if already true;
affiliation initialization and the remaining pipeline are separate obligations. -/
theorem original_lookup_repayment_carrier_projections (protocol : Nat) (bytes : List UInt8) :
    Framing.SameView Queues.rxQueues (Queues.RxBorrow.source protocol bytes) ∧
    (∀ pid, Framing.SameView (fun w => (Framing.PeerBorrow.resident (Framing.wgStoreView w) pid).map fun p =>
      (p.napiScheduled, p.keypairCurrent, p.keypairPrevious, p.keypairNext))
      (Queues.RxBorrow.source protocol bytes)) ∧
    Framing.SameView Queues.RxBorrow.SlotAffiliation (Queues.RxBorrow.source protocol bytes) :=
  ⟨Queues.RxBorrow.source_queues protocol bytes,
    Queues.RxBorrow.source_peer_fields protocol bytes, Queues.RxBorrow.source_affiliation protocol bytes⟩

/-- The joint admission, publication, createData and TX-step observations erase
on every input, preserving the complete original result, World and Stop. -/
theorem original_tx_disposition_erasure (pid : PeerId) (item : List SkbId) (state : PacketState) :
    Logged.ErasesPrefix (Queues.TxDisposition.enqueue pid item) (liftWG (enqueuePerDeviceAndPeer pid item)) ∧
    Logged.ErasesPrefix (Queues.TxDisposition.publish item state) (liftWG (enqueuePerPeerTx item state)) ∧
    Logged.ErasesPrefix (Queues.TxDisposition.create pid item) (liftWG (createData pid item)) ∧
    Logged.ErasesPrefix (Queues.TxDisposition.step pid) (liftWG (txStep pid)) :=
  ⟨Queues.TxDisposition.enqueue_erases pid item, Queues.TxDisposition.publish_erases item state,
    Queues.TxDisposition.create_erases pid item, Queues.TxDisposition.step_erases pid⟩

/-- Direct history correspondence, stronger than separate erasures. createData's
access/ring projections are unconditional; full-step access projection uses the
existing AllocationInv at entry and concretely discharged intermediate contracts. -/
theorem original_tx_disposition_projections (pid : PeerId) (item : List SkbId) :
    Logged.ProjectsPrefix Queues.TxDisposition.accessEvent id
      (Queues.TxDisposition.create pid item) (Logged.liftWGObserver (Lifetimes.createDataPrefix pid item)) ∧
    Logged.ProjectsPrefix Queues.TxDisposition.ringEvent id
      (Queues.TxDisposition.create pid item) (Queues.TxRing.create pid item) ∧
    Logged.ProjectsUnder (fun h w => Lifetimes.AllocationInv h w.wg) Queues.TxDisposition.accessEvent
      (Queues.TxDisposition.step pid) (Logged.liftWGObserver (Lifetimes.txStepPrefix pid)) :=
  ⟨Queues.TxDisposition.create_access pid item, Queues.TxDisposition.create_ring pid item,
    Queues.TxDisposition.step_access pid⟩

/-- Reached-prefix access safety and the existing ring refinement transport
through the direct projections. A Stop has no retained World. -/
theorem original_tx_disposition_prefix_refinement (pid : PeerId) (item : List SkbId)
    (w : World) (h : List Queues.TxDisposition.Event)
    (ha : Lifetimes.AllocationInv (h.filterMap Queues.TxDisposition.accessEvent) w.wg)
    (hr : Queues.TxRing.Inv deviceIndex initial (h.filterMap Queues.TxDisposition.ringEvent) w) :
    (Lifetimes.LifetimeEvent.Safe
      ((Logged.runPrefix (Queues.TxDisposition.create pid item) w h).2.filterMap Queues.TxDisposition.accessEvent) ∧
      match (Logged.runPrefix (Queues.TxDisposition.create pid item) w h).1 with
      | .error _ => True
      | .ok (_, v) => Lifetimes.AllocationInv
          ((Logged.runPrefix (Queues.TxDisposition.create pid item) w h).2.filterMap Queues.TxDisposition.accessEvent) v.wg) ∧
    (Lifetimes.LifetimeEvent.Safe
      ((Logged.runPrefix (Queues.TxDisposition.step pid) w h).2.filterMap Queues.TxDisposition.accessEvent) ∧
      match (Logged.runPrefix (Queues.TxDisposition.step pid) w h).1 with
      | .error _ => True
      | .ok (_, v) => Lifetimes.AllocationInv
          ((Logged.runPrefix (Queues.TxDisposition.step pid) w h).2.filterMap Queues.TxDisposition.accessEvent) v.wg) ∧
    (Queues.TxRing.Safe initial
      ((Logged.runPrefix (Queues.TxDisposition.create pid item) w h).2.filterMap Queues.TxDisposition.ringEvent) ∧
      match (Logged.runPrefix (Queues.TxDisposition.create pid item) w h).1 with
      | .error _ => True
      | .ok (_, v) => Queues.TxRing.Inv deviceIndex initial
          ((Logged.runPrefix (Queues.TxDisposition.create pid item) w h).2.filterMap Queues.TxDisposition.ringEvent) v) :=
by
  have hc := (Queues.TxDisposition.create_access pid item).under.preserves
      (Lifetimes.createDataPrefix_preserves_ambient Lifetimes.allocationAmbient Lifetimes.allocationTx pid item).liftWGObserver w h ha
  have hs := (Queues.TxDisposition.step_access pid).preserves
      (Lifetimes.txStepPrefix_preserves_ambient Lifetimes.allocationAmbient Lifetimes.allocationTx Lifetimes.allocationSocket pid).liftWGObserver w h ha
  have hj := (Queues.TxDisposition.create_ring pid item).under.preserves (Queues.TxRing.create_preserves pid item) w h hr
  constructor
  · cases he : (Logged.runPrefix (Queues.TxDisposition.create pid item) w h).1 <;> simpa only [he] using hc
  constructor
  · cases he : (Logged.runPrefix (Queues.TxDisposition.step pid) w h).1 <;> simpa only [he] using hs
  · cases he : (Logged.runPrefix (Queues.TxDisposition.create pid item) w h).1 <;> simpa only [he] using hj

/-- Exact original continuations: EPIPE returns, ENOSPC enters direct cleanup,
and a reached DEAD head skips completion before disposal. These are local cuts,
not full queue-retention or store-absence endpoints. -/
theorem original_tx_disposition_continuations (pid : PeerId) (item : List SkbId)
    (first : SkbId) (head : DataPacket) (hd : head.state = .dead) :
    Queues.TxDisposition.createTail pid item first (-WG.EPIPE) = (do
      _ ← Logged.liftPrefix (branch .createDataOk false)
      _ ← Logged.liftPrefix (branch .createDataOkEpipe true)
      pure ()) ∧
    Queues.TxDisposition.createTail pid item first (-WG.ENOSPC) = (do
      _ ← Logged.liftPrefix (branch .createDataOk false)
      _ ← Logged.liftPrefix (branch .createDataOkEpipe false)
      Queues.TxDisposition.cleanup pid item first) ∧
    Queues.TxDisposition.afterHead pid item head = (do
      Queues.TxDisposition.drop pid item
      _ ← Logged.liftPrefix (branch .txCrypted false)
      Queues.TxDisposition.dispose pid item head.keypair) ∧
    Logged.HistoryFrame Queues.TxDisposition.completionEvent (Queues.TxDisposition.afterHead pid item head) :=
  ⟨Queues.TxDisposition.epipe_tail pid item first, Queues.TxDisposition.enospc_tail pid item first,
    Queues.TxDisposition.dead_afterHead pid item head hd, Queues.TxDisposition.dead_no_completion pid item head hd⟩

/-- Exact release observation and normal no-send disposal. Subsequent getter or
put failure retains the reached prefix but supplies no final World. -/
theorem original_tx_disposition_release_cut (pid : PeerId) (item : List SkbId) (key : KeypairId)
    (id : SkbId) (w : World) (h : List Queues.TxDisposition.Event) :
    Logged.runPrefix (Queues.TxDisposition.nativeAccess (Lifetimes.freeTxSkbPrefix id)) w h =
      (match (liftWG (getTxSkb id)).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((liftWG (freeTxSkb id)).run w,
          h ++ [.access (.packet (.read (.inl id) (Lifetimes.packetStamp w.wg id))),
                .access (.packet (.release (.inl id) (Lifetimes.packetStamp w.wg id)))])) ∧
    Framing.SameView (fun w : WGWorld => w.sent) (Queues.TxDisposition.disposeSource pid item key) :=
  ⟨Queues.TxDisposition.free_run id w h, Queues.TxDisposition.dispose_no_send pid item key⟩

/-- Strict peerGet derives positivity from its original normal return. Immediate
repayment restores the WG store view; intervening publication is not covered. -/
theorem original_tx_strict_reference_cut (pid : PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((peerGet pid).run w).run ambient = .ok (((), v), ambient')) :
    Framing.PeerBorrow.Borrowed (Framing.wgStoreView w) (some pid) (Framing.wgStoreView v) ∧
    Framing.SameView Framing.PeerBorrow.view (do peerGet pid; peerPut (some pid)) :=
  ⟨(Framing.hoare_iff_run_ambient _ _ _).mp
      (Framing.PeerBorrow.strict_acquire_spec pid (Framing.wgStoreView w))
      w ambient () v ambient' rfl hr,
    Framing.PeerBorrow.strict_repaid pid⟩

/-- The actual publication borrow spans CPU/work-queue updates. Every peer's
full TX queue is retained on normal return; publication's keypair-derived peer
need not equal the original enqueue caller. Stops have only the existing prefix. -/
theorem original_tx_publication_retains_queues (item : List SkbId) (state : PacketState) :
    Framing.SameView Queues.TxDisposition.txQueues (enqueuePerPeerTx item state) :=
  Queues.TxDisposition.publication_queues item state

/-- The original ring-refusal createData path retains the newly enqueued item,
marks its actual head DEAD and leaves the physical encrypt ring unchanged. The
entry guards are source conditions; normal return is explicit, not guaranteed. -/
theorem original_create_data_epipe_endpoint (pid : PeerId) (first : SkbId) (rest : List SkbId)
    (d : Device) (p : Peer) (w v : WGWorld) (ambient ambient' : Ambient) (hd : w.dev = some d)
    (hp : d.peers[pid]? = some p) (hl : p.isDead = false)
    (hq : p.txQueue.count < MAX_QUEUED_PACKETS) (hf : d.encryptQueue.full = true)
    (hr : ((createData pid (first :: rest)).run w).run ambient = .ok (((), v), ambient')) :
    Queues.TxDisposition.txQueues v pid = some (p.txQueue.enqueue (first :: rest)) ∧
    Queues.TxDisposition.HeadState first .dead v ∧
    Queues.TxRing.nativeCell v = some (d.ifindex, d.encryptQueue) :=
  (Framing.hoare_iff_run_ambient _ _ _).mp
    (Queues.TxDisposition.create_pipe pid first rest d p hp hl hq hf) w ambient () v ambient' hd hr

/-- Actual peer-queue refusal and normal cleanup remove every supplied packet
slot. The preceding key/peer puts may Stop; peer-queue retention is not claimed. -/
theorem original_create_data_enospc_endpoint (pid : PeerId) (item : List SkbId)
    (p : Peer) (w v : WGWorld) (ambient ambient' : Ambient) (hp : Framing.PeerBorrow.resident (Framing.wgStoreView w) pid = some p)
    (hl : p.isDead = false) (hq : MAX_QUEUED_PACKETS ≤ p.txQueue.count)
    (hr : ((createData pid item).run w).run ambient = .ok (((), v), ambient')) :
    ∀ id ∈ item, Queues.TxDisposition.txPackets v id = none :=
  (Framing.hoare_iff_run_ambient _ _ _).mp
    (Queues.TxDisposition.create_noSpace pid item p.txQueue hq)
      w ambient () v ambient' ⟨p, hp, hl, rfl⟩ hr

/-- Complete original txStep on its actual logical DEAD head frees the whole
item without adding socket output. This is a local step contract, not a proof
that every previous EPIPE reaches this state under an arbitrary schedule. -/
theorem original_dead_tx_step_disposal (pid : PeerId) (first : SkbId) (rest : List SkbId)
    (p : Peer) (w v : WGWorld) (ambient ambient' : Ambient) (result : Bool)
    (hp : Framing.PeerBorrow.resident (Framing.wgStoreView w) pid = some p)
    (hq : p.txQueue.all.head? = some (first :: rest))
    (hd : Queues.TxDisposition.HeadState first .dead w)
    (hr : ((txStep pid).run w).run ambient = .ok ((result, v), ambient')) :
    result = true ∧ (∀ id ∈ first :: rest, Queues.TxDisposition.txPackets v id = none) ∧
      v.sent = w.sent :=
  (Framing.hoare_iff_run_ambient _ _ _).mp
    (Queues.TxDisposition.dead_step_endpoint pid first rest w.sent)
      w ambient result v ambient' ⟨⟨p, hp, hq⟩, hd, rfl⟩ hr

/-- Normal original list frees erase exactly the listed TX slots. Repeated IDs
are allowed in the statement: a later missing getter instead Stops, retaining
only its reached access prefix, and cannot satisfy this normal-run premise. -/
theorem original_tx_list_disposal_exact (item : List SkbId) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((Queues.TxDisposition.freeList item).run w).run ambient = .ok (((), v), ambient')) :
    Queues.TxDisposition.txPackets v = fun id =>
      if id ∈ item then none else Queues.TxDisposition.txPackets w id :=
  (Framing.hoare_iff_run_ambient _ _ _).mp
    (Queues.TxDisposition.freeList_wp item (Queues.TxDisposition.txPackets w)) w ambient () v ambient' rfl hr

open Leanux.Proofs.Logged Queues.RxJoint

/-- One actual poll observes both stamped GRO payloads and original lifetime
accesses. Source erasure and GRO projection are unconditional; direct access
projection transports the existing allocation invariant. -/
theorem joint_poll_correspondence (pid : PeerId) (budget : Nat) :
    ErasesPrefix (poll pid budget)
      (Leanux.WG.rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) ∧
    ProjectsPrefix groEvent id (poll pid budget) (Queues.rxPollGro pid budget) ∧
    ProjectsUnder (fun h w => Lifetimes.AllocationInv h w.wg) accessEvent (poll pid budget)
      (Lifetimes.rxPollStackPrefix pid budget) :=
  ⟨poll_erases pid budget, poll_gro pid budget, poll_access pid budget⟩

/-- Each poll starts a fresh occurrence journal while retaining arbitrary
valid prior lifetime history. Every Stop retains its exact safe access suffix. -/
theorem joint_poll_fresh_history (pid : PeerId) (budget : Nat) (w : World)
    (prior : List Lifetimes.LifetimeEvent) (hi : Lifetimes.AllocationInv prior w.wg) :
    runPrefix (Queues.rxPollGro pid budget) w [] =
      ((runPrefix (poll pid budget) w (seed prior)).1,
        (runPrefix (poll pid budget) w (seed prior)).2.filterMap groEvent) ∧
    ∃ suffix, (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix ∧
      Lifetimes.LifetimeEvent.Safe (prior ++ suffix.filterMap accessEvent) ∧
      (match (runPrefix (poll pid budget) w (seed prior)).1 with
       | .error _ => True
       | .ok (_, v) => Lifetimes.AllocationInv (prior ++ suffix.filterMap accessEvent) v.wg) :=
  ⟨poll_fresh_gro pid budget w prior, poll_safe_suffix pid budget w prior hi⟩

/-- Removal allocation stamps are distinct on every reached poll prefix.
Normal return observes a real release for every removed allocation; no release
of a pending captured stamp is asserted after a Stop. -/
theorem joint_poll_removal_identity_safety (pid : PeerId) (budget : Nat) (w : World)
    (prior : List Lifetimes.LifetimeEvent) (hi : Lifetimes.AllocationInv prior w.wg) :
    (removedStamps (runPrefix (poll pid budget) w (seed prior)).2).Nodup ∧
      (match (runPrefix (poll pid budget) w (seed prior)).1 with
       | .error _ => True
       | .ok _ => ∀ s ∈ removedStamps (runPrefix (poll pid budget) w (seed prior)).2,
          Released (runPrefix (poll pid budget) w (seed prior)).2 s) :=
  poll_removed_stamps pid budget w prior hi

/-- Actual callback entries have distinct allocation stamps within one poll.
Normal poll completion has released them all, including buffered GRO payloads
entered after their packet storage's earlier release. This is not a completed
delivery or cross-poll uniqueness statement. -/
theorem joint_poll_callback_identity_safety (pid : PeerId) (budget : Nat) (w : World)
    (prior : List Lifetimes.LifetimeEvent) (hi : Lifetimes.AllocationInv prior w.wg) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2
    ((entries h).map Entry.stamp).Nodup ∧
      (match (runPrefix (poll pid budget) w (seed prior)).1 with
       | .error _ => True
       | .ok _ => ∀ e ∈ entries h, Released h e.stamp) :=
  poll_entry_stamps pid budget w prior hi

/-- Full occurrence/slot/stamp provenance comes from the same joint poll
journal, even on failure. Independent source erasures are not its premise. -/
theorem joint_poll_callback_removal_provenance (pid : PeerId) (budget : Nat) (w : World)
    (prior : List Lifetimes.LifetimeEvent) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2
    ∀ e ∈ entries h, e.key ∈ removalKeys h :=
  poll_entry_support pid budget w prior

/-- An entry event precedes the actual stack callback and survives its Stop.
It records attempted handoff, without asserting callback success. -/
theorem joint_poll_callback_entry_prefix (e : Entry) (w : World) (h : List Queues.RxJoint.Event) :
    ∃ suffix, (runPrefix (enter e) w h).2 = h ++ [.entered e] ++ suffix :=
  enter_suffix e w h


/-- Every removed key and every entered payload has its matching original
capture read before its supporting removal, inside the new poll suffix.
The operational provenance requires no allocation or successful-return premise. -/
theorem joint_poll_capture_read_suffix (pid : PeerId) (budget : Nat) (w : World)
    (prior : List Lifetimes.LifetimeEvent) (suffix : List Queues.RxJoint.Event)
    (he : (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix) :
    (∀ k ∈ removalKeys suffix, ReadBeforeRemoval [] suffix k) ∧
      (∀ e ∈ entries suffix, ReadBeforeRemoval [] suffix e.key) :=
  ⟨poll_suffix_read_before pid budget w prior suffix he,
    poll_suffix_entry_read_before pid budget w prior suffix he⟩

/-- No new removal or callback entry names a previously released allocation.
Entry stamps are distinct on failed prefixes too. Normal return has observed
all removal and entry releases in this very suffix, including explicit drops. -/
theorem joint_poll_suffix_lifetime (pid : PeerId) (budget : Nat) (w : World)
    (prior : List Lifetimes.LifetimeEvent) (hi : Lifetimes.AllocationInv prior w.wg)
    (suffix : List Queues.RxJoint.Event)
    (he : (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix) :
    ((∀ k ∈ removalKeys suffix, ¬ PriorReleased prior k.2.2) ∧
      (∀ e ∈ entries suffix, ¬ PriorReleased prior e.stamp)) ∧
    (((entries suffix).map Entry.stamp).Nodup ∧
      (match (runPrefix (poll pid budget) w (seed prior)).1 with
       | .error _ => True
       | .ok _ => ∀ e ∈ entries suffix, Released suffix e.stamp)) ∧
    (match (runPrefix (poll pid budget) w (seed prior)).1 with
     | .error _ => True
     | .ok _ => ∀ k ∈ removalKeys suffix, Released suffix k.2.2) :=
  ⟨poll_suffix_fresh pid budget w prior hi suffix he,
    poll_suffix_entries pid budget w prior hi suffix he,
    poll_suffix_removal_release pid budget w prior hi suffix he⟩

/-- Persistent poll metadata directly projects to the existing audit observer
at the identical incoming lifetime history. Old probe entries and Stops are
retained. Source erasure and suffix extension are unconditional. -/
theorem joint_poll_persistent_correspondence (pid : PeerId) (budget : Nat) :
    ErasesPrefix (Queues.RxHistory.observePoll pid budget)
      (Leanux.WG.rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.observePoll pid budget)
      (Lifetimes.auditFocus (Lifetimes.rxPollStackPrefix pid budget)) ∧
    Appends (Queues.RxHistory.observePoll pid budget) :=
  ⟨Queues.RxHistory.observePoll_erases pid budget,
    Queues.RxHistory.observePoll_projects pid budget,
    Queues.RxHistory.observePoll_appends pid budget⟩

/-- Normal boundaries retain released, distinct entry stamps; failed prefixes
retain uniqueness without requiring the last capture's release. The generic
audit frame preserves recorded entries, not coverage of polls inside its callee. -/
theorem joint_poll_boundary_composition (pid : PeerId) (budget : Nat)
    (a : Lifetimes.AuditM α) (ha : PrefixPreserves Lifetimes.AuditInv Lifetimes.AuditSafe a) :
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.observePoll pid budget) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.audit a) :=
  ⟨Queues.RxHistory.observePoll_preserves pid budget, Queues.RxHistory.audit_preserves a ha⟩

/-- Finite sequences of the original polls have distinct observed callback-entry
allocation stamps on every prefix from an allocation-valid empty-history entry.
This is composition of polls, not initialized scheduler/Runner coverage or
successful stack delivery. -/
theorem joint_poll_finite_sequence (calls : List (PeerId × Nat)) (w : World)
    (hi : Lifetimes.AllocationInv [] w.wg) :
    ErasesPrefix (Queues.RxHistory.polls calls)
      (calls.forM fun (pid, budget) => do
        discard <| Leanux.WG.rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.polls calls) ∧
    Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.polls calls) w []).2 :=
  ⟨Queues.RxHistory.polls_erases calls, Queues.RxHistory.polls_preserves calls,
    Queues.RxHistory.polls_safe calls w hi⟩

/-- The actual NET_RX softirq caller observes every reached direct poll.
Original guards, saved-map reads, section framing and callback Stops survive
exact source erasure and audit projection at the same incoming history.
Entry stamps stay distinct on failures; only normal returns restore releases. -/
theorem original_napi_softirq_joint :
    ErasesPrefix Queues.RxHistory.napiSoftirq Leanux.Env.napiSoftirq ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      Queues.RxHistory.napiSoftirq (Lifetimes.auditFocus Lifetimes.napiSoftirqPrefix) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      Queues.RxHistory.napiSoftirq ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix Queues.RxHistory.napiSoftirq w []).2 :=
  ⟨Queues.RxHistory.napiSoftirq_erases, Queues.RxHistory.napiSoftirq_projects,
    Queues.RxHistory.napiSoftirq_preserves,
    fun w hi => (Queues.RxHistory.napiSoftirq_preserves w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- Inline scheduled polling observes its direct source calls without adding
a worker section. The complete scan and multi-peer refusal remain exact.
The allocation-valid local entry is not an initialized Runner theorem. -/
theorem original_inline_poll_joint :
    ErasesPrefix Queues.RxHistory.pollScheduledInline Leanux.Env.pollScheduledInline ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      Queues.RxHistory.pollScheduledInline (Lifetimes.auditFocus Lifetimes.pollScheduledInlinePrefix) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      Queues.RxHistory.pollScheduledInline ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix Queues.RxHistory.pollScheduledInline w []).2 :=
  ⟨Queues.RxHistory.pollScheduledInline_erases, Queues.RxHistory.pollScheduledInline_projects,
    Queues.RxHistory.pollScheduledInline_preserves,
    fun w hi => (Queues.RxHistory.pollScheduledInline_preserves w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- IRQ exit retains short-circuit peer reads, all placement guards and the
actual true-arm softirq rescan. Prior probe markers remain interleaved in the
direct audit projection. Callback entry does not assert successful delivery. -/
theorem original_napi_irq_exit_joint :
    ErasesPrefix Queues.RxHistory.napiIrqExit Leanux.Env.napiIrqExit ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      Queues.RxHistory.napiIrqExit (Lifetimes.auditFocus Lifetimes.napiIrqExitPrefix) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      Queues.RxHistory.napiIrqExit ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix Queues.RxHistory.napiIrqExit w []).2 :=
  ⟨Queues.RxHistory.napiIrqExit_erases, Queues.RxHistory.napiIrqExit_projects,
    Queues.RxHistory.napiIrqExit_preserves,
    fun w hi => (Queues.RxHistory.napiIrqExit_preserves w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- The concrete encrypt iteration observes its initial softirq even when its
queue is empty. The remaining checksum/encryption/reschedule cut contains no poll.
Failed prefixes retain entry uniqueness; only normal returns restore releases. -/
theorem original_encrypt_iteration_joint :
    ErasesPrefix Queues.RxHistory.encryptIteration (Leanux.WG.encryptIter Leanux.Env.checksumHelp Leanux.Env.napiSoftirq
      (Leanux.Env.condResched .encryptWorker)) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      Queues.RxHistory.encryptIteration (Lifetimes.auditFocus (Lifetimes.encryptIterPrefix (fun p => liftPrefix (Leanux.Env.checksumHelp p))
        Lifetimes.napiSoftirqPrefix (liftPrefix (Leanux.Env.condResched .encryptWorker)))) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      Queues.RxHistory.encryptIteration ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix Queues.RxHistory.encryptIteration w []).2 :=
  ⟨Queues.RxHistory.encryptIteration_erases, Queues.RxHistory.encryptIteration_projects,
    Queues.RxHistory.encryptIteration_preserves,
    fun w hi => (Queues.RxHistory.encryptIteration_preserves w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- The concrete decrypt iteration observes initial and trailing softirqs plus
the publication IRQ placement. Cached publication writes and later peerPut retain
the original getters, callback Stops and allocation-derived identity checks. -/
theorem original_decrypt_iteration_joint :
    ErasesPrefix Queues.RxHistory.decryptIteration (Leanux.WG.decryptIter Leanux.Env.napiSoftirq Leanux.Env.napiIrqExit
      (Leanux.Env.condResched .decryptWorker)) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      Queues.RxHistory.decryptIteration (Lifetimes.auditFocus (Lifetimes.decryptIterPrefix Lifetimes.napiSoftirqPrefix Lifetimes.napiIrqExitPrefix
        (liftPrefix (Leanux.Env.condResched .decryptWorker)))) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      Queues.RxHistory.decryptIteration ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix Queues.RxHistory.decryptIteration w []).2 :=
  ⟨Queues.RxHistory.decryptIteration_erases, Queues.RxHistory.decryptIteration_projects,
    Queues.RxHistory.decryptIteration_preserves,
    fun w hi => (Queues.RxHistory.decryptIteration_preserves w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- Transmit pre-encryption retains hidden-record guards, its temporary work
queue and suspended activation update, including Stops after an observed encrypt
callback. Direct audit projection preserves the same prior probe interleaving. -/
theorem original_crypt_ahead_joint (pid : PeerId) :
    ErasesPrefix (Queues.RxHistory.cryptAhead pid) (Leanux.Env.cryptAhead pid) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.cryptAhead pid) (Lifetimes.auditFocus (Lifetimes.cryptAheadPrefix pid)) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.cryptAhead pid) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.cryptAhead pid) w []).2 :=
  ⟨Queues.RxHistory.cryptAhead_erases pid, Queues.RxHistory.cryptAhead_projects pid,
    Queues.RxHistory.cryptAhead_preserves pid,
    fun w hi => (Queues.RxHistory.cryptAhead_preserves pid w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- One original activation iteration composes all concrete crypt callbacks
with poll-free TX/receive observers. This is a local allocation-valid contract;
the enclosing scheduler is composed below. Initialized Env/Runner coverage and
completed stack delivery remain open. -/
theorem original_activation_iteration_joint (a : Activation) :
    ErasesPrefix (Queues.RxHistory.activationIteration a) (Leanux.Env.Activation.iter a) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.activationIteration a) (Lifetimes.auditFocus (Lifetimes.activationIterPrefix a)) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.activationIteration a) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.activationIteration a) w []).2 :=
  ⟨Queues.RxHistory.activationIteration_erases a, Queues.RxHistory.activationIteration_projects a,
    Queues.RxHistory.activationIteration_preserves a,
    fun w hi => (Queues.RxHistory.activationIteration_preserves a w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- A complete original activation run observes every reached iteration,
including occupancy reads, section-stop failure, yield and bound exhaustion.
Only normal completion restores releases; failed prefixes retain entry uniqueness. -/
theorem original_activation_run_joint (a : Activation) :
    ErasesPrefix (Queues.RxHistory.activationRun a) (Leanux.Env.Activation.run a) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.activationRun a) (Lifetimes.auditFocus (Lifetimes.activationRunPrefix a)) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.activationRun a) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.activationRun a) w []).2 :=
  ⟨Queues.RxHistory.activationRun_erases a, Queues.RxHistory.activationRun_projects a,
    Queues.RxHistory.activationRun_preserves a,
    fun w hi => (Queues.RxHistory.activationRun_preserves a w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- Original dispatch retains empty/default refusals, TX unit resolution and
queue erasure before section start. Its actual run carries stamped NAPI callbacks
and directly projects to the existing audit at the same incoming history. -/
theorem original_dispatch_joint (worker : Worker) :
    ErasesPrefix (Queues.RxHistory.dispatch worker) (Leanux.Env.dispatch worker) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.dispatch worker) (Lifetimes.auditFocus (Lifetimes.dispatchPrefix worker)) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.dispatch worker) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.dispatch worker) w []).2 :=
  ⟨Queues.RxHistory.dispatch_erases worker, Queues.RxHistory.dispatch_projects worker,
    Queues.RxHistory.dispatch_preserves worker,
    fun w hi => (Queues.RxHistory.dispatch_preserves worker w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- The actual finite scheduler observes committed polls and exact existing
filter-entry probes. Copied trial worlds and histories remain isolated; each
reached marker supplies allocation safety and the original ordered filter decision.
This local entry contract does not establish initialized enclosing Runner coverage. -/
theorem original_recorded_schedule_joint (stack : Option Worker) :
    ErasesPrefix (Queues.RxHistory.schedule stack) (Leanux.Env.schedule stack) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.schedule stack) (Lifetimes.scheduleAudit stack) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.schedule stack) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.schedule stack) w []).2 ∧
      ∀ p ∈ Lifetimes.probeEntries (Queues.RxHistory.auditHistory
          (runPrefix (Queues.RxHistory.schedule stack) w []).2),
        Lifetimes.AllocationInv p.history p.world.wg ∧
        (p.world.ambient.suspended.filterM Leanux.Env.Activation.consistent).run p.world =
          (p.world.ambient.suspended.filterM (fun a => Lifetimes.activationTrialDecision a p.world p.history)).map
            (fun ys => (ys, p.world)) ∧
        ∀ a ∈ p.world.ambient.suspended,
          Lifetimes.LifetimeEvent.Safe (runPrefix (Lifetimes.activationRunPrefix a) p.world p.history).2 :=
  ⟨Queues.RxHistory.schedule_erases stack, Queues.RxHistory.schedule_projects stack,
    Queues.RxHistory.schedule_preserves stack,
    fun w hi => ⟨(Queues.RxHistory.schedule_preserves stack w []
      (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1,
      fun p hp => Queues.RxHistory.schedule_trials stack w []
        (Queues.RxHistory.boundary_initial w hi) p hp⟩⟩

/-- Nested rescheduling consumes the original worker reschedule record and
invokes the observed scheduler only on its true arm. Audit probes, Stops and
committed entry uniqueness survive; callback entry is not completed delivery. -/
theorem original_nested_reschedule_joint (self : Worker) :
    ErasesPrefix (Queues.RxHistory.nestedResched self) (Leanux.Env.nestedResched self) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.nestedResched self) (Lifetimes.nestedReschedAudit self) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.nestedResched self) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.nestedResched self) w []).2 :=
  ⟨Queues.RxHistory.nestedResched_erases self, Queues.RxHistory.nestedResched_projects self,
    Queues.RxHistory.nestedResched_preserves self,
    fun w hi => (Queues.RxHistory.nestedResched_preserves self w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- The actual deferred crypt/send continuations retain all reached scheduler
calls. Focused send/drain leaves are poll-free, with exact R2 access histories.
All failure prefixes retain entry uniqueness; normal boundaries restore releases. -/
theorem original_deferred_workers_joint :
    (ErasesPrefix Queues.RxHistory.runCryptWorkers (Leanux.Env.runCryptWorkers) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent Queues.RxHistory.runCryptWorkers Lifetimes.runCryptWorkersAudit ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe Queues.RxHistory.runCryptWorkers ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix Queues.RxHistory.runCryptWorkers w []).2) ∧
    (ErasesPrefix Queues.RxHistory.runSendWorkers (Leanux.Env.runSendWorkers) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent Queues.RxHistory.runSendWorkers Lifetimes.runSendWorkersAudit ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe Queues.RxHistory.runSendWorkers ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix Queues.RxHistory.runSendWorkers w []).2) ∧
    (ErasesPrefix Queues.RxHistory.afterXmit (Leanux.Env.afterXmit) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent Queues.RxHistory.afterXmit Lifetimes.afterXmitAudit ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe Queues.RxHistory.afterXmit ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix Queues.RxHistory.afterXmit w []).2) :=
  ⟨⟨Queues.RxHistory.runCryptWorkers_erases, Queues.RxHistory.runCryptWorkers_projects, Queues.RxHistory.runCryptWorkers_preserves,
    fun w hi => (Queues.RxHistory.runCryptWorkers_preserves w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩,
  ⟨Queues.RxHistory.runSendWorkers_erases, Queues.RxHistory.runSendWorkers_projects, Queues.RxHistory.runSendWorkers_preserves,
    fun w hi => (Queues.RxHistory.runSendWorkers_preserves w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩,
  ⟨Queues.RxHistory.afterXmit_erases, Queues.RxHistory.afterXmit_projects, Queues.RxHistory.afterXmit_preserves,
    fun w hi => (Queues.RxHistory.afterXmit_preserves w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩⟩

/-- Original injection preserves its namespace and destination guards, NET_RX
receive section and deferred scheduler. The direct R2 audit projection uses the
same incoming journal, including prior consistency probes. -/
theorem original_inject_joint (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (Queues.RxHistory.inject family port msg tos ll dest) (Leanux.Env.inject family port msg tos ll dest) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent (Queues.RxHistory.inject family port msg tos ll dest) (Lifetimes.injectAudit family port msg tos ll dest) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe (Queues.RxHistory.inject family port msg tos ll dest) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.inject family port msg tos ll dest) w []).2 :=
  ⟨Queues.RxHistory.inject_erases family port msg tos ll dest, Queues.RxHistory.inject_projects family port msg tos ll dest, Queues.RxHistory.inject_preserves family port msg tos ll dest,
    fun w hi => (Queues.RxHistory.inject_preserves family port msg tos ll dest w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- The original exact flood observes every producer, inline poll and deferred
activation, including actual nested receive reschedules and the final drain guard. No drain, progress, credit or history-neutrality premise is added. -/
theorem original_flood_joint (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (Queues.RxHistory.flood count port family messages) (Leanux.Env.flood count port family messages) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent (Queues.RxHistory.flood count port family messages) (Lifetimes.floodAudit count port family messages) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe (Queues.RxHistory.flood count port family messages) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.flood count port family messages) w []).2 :=
  ⟨Queues.RxHistory.flood_erases count port family messages, Queues.RxHistory.flood_projects count port family messages, Queues.RxHistory.flood_preserves count port family messages,
    fun w hi => (Queues.RxHistory.flood_preserves count port family messages w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- Original batch continuation, item and complete submission preserve CQEs,
captured device scalars and actual scheduler calls. Ingress and its stamped inline
poll remain inside the same NET_RX wrapper, including callback failure before
cleanup. These local entry contracts do not establish initialized Env/Runner
coverage, successful stack delivery or receive-pipeline conservation. -/
theorem original_batch_joint (d : Device) (cqes : List Int) (item : Leanux.Env.BatchItem) (items : List Leanux.Env.BatchItem) :
    (ErasesPrefix Queues.RxHistory.afterBatch (Leanux.Env.afterBatch) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent Queues.RxHistory.afterBatch Lifetimes.afterBatchAudit ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe Queues.RxHistory.afterBatch ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix Queues.RxHistory.afterBatch w []).2) ∧
    (ErasesPrefix (Queues.RxHistory.batchItem d cqes item) (Environment.batchItemSource d cqes item) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent (Queues.RxHistory.batchItem d cqes item) (Lifetimes.batchItemAudit d cqes item) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe (Queues.RxHistory.batchItem d cqes item) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.batchItem d cqes item) w []).2) ∧
    (ErasesPrefix (Queues.RxHistory.batch items) (Leanux.Env.batch items) ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent (Queues.RxHistory.batch items) (Lifetimes.batchAudit items) ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe (Queues.RxHistory.batch items) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.batch items) w []).2) :=
  ⟨⟨Queues.RxHistory.afterBatch_erases, Queues.RxHistory.afterBatch_projects, Queues.RxHistory.afterBatch_preserves,
    fun w hi => (Queues.RxHistory.afterBatch_preserves w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩,
  ⟨Queues.RxHistory.batchItem_erases d cqes item, Queues.RxHistory.batchItem_projects d cqes item, Queues.RxHistory.batchItem_preserves d cqes item,
    fun w hi => (Queues.RxHistory.batchItem_preserves d cqes item w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩,
  ⟨Queues.RxHistory.batch_erases items, Queues.RxHistory.batch_projects items, Queues.RxHistory.batch_preserves items,
    fun w hi => (Queues.RxHistory.batch_preserves items w [] (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩⟩

/-- Every original deferred caller has exact source and full-audit correspondence.
Recorded/placeholder timer passes observe actual crypt/send continuations; the
placeholder reset and absent return precede its poll-free saved-peer timer block.
Wait records, failed callbacks and prior consistency probes retain source order. -/
theorem original_environment_deferred_joint (call : Lifetimes.EnvDeferredCall) :
    ErasesPrefix (Queues.RxHistory.deferred call) call.original ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.deferred call) call.observed ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.deferred call) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.deferred call) w []).2 :=
  ⟨Queues.RxHistory.deferred_erases call, Queues.RxHistory.deferred_projects call,
    Queues.RxHistory.deferred_preserves call,
    fun w hi => (Queues.RxHistory.deferred_preserves call w []
      (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- Every remaining original environment caller, including observation, uses its
concrete stamped timer/traffic path or an inspected poll-free control observer.
The same incoming audit history projects directly, with failed-prefix uniqueness
and normal release boundaries. The initialized syscall/Runner composition follows
below; successful stack delivery and joint receive-pipeline conservation remain
separate obligations. -/
theorem original_environment_remaining_joint (call : Lifetimes.EnvRemainingCall) :
    ErasesPrefix (Queues.RxHistory.remaining call) call.original ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.remaining call) call.observed ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.remaining call) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.remaining call) w []).2 :=
  ⟨Queues.RxHistory.remaining_erases call, Queues.RxHistory.remaining_projects call,
    Queues.RxHistory.remaining_preserves call,
    fun w hi => (Queues.RxHistory.remaining_preserves call w []
      (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- Every original dispatch/syscall arm and fixture holder-close boundary has
exact source and same-history audit correspondence. Normal negative errno still
runs the original worker/timer suffix; failed prefixes retain entry uniqueness. -/
theorem original_syscall_family_joint (call : Lifetimes.SyscallAuditCall) :
    ErasesPrefix (Queues.RxHistory.syscallFamily call) call.original ∧
    ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.syscallFamily call) call.observed ∧
    PrefixPreserves Queues.RxHistory.BoundaryInv Queues.RxHistory.BoundarySafe
      (Queues.RxHistory.syscallFamily call) ∧
    ∀ w, Lifetimes.AllocationInv [] w.wg →
      Queues.RxHistory.BoundarySafe (runPrefix (Queues.RxHistory.syscallFamily call) w []).2 :=
  ⟨Queues.RxHistory.syscallFamily_erases call, Queues.RxHistory.syscallFamily_projects call,
    Queues.RxHistory.syscallFamily_preserves call,
    fun w hi => (Queues.RxHistory.syscallFamily_preserves call w []
      (Queues.RxHistory.boundary_initial w hi)).choose_spec.2.1⟩

/-- Every typed initialized Runner trace and both placeholder settings retain distinct committed
callback-entry allocation stamps, even on Stop, and exactly the existing full R2
audit/probe history. Copied trials remain isolated. No parser, length, success,
drain, credit or progress premise is added. Callback entry does not assert stack
completion, and receive-pipeline conservation remains a separate obligation. -/
theorem initialized_runner_joint (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    Logged.ErasesOuter (Queues.RxHistory.executeTraceHistory trace placeholders)
      (Leanux.Runner.executeTrace trace placeholders) ∧
    Queues.RxHistory.BoundarySafe
      (Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 ∧
    Logged.runPrefixOuter (Lifetimes.executeTraceAudit trace placeholders) [] =
      ((Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).1,
       Queues.RxHistory.auditHistory
         (Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2) ∧
    ∀ p ∈ Lifetimes.probeEntries (Queues.RxHistory.auditHistory
        (Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2),
      Lifetimes.AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Leanux.Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => Lifetimes.activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended,
        Lifetimes.LifetimeEvent.Safe
          (runPrefix (Lifetimes.activationRunPrefix a) p.world p.history).2 :=
  ⟨Queues.RxHistory.executeTraceHistory_erases trace placeholders,
    Queues.RxHistory.executeTraceHistory_safe trace placeholders,
    Queues.RxHistory.executeTraceHistory_projects trace placeholders,
    Queues.RxHistory.executeTraceHistory_trials trace placeholders⟩

/-- The callback observer runs the actual Stack operation once. Entry is before
it; a receipt contains its actual entry/return Worlds only on normal return.
A Stop retains the actual callback access prefix and produces no receipt. -/
theorem original_callback_return_execution (e : Queues.RxJoint.Entry)
    (w : World) (h : List Queues.RxJoint.Event) :
    Logged.ErasesPrefix (Queues.RxJoint.enter e) (Leanux.Env.Stack.receive e.tag.bytes) ∧
    runPrefix (Queues.RxJoint.enter e) w h =
      match runPrefix (Queues.RxJoint.access (Lifetimes.stackReceivePrefix e.tag.bytes))
          w (h ++ [.entered e]) with
      | (.error stop, t) => (.error stop, t)
      | (.ok (x, v), t) => (.ok (x, v), t ++ [.completed e ⟨x, w, v⟩]) :=
  ⟨Queues.RxCompletion.enter_erases e, Queues.RxCompletion.enter_run e w h⟩

/-- Every local poll obeys ordered callback pairing, without allocation or
progress assumptions. Normal return matches all entered callbacks with valid
original Stack receipts; a failed prefix may leave one final entry unmatched. -/
theorem original_poll_callback_completion (pid : PeerId) (budget : Nat) :
    Queues.RxCompletion.Preserves Queues.RxCompletion.jointEvent (Queues.RxJoint.poll pid budget) ∧
    ∀ w h, Queues.RxCompletion.Closed Queues.RxCompletion.jointEvent h →
      ∀ n v, (runPrefix (Queues.RxJoint.poll pid budget) w h).1 = .ok (n, v) →
        let t := (runPrefix (Queues.RxJoint.poll pid budget) w h).2.filterMap Queues.RxCompletion.jointEvent
        Queues.RxJoint.entries (runPrefix (Queues.RxJoint.poll pid budget) w h).2 =
          t.filterMap Queues.RxCompletion.completed ∧
          ∀ e r, Queues.RxCompletion.Step.completed e r ∈ t →
            r.Valid (Leanux.Env.Stack.receive e.tag.bytes) :=
  ⟨Queues.RxCompletion.poll_preserves pid budget,
    fun w h hi n v hr => by
      simpa only [Queues.RxCompletion.joint_entries] using Queues.RxCompletion.normal_receipts
        (Queues.RxCompletion.poll_preserves pid budget) w h hi n v hr⟩

/-- Actual persistent polls append only the fresh local suffix and preserve
ordered callback pairing at the identical incoming audit seed. This includes
finite poll sequences and Stops. The caller/Runner composition follows below;
socket inbox delivery and receive-pipeline conservation remain separate. -/
theorem persistent_poll_callback_completion (pid : PeerId) (budget : Nat)
    (calls : List (PeerId × Nat)) :
    Queues.RxCompletion.Preserves Queues.RxCompletion.historyEvent
      (Queues.RxHistory.observePoll pid budget) ∧
    Queues.RxCompletion.Preserves Queues.RxCompletion.historyEvent
      (Queues.RxHistory.polls calls) :=
  ⟨Queues.RxCompletion.observePoll_preserves pid budget,
    Queues.RxCompletion.polls_preserves calls⟩

/-- Ordered callback entry/return pairing propagates through the existing
concrete Env and syscall observers, including all worker, timer and scheduler
continuations. The history premise is only prior completion pairing; allocation,
residency, credit and progress are not premises. Stops retain a prefix with at
most one unfinished trailing callback. Source erasure and full audit projection
remain those of the preceding original-caller contracts. -/
theorem original_caller_callback_completion (deferred : Lifetimes.EnvDeferredCall)
    (remaining : Lifetimes.EnvRemainingCall) (syscall : Lifetimes.SyscallAuditCall) :
    Queues.RxCompletion.Preserves Queues.RxCompletion.historyEvent
      (Queues.RxHistory.deferred deferred) ∧
    Queues.RxCompletion.Preserves Queues.RxCompletion.historyEvent
      (Queues.RxHistory.remaining remaining) ∧
    Queues.RxCompletion.Preserves Queues.RxCompletion.historyEvent
      (Queues.RxHistory.syscallFamily syscall) :=
  ⟨Queues.RxCompletion.deferred_preserves deferred,
    Queues.RxCompletion.remaining_preserves remaining,
    Queues.RxCompletion.syscallFamily_preserves syscall⟩

/-- Every typed initialized Runner trace and both placeholder settings retain valid actual
Stack-return receipts and distinct completed allocation stamps, even on Stop.
Normal return pairs every committed callback entry in order; a failed prefix can
leave one last entry unfinished. Copied consistency trials remain outside this
committed journal. This is the same observer whose unconditional original Runner
erasure and exact full audit projection are proved by initialized_runner_joint.
It proves normal Stack return, not socket inbox arrival or receive-pipeline
conservation, and adds no parser, allocation or success premise. -/
theorem initialized_runner_callback_completion (trace : Leanux.Runner.Trace)
    (placeholders : Bool) :
    Logged.ErasesOuter (Queues.RxHistory.executeTraceHistory trace placeholders)
      (Leanux.Runner.executeTrace trace placeholders) ∧
    let out := Logged.runPrefixOuter
      (Queues.RxHistory.executeTraceHistory trace placeholders) []
    let t := out.2.filterMap Queues.RxCompletion.historyEvent
    Queues.RxCompletion.CompletionPrefix Queues.RxCompletion.historyEvent out.2 ∧
    (∀ e r, Queues.RxCompletion.Step.completed e r ∈ t →
      r.Valid (Leanux.Env.Stack.receive e.tag.bytes)) ∧
    ((t.filterMap Queues.RxCompletion.completed).map Queues.RxJoint.Entry.stamp).Nodup ∧
    (∀ result, out.1 = .ok result →
      Queues.RxCompletion.Closed Queues.RxCompletion.historyEvent out.2 ∧
      Queues.RxHistory.entries out.2 = t.filterMap Queues.RxCompletion.completed) := by
  refine ⟨Queues.RxHistory.executeTraceHistory_erases trace placeholders, ?_⟩
  have hp := Queues.RxCompletion.executeTraceHistory_completion trace placeholders
  have hr := Queues.RxCompletion.executeTraceHistory_receipts trace placeholders
  exact ⟨hp.1, hr.1, hr.2.1, fun result hs => ⟨hp.2 result hs, hr.2.2 result hs⟩⟩

/-- Every freshly observed poll has valid check/consume receipts and carried
consume-run payload witnesses, even on Stop. Normal None is classified
by the original executed source factors; the endpoint helper never returns
None normally. This run/payload contract alone does not identify the consume
packet with the captured allocation or its earlier consumed event. The stronger
local source/history link is exported below; initialized routing remains open. -/
theorem original_poll_disposition_receipts (pid : PeerId) (budget : Nat)
    (w : World) (prior : List Lifetimes.LifetimeEvent) :
    Queues.RxDisposition.Valid
      (runPrefix (Queues.RxJoint.poll pid budget) w (Queues.RxJoint.seed prior)).2 ∧
    (∀ r : Queues.RxDisposition.ConsumeReceipt, r.Valid → r.run.value = none →
      Queues.RxDisposition.PrepareRejected r.packet ∨
      ∃ ready u q routed paid middle afterLookup afterPaid,
        ((Packets.rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore =
          .ok ((some ready, u), middle) ∧
        ((lookupSrc ready.protocol ready.bytes).run u).run middle = .ok ((routed, q), afterLookup) ∧
        ((peerPut routed).run q).run afterLookup = .ok (((), paid), afterPaid) ∧ routed ≠ some r.peer ∧
        ((Packets.rxAfterLookup r.peer ready routed).run q).run afterLookup =
          .ok ((none, r.run.after), r.run.ambientAfter)) ∧
    (∀ (pkt : RxPacket) (r : Logged.RunWitness (Option Endpoint)),
      r.Valid (liftWG (endpointFromSkb pkt.source)) → r.value = none → False) :=
  ⟨Queues.RxDisposition.poll_seed_valid pid budget w prior,
    Queues.RxDisposition.none_classified, Queues.RxDisposition.endpoint_none_impossible⟩

/-- Actual removed occurrences partition by source phase, not chronological
concatenation of GRO output. Stop retains at most one unresolved selection, the entire
unentered selected-offer suffix (including an offered second held packet), and
at most one entered unfinished callback. Normal return leaves no residual and
partitions uniquely into nondelivery decisions/None and completed Stack calls.
Nondelivery decisions on Stop do not assert completed put/free cleanup. This is
local post-removal accounting, not initialized admission/carrier conservation. -/
theorem original_poll_occurrence_dispositions (pid : PeerId) (budget : Nat)
    (w : World) (prior : List Lifetimes.LifetimeEvent) :
    let h := (runPrefix (Queues.RxJoint.poll pid budget) w (Queues.RxJoint.seed prior)).2
    (∃ pending : Option Queues.RxJoint.EntryKey,
      Queues.RxDisposition.Account pending h ∧
      ((Queues.RxJoint.removalKeys h).map Prod.fst).Perm
        ((h.filterMap Queues.RxDisposition.nondeliveryKey).map Prod.fst ++
         (Queues.RxDisposition.completedEntries h).map (fun e => e.tag.occurrence) ++
         (Queues.RxDisposition.callbackPending h).map (fun e => e.tag.occurrence) ++
         (Queues.RxDisposition.unentered h).map Queues.GroEntry.occurrence ++ pending.toList.map Prod.fst) ∧
      (Queues.RxDisposition.callbackPending h).length ≤ 1 ∧
      ((Queues.RxJoint.removalKeys h).map Prod.fst).Nodup) ∧
    (∀ n v, (runPrefix (Queues.RxJoint.poll pid budget) w (Queues.RxJoint.seed prior)).1 = .ok (n, v) →
      Queues.RxDisposition.Account none h ∧ Queues.RxDisposition.callbackPending h = [] ∧
      Queues.RxDisposition.unentered h = [] ∧
      ((Queues.RxJoint.removalKeys h).map Prod.fst).Perm
        ((h.filterMap Queues.RxDisposition.nondeliveryKey).map Prod.fst ++
          (Queues.RxDisposition.completedEntries h).map (fun e => e.tag.occurrence)) ∧
      (((h.filterMap Queues.RxDisposition.nondeliveryKey).map Prod.fst ++
          (Queues.RxDisposition.completedEntries h).map (fun e => e.tag.occurrence))).Nodup) :=
  ⟨Queues.RxDisposition.poll_partition pid budget w prior,
    fun n v hr => Queues.RxDisposition.poll_normal_partition pid budget w v prior n hr⟩

/-- Persistent promotion uses the same incoming lifetime history and appends
only its actual fresh valid receipt suffix, preserving prior probes. Original
erasure is unconditional; the separate existing full audit projection keeps
its original allocation premise. No old arbitrary origin metadata is validated. -/
theorem persistent_poll_disposition_receipts (pid : PeerId) (budget : Nat)
    (w : World) (h : List Queues.RxHistory.Event) :
    Logged.ErasesPrefix (Queues.RxHistory.observePoll pid budget)
      (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) ∧
    ∃ suffix : List Queues.RxJoint.Event,
      (runPrefix (Queues.RxJoint.poll pid budget) w (Queues.RxJoint.seed (Queues.RxHistory.prior h))).2 =
        Queues.RxJoint.seed (Queues.RxHistory.prior h) ++ suffix ∧
      runPrefix (Queues.RxHistory.observePoll pid budget) w h =
        ((runPrefix (Queues.RxJoint.poll pid budget) w (Queues.RxJoint.seed (Queues.RxHistory.prior h))).1,
          h ++ suffix.map Queues.RxHistory.promote) ∧ Queues.RxDisposition.Valid suffix :=
  ⟨Queues.RxHistory.observePoll_erases pid budget,
    Queues.RxDisposition.observePoll_receipt_suffix pid budget w h⟩

/-- In the unchanged original poll, every reached consume receipt names the
actual selected skb/stamp/packet at consume entry and the checked peer. Its
strict earlier prefix contains the capture read followed by that removal.
Each buffered/entered/completed full Entry carries the same whole receipt in
order in this fresh suffix, including on Stop. No allocation, current residency
or initialized-origin premise is added. Consume's after World is not equated
with the later Stack callback's before World. -/
theorem original_poll_packet_receipt_links (pid : PeerId) (budget : Nat)
    (w : World) (prior : List Lifetimes.LifetimeEvent) :
    Logged.ErasesPrefix (Queues.RxJoint.poll pid budget)
      (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) ∧
    ∃ suffix,
      (runPrefix (Queues.RxJoint.poll pid budget) w (Queues.RxJoint.seed prior)).2 =
        Queues.RxJoint.seed prior ++ suffix ∧ Queues.RxLink.Linked [] suffix ∧
      ∀ event ∈ suffix, ∃ before after,
        suffix = before ++ [event] ++ after ∧ Queues.RxLink.EventLink [] before event :=
  ⟨Queues.RxJoint.poll_erases pid budget, Queues.RxLink.poll_ordered_links pid budget w prior⟩

/-- Persistent and finite-poll composition keeps exact input audit history and
old probe interleaving, promoting only the actual new linked suffix. The local
link has no World premise; preserving an entire old receipt history requires
that history's explicit linkage. The existing R2 projection retains its
original AuditInv premise. Initialized caller linkage is exported below; this
local contract does not prove key/session identity, inbox delivery or admission conservation. -/
theorem persistent_poll_packet_receipt_links (pid : PeerId) (budget : Nat)
    (calls : List (PeerId × Nat)) (w : World) (h : List Queues.RxHistory.Event) :
    Logged.ErasesPrefix (Queues.RxHistory.observePoll pid budget)
      (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) ∧
    Logged.ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.observePoll pid budget) (Lifetimes.auditFocus (Lifetimes.rxPollStackPrefix pid budget)) ∧
    Logged.PrefixPreserves (fun h _ => Queues.RxLink.HistoryLinked h) Queues.RxLink.HistoryLinked
      (Queues.RxHistory.observePoll pid budget) ∧
    Logged.PrefixPreserves (fun h _ => Queues.RxLink.HistoryLinked h) Queues.RxLink.HistoryLinked
      (Queues.RxHistory.polls calls) ∧
    ∃ suffix,
      (runPrefix (Queues.RxJoint.poll pid budget) w (Queues.RxJoint.seed (Queues.RxHistory.prior h))).2 =
        Queues.RxJoint.seed (Queues.RxHistory.prior h) ++ suffix ∧
      runPrefix (Queues.RxHistory.observePoll pid budget) w h =
        ((runPrefix (Queues.RxJoint.poll pid budget) w (Queues.RxJoint.seed (Queues.RxHistory.prior h))).1,
          h ++ suffix.map Queues.RxHistory.promote) ∧ Queues.RxLink.Linked [] suffix :=
  ⟨Queues.RxHistory.observePoll_erases pid budget, Queues.RxHistory.observePoll_projects pid budget,
    Queues.RxLink.observePoll_link pid budget, Queues.RxLink.polls_link calls,
    Queues.RxLink.observePoll_link_suffix pid budget w h⟩


/-- Concrete Env/syscall callers preserve source/history linkage and independently
checked consume/branch receipts. Each history-only premise is explicit for an
arbitrary incoming journal; neither requires a World, allocation or credit
premise. These are the unchanged observers with the original erasure/audit
contracts above. Focused audit framing alone is not hidden-poll coverage. -/
theorem original_caller_packet_receipt_linkage (deferred : Lifetimes.EnvDeferredCall)
    (remaining : Lifetimes.EnvRemainingCall) (syscall : Lifetimes.SyscallAuditCall) :
    (Queues.RxLink.Preserves Queues.RxLink.HistoryLinked (Queues.RxHistory.deferred deferred) ∧
      Queues.RxLink.Preserves Queues.RxLink.HistoryReceiptsValid (Queues.RxHistory.deferred deferred)) ∧
    (Queues.RxLink.Preserves Queues.RxLink.HistoryLinked (Queues.RxHistory.remaining remaining) ∧
      Queues.RxLink.Preserves Queues.RxLink.HistoryReceiptsValid (Queues.RxHistory.remaining remaining)) ∧
    (Queues.RxLink.Preserves Queues.RxLink.HistoryLinked (Queues.RxHistory.syscallFamily syscall) ∧
      Queues.RxLink.Preserves Queues.RxLink.HistoryReceiptsValid (Queues.RxHistory.syscallFamily syscall)) :=
  ⟨⟨Queues.RxLink.deferred_preserves deferred, Queues.RxLink.deferred_preserves deferred⟩,
    ⟨Queues.RxLink.remaining_preserves remaining, Queues.RxLink.remaining_preserves remaining⟩,
    ⟨Queues.RxLink.syscallFamily_preserves syscall, Queues.RxLink.syscallFamily_preserves syscall⟩⟩

/-- Every typed Trace and both placeholder settings have actual selected
packet/stamp/peer linkage and strict whole-receipt/Entry order in the same
committed history, even on Stop. Empty initialization discharges receipt truth
and linkage; the exact original result and full R2 audit/probes are unchanged.
The global order does not label individual poll boundaries: the stronger fresh
same-poll suffix theorem remains separate. Completed Stack calls retain their
actual receipts and distinct stamps, but key/session authentication, inbox
arrival and admission/carrier conservation are not conclusions. -/
theorem initialized_runner_packet_receipt_linkage (trace : Leanux.Runner.Trace)
    (placeholders : Bool) :
    Logged.ErasesOuter (Queues.RxHistory.executeTraceHistory trace placeholders)
      (Leanux.Runner.executeTrace trace placeholders) ∧
    Logged.runPrefixOuter (Lifetimes.executeTraceAudit trace placeholders) [] =
      ((Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).1,
        Queues.RxHistory.auditHistory
          (Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2) ∧
    let out := Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []
    let events := out.2.filterMap Queues.RxLink.historyEvent
    let callbacks := out.2.filterMap Queues.RxCompletion.historyEvent
    Queues.RxLink.HistoryLinked out.2 ∧ Queues.RxLink.HistoryReceiptsValid out.2 ∧
    (∀ event ∈ events, ∃ before after,
      events = before ++ [event] ++ after ∧ Queues.RxLink.EventLink [] before event) ∧
    Queues.RxHistory.BoundarySafe out.2 ∧
    Queues.RxCompletion.CompletionPrefix Queues.RxCompletion.historyEvent out.2 ∧
    (∀ e r, Queues.RxCompletion.Step.completed e r ∈ callbacks →
      r.Valid (Leanux.Env.Stack.receive e.tag.bytes)) ∧
    ((callbacks.filterMap Queues.RxCompletion.completed).map Queues.RxJoint.Entry.stamp).Nodup ∧
    (∀ result, out.1 = .ok result →
      Queues.RxCompletion.Closed Queues.RxCompletion.historyEvent out.2 ∧
      Queues.RxHistory.entries out.2 = callbacks.filterMap Queues.RxCompletion.completed) := by
  have old := initialized_runner_callback_completion trace placeholders
  have linked := Queues.RxLink.executeTraceHistory_linkage trace placeholders
  exact ⟨old.1, Queues.RxHistory.executeTraceHistory_projects trace placeholders,
    linked.1, linked.2, Queues.RxLink.executeTraceHistory_ordered trace placeholders,
    Queues.RxHistory.executeTraceHistory_safe trace placeholders, old.2⟩

open Queues.RxCredits

/-- Local source-acquired RX credit cuts. The complete lookup derives positivity
and its actual loan; admission retains that loan at allocation and derives the
stored key word. Allocation transfers an explicit reservation into the same
inventory, with vacancy stated openly. Pure-IRQ publication repays its own
resolved-peer borrow. This is not full consumeData or initialized protection. -/
theorem original_rx_credit_transfer :
    (∀ kinds index w v ambient ambient' result,
      ((indexLookup kinds index).run w).run ambient = .ok ((result,v),ambient') →
      Loan w (result.map Prod.snd) v) ∧
    (∀ msg src ds ctx w v ambient ambient',
      ((RxOrigin.admitSource msg src ds).run w).run ambient = .ok ((some ctx,v),ambient') →
      (∃ before allocationAmbient, Loan w (some ctx.packet.peer) before ∧
        ((newRxSkb ctx.packet).run before).run allocationAmbient = .ok ((ctx.slot,v),ambient')) ∧
      KeyWord ctx.packet.keypair ctx.packet.peer v) ∧
    (∀ cs loans w d o pkt ambient,
      Inventory cs w → w.dev = some d → d.rxSkbs[d.nextSkb]? = none →
      o.epoch = d.ifindex → pkt.peer = o.slot → Protected cs (o :: loans) w →
      ∃ v, ((newRxSkb pkt).run w).run ambient = .ok ((d.nextSkb,v),ambient) ∧
        Inventory (⟨⟨d.ifindex,d.nextSkb⟩,o,.unpublished⟩ :: cs) v ∧
        Protected (⟨⟨d.ifindex,d.nextSkb⟩,o,.unpublished⟩ :: cs) loans v) ∧
    (∀ id state w v ambient ambient',
      ((enqueuePerPeerRx (pure () : WG.M Unit) id state).run w).run ambient = .ok (((),v),ambient') →
      ∀ o, balance v o = balance w o) := by
  refine ⟨?_,?_,?_,publication_balances⟩
  · intro kinds index w v ambient ambient' result hr
    exact (Framing.hoare_iff_run_ambient _ _ _).mp
      (indexLookup_loan kinds index w) w ambient result v ambient' rfl hr
  · intro msg src ds ctx w v ambient ambient' hr
    exact ⟨admitted_loan ambient ambient' hr,admitted_key_word ambient ambient' hr⟩
  · intro cs loans w d o pkt ambient hi hd fresh epoch owner hs
    exact allocate_transfer ambient hi hd fresh epoch owner hs

/-- Supported cuts from the withdrawn original_rx_cleanup_credit_discharge:
actual cached-head selection, positive-demand non-retirement, and the actual
ENOSPC cleanup path. The former unrestricted selected-cleanup totality conjunct
is false; its counterexample is exported separately below. -/
theorem original_rx_cleanup_supported_cuts :
    (∀ (id : SkbId) w d pid p cs loans ambient,
      w.dev = some d → d.peers[pid]? = some p → p.rxQueue.peeked = some id →
      Inventory (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ :: cs) w →
      QueueOwners (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ :: cs) w →
      Protected (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.queued⟩ :: cs) loans w →
      ∃ v, ((Queues.dropRxQueue pid).run w).run ambient = .ok (((),v),ambient) ∧
        Inventory (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ :: cs) v ∧
        QueueOwners (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ :: cs) v ∧
        Protected (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ :: cs) loans v) ∧
    (∀ c cs loans w, Protected (c :: cs) loans w → c.phase = .selected →
      0 < demand cs loans c.owner → ∃ p, resident w c.owner = some p ∧ 1 < p.refcount) ∧
    (∀ ctx c cs loans w a b ambient afterEnqueue afterKey,
      ((enqueuePerDeviceAndPeerRx ctx.slot).run w).run ambient = .ok ((-ENOSPC,a),afterEnqueue) →
      Inventory (c :: cs) a → Protected (c :: cs) loans a → QueueOwners (c :: cs) a →
      c.phase = .unpublished → c.packet.slot = ctx.slot → ctx.packet.peer = c.owner.slot →
      ((keypairPut (some ctx.packet.keypair) false).run a).run (enospcDecisions afterEnqueue) =
        .ok (((),b),afterKey) →
      ∃ v finalAmbient, ((finishSource ctx).run w).run ambient = .ok (((),v),finalAmbient) ∧
        Inventory cs v ∧ Protected cs loans v ∧ QueueOwners cs v ∧ packetAt v c.packet = none) := by
  refine ⟨?_,?_,?_⟩
  · intro id w d pid p cs loans ambient hd hp peek hi hq hs
    exact drop_selection id ambient hd hp peek hi hq hs
  · intro c cs loans w hi hc hr
    exact selected_nonfinal hi hc hr
  · intro ctx c cs loans w a b ambient afterEnqueue afterKey hr hi hs hq phase slot owner hk
    exact enospc_discharge ctx ambient afterEnqueue afterKey hr hi hs hq phase slot owner hk

/-- Kernel-checked refutation of the third conjunct of the withdrawn
original_rx_cleanup_credit_discharge. Positive credit does not bypass final
peer-release queue guards. This is an unrestricted local fixture, not an
initialized execution or a claim about Linux reachability. -/
theorem original_rx_cleanup_totality_refuted :
    ¬ (∀ (c : Carrier) (cs : Ledger) (loans : Reservations)
      (w a : WGWorld) (clock midway : Ambient) (pkt : RxPacket) (pid : PeerId) (flag : Bool),
      Inventory (c :: cs) w → Protected (c :: cs) loans w → c.phase = .selected →
      packetAt w c.packet = some pkt → pkt.peer = c.owner.slot → pkt.peer = pid →
      ((keypairPut (some pkt.keypair) false).run w).run clock = .ok (((),a),midway) →
      ∃ v last,
        ((do keypairPut (some pkt.keypair) false; peerPut (some pid)
             _ ← branch .rxPollFree flag; freeRxSkb c.packet.slot : WG.M Unit).run w).run clock =
          .ok (((),v),last) ∧
        Inventory cs v ∧ Protected cs loans v ∧ packetAt v c.packet = none) :=
  Queues.CleanupFindings.cleanup_discharge_totality_refuted

/-- The selected cleanup cut preserves inventory and funding when the actual
whole cleanup returns normally. No normal return is inferred from credit or
from a successful key payment alone. -/
theorem original_rx_cleanup_normal (c : Carrier) (cs : Ledger) (loans : Reservations)
    (w v : WGWorld) (ambient ambient' : Ambient) (pkt : RxPacket) (pid : PeerId) (flag : Bool)
    (hi : Inventory (c :: cs) w) (hs : Protected (c :: cs) loans w) (phase : c.phase = .selected)
    (hp : packetAt w c.packet = some pkt) (owner : pkt.peer = c.owner.slot) (guard : pkt.peer = pid)
    (hr : ((do keypairPut (some pkt.keypair) false; peerPut (some pid)
               _ ← branch .rxPollFree flag; freeRxSkb c.packet.slot : WG.M Unit).run w).run ambient =
          .ok (((),v),ambient')) :
    Inventory cs v ∧ Protected cs loans v ∧ packetAt v c.packet = none := by
  apply cleanup_discharge_normal hi hs phase hp owner ambient ambient'
  simpa only [cleanup_poll_guard _ _ _ _ guard] using hr

/-- Full original staged transmission preserves the same supplied RX inventory,
queue assignment and funded reservations on normal return. Nullable current-key
compatibility supplies the actual acquisition owner. The returned delta names
appended TX-batch/send-work occurrences and their exact reference balance; it is
not a TX packet-ownership invariant or an output key-compatibility frame. No
failed World, retrospective slack, or initialized conservation is asserted. -/
theorem original_staged_send_rx_protection (pid : PeerId) (w v : WGWorld) (ambient ambient' : Ambient)
    (cs : List Carrier) (loans : List Owner)
    (hc : CurrentCompatible pid w) (hi : Inventory cs w)
    (hq : QueueOwners cs w) (hp : Protected cs loans w)
    (hr : ((sendStagedPackets pid).run w).run ambient = .ok (((),v),ambient')) :
    ∃ delta, Handoff w v [] [] delta ∧ Inventory cs v ∧ QueueOwners cs v ∧
      Protected cs loans v ∧ Protected cs (loans ++ delta.owners) v := by
  obtain ⟨delta,hd⟩ := staged_send_handoff pid hc ambient ambient' hr
  exact ⟨delta,hd,hd.protect hi hq hp⟩

/-- Full original consumeDataDone, including promotion, staged send, timers and
actual lookup repayment, preserves the same supplied RX ledger on every normal
endpoint (Some and None). Only the packet key's nullable, validity-independent
owner compatibility is required; actual promotion supplies the staged call's
current-key condition. The source-derived queue/reference delta retains funded
handoffs. This local theorem does not itself supply Stack/IRQ or output-key
frames; the concrete Stack and normal-poll results appear below. Initialized
carrier conservation remains open; Stops have no claimed endpoint World. -/
theorem original_consume_data_done_rx_protection (pid : PeerId) (pkt : RxPacket)
    (endpoint : Endpoint) (w v : WGWorld) (ambient ambient' : Ambient) (result : Option (List UInt8))
    (cs : List Carrier) (loans : List Owner)
    (hc : KeyCompatible pid pkt.keypair w) (hi : Inventory cs w)
    (hq : QueueOwners cs w) (hp : Protected cs loans w)
    (hr : ((consumeDataDone pid pkt endpoint).run w).run ambient = .ok ((result,v),ambient')) :
    ∃ delta, Handoff w v [] [] delta ∧ Inventory cs v ∧ QueueOwners cs v ∧
      Protected cs loans v ∧ Protected cs (loans ++ delta.owners) v := by
  obtain ⟨delta,hd⟩ := consumeDataDone_handoff pid pkt endpoint hc ambient ambient' hr
  exact ⟨delta,hd,hd.protect hi hq hp⟩

/-- Actual Stack transmission (including normal negative errno) and batched
receive callbacks preserve the same supplied RX ledger and explicit funded
reservations. Concrete destination acquisition and repayment retain the exact
nonempty TX/send-work handoff delta. Nullable packet/current-key compatibility
is supplied and preserved separately. Bytes may belong to a held GRO entry
whose RX cell was already freed; no delivery-packet residency is required.
These are normal endpoint contracts, not initialized ownership or inbox arrival. -/
theorem original_stack_rx_protection (w v : World) (cs : List Carrier) (loans : List Owner)
    (hi : Inventory cs w.wg) (hq : QueueOwners cs w.wg) (hp : Protected cs loans w.wg)
    (hk : KeysCompatible w.wg) :
    (∀ family addr (packets : List WG.Packet) mtu ret,
      (liftWG (wgXmit family addr packets mtu)).run w=.ok (ret,v) →
      ∃ delta,Handoff w.wg v.wg [] [] delta ∧ Inventory cs v.wg ∧ QueueOwners cs v.wg ∧
        Protected cs loans v.wg ∧ Protected cs (loans++delta.owners) v.wg ∧ KeysCompatible v.wg) ∧
    (∀ packets : List (List UInt8),
      (packets.forM Leanux.Env.deliverInner).run w=.ok ((),v) →
      ∃ delta,Handoff w.wg v.wg [] [] delta ∧ Inventory cs v.wg ∧ QueueOwners cs v.wg ∧
        Protected cs loans v.wg ∧ Protected cs (loans++delta.owners) v.wg ∧ KeysCompatible v.wg) := by
  constructor
  · intro family addr packets mtu ret hr
    rw [Framing.liftWG_run] at hr
    cases he : ((wgXmit family addr packets mtu).run w.wg).run w.ambient with
    | error stop => simp [he,Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨value,g⟩,ambient⟩
      simp [he,Except.map] at hr
      rcases hr with ⟨rfl,rfl⟩
      obtain ⟨⟨delta,hd⟩,kv⟩ := wgXmit_protection family addr packets mtu hk he
      obtain ⟨iv,qv,pv,pd⟩ := hd.protect hi hq hp
      exact ⟨delta,hd,iv,qv,pv,pd,kv⟩
  · intro packets hr
    exact stackForM_protection packets hi hq hp hk hr

/-- A normal ORIGINAL poll removes exactly its observed allocation identities
from the supplied RX inventory; all other carriers and their reservations stay
funded, with exact queue ownership and nullable key/current compatibility.
Actual removal occurrences partition into named nondelivery or completed Stack
callbacks, with no selection/GRO/callback residual on normal return. The prior
journal contains lifetime accesses only, so subtraction uses this poll's fresh
removals. No caller/base reservation, peer-survival, totality, allocation-frontier
or initialized premise is added. Uncrypted-head normal exits may retain queued
carriers. Stops retain the existing prefix contracts but have no endpoint World;
whole admission/ring/lifecycle conservation and initialized identity remain open. -/
theorem original_poll_carrier_conservation (pid : PeerId) (budget : Nat) (w v : World) (n : Nat)
    (cs : List Carrier) (loans : List Owner) (prior : List Lifetimes.LifetimeEvent)
    (hi : Inventory cs w.wg) (hq : QueueOwners cs w.wg) (hp : Protected cs loans w.wg)
    (hk : KeysCompatible w.wg) (hr : (WG.rxPoll pid budget (fun packets=>packets.forM Leanux.Env.deliverInner)).run w=.ok (n,v)) :
    let h := (runPrefix (Queues.RxJoint.poll pid budget) w (Queues.RxJoint.seed prior)).2
    let rest := remaining cs (PollCarrier.removedPackets h)
    Inventory rest v.wg ∧ QueueOwners rest v.wg ∧ Protected rest loans v.wg ∧ KeysCompatible v.wg ∧
      (∀p∈PollCarrier.removedPackets h,packetAt v.wg p=none) ∧
      Queues.RxDisposition.Account none h ∧ Queues.RxDisposition.callbackPending h=[] ∧ Queues.RxDisposition.unentered h=[] ∧
      ((Queues.RxJoint.removalKeys h).map Prod.fst).Perm
        ((h.filterMap Queues.RxDisposition.nondeliveryKey).map Prod.fst ++
          (Queues.RxDisposition.completedEntries h).map (fun e=>e.tag.occurrence)) ∧
      (((h.filterMap Queues.RxDisposition.nondeliveryKey).map Prod.fst ++
          (Queues.RxDisposition.completedEntries h).map (fun e=>e.tag.occurrence))).Nodup := by
  obtain ⟨state,gone⟩ := PollCarrier.poll_normal pid budget w v n cs loans prior ⟨hi,hq,hp,hk⟩ hr
  have joint := (Queues.RxJoint.poll_erases pid budget w (Queues.RxJoint.seed prior)).trans hr
  exact ⟨state.inventory,state.queues,state.funded,state.keys,gone,
    Queues.RxDisposition.poll_normal_partition pid budget w v prior n joint⟩

/-- Whole original admission conserves the supplied carrier inventory, exact
queue ownership, funded reservations and nullable key compatibility. The same
actual admission witness is appended by the existing receipt observer before
its finish suffix. Enqueue success and EPIPE retain the queued carrier; ENOSPC
pays its key/peer references and frees it. No initialized reachability, positive
ring size, or peer-survival premise is asserted. This export is normal-only;
the separate lower consume_receipt lemma also covers a later stopped finish,
without assigning a World to that Stop. -/
theorem original_consume_data_carrier_conservation
    (cs : Ledger) (loans : Reservations) (w v : WGWorld) (ambient ambient' : Ambient)
    (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (hi : CarrierState cs loans w) (hf : Packets.Inv w)
    (hr : ((consumeData msg src ds).run w).run ambient=.ok (((),v),ambient')) :
    ∃ r, Consumption cs loans msg src ds w v ambient ambient' r ∧
      ∀ h : List (MaterialOrigin.Event RxOrigin.Receipt),
        runWGPrefix (RxOrigin.consume msg src ds) w ambient h =
          let next := (runWGPrefix (RxOrigin.admitRaw msg src ds) w ambient h).2 ++
            [.receipt (.admission msg src ds r)]
          match r.value with
          | none => (.ok (((),r.after),r.ambientAfter),next)
          | some ctx => runWGPrefix (finishObserved ctx) r.after r.ambientAfter next := by
  obtain ⟨r,hc⟩ := consume_normal hi hf ambient ambient' hr
  exact ⟨r,hc,fun h=>consume_receipt r hc.1 hc.2.1 hc.2.2.1 h⟩

/-- Normal original admission preserves the supplied stable RX boundary with
its exact outcome-selected carrier ledger. The separately existing ring
observer gives the actual appended physical journal for the same execution.
At a stable boundary, empty physical ring and cold resident NAPI flags force
both the carrier ledger and RX store empty, including ring size zero. This does
not establish initialized or all-prefix receive-pipeline conservation. -/
theorem original_consume_data_stable_rx
    (cs : Ledger) (loans : Reservations) (w : World)
    (epoch n : Nat) (h : List (Queues.Ring.Journal.Event SkbId))
    (hi : CarrierState cs loans w.wg) (hs : StableRx cs w.wg)
    (physical : Queues.RxRing.Inv epoch (PtrRing.init n) h w) :
    (∀ msg src ds v, Packets.Inv w.wg → (liftWG (consumeData msg src ds)).run w=.ok ((),v) →
      (∃r, StableConsumption cs loans msg src ds w.wg v.wg w.ambient v.ambient r) ∧
      let out := runPrefix (Queues.RxRing.consume msg src ds) w h
      out.1=.ok ((),v) ∧ (∃suffix,out.2=h++suffix) ∧
        Queues.RxRing.Safe (PtrRing.init n) out.2 ∧
        Queues.RxRing.Inv epoch (PtrRing.init n) out.2 v) ∧
    ((∀d,w.wg.dev=some d → d.decryptQueue.empty=true) →
      (∀(d : Device)(pid : PeerId)(p : Peer),w.wg.dev=some d → d.peers[pid]?=some p → p.napiScheduled=false) →
      cs=[] ∧ ∀(d : Device)(id : SkbId)(pkt : RxPacket),w.wg.dev=some d → d.rxSkbs[id]?≠some pkt) := by
  constructor
  · intro msg src ds v hf hr
    have native : ((consumeData msg src ds).run w.wg).run w.ambient =
        .ok (((),v.wg),v.ambient) := by
      rw [Framing.liftWG_run] at hr
      cases ha : ((consumeData msg src ds).run w.wg).run w.ambient with
      | error e => simp [ha,Except.map] at hr
      | ok out =>
        rcases out with ⟨⟨u,g⟩,ambient⟩
        simp only [ha,Except.map,Except.ok.injEq,Prod.mk.injEq] at hr
        rcases hr with ⟨_,rfl⟩
        cases u
        rfl
    exact ⟨consume_stable hi hf hs physical w.ambient v.ambient native,
      consume_ring_normal physical hr⟩
  · exact stable_drained hi hs physical


open Leanux Leanux.WG Queues.RxCredits Framing Lifetimes

/-- Every original fixture starts with empty receive carriers and a stable
boundary. This establishes initialization, not closure through the runner. -/
theorem original_rx_carrier_fixture (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w = wgStoreView (Runner.initialWG net bare)) :
    CarrierState [] [] w ∧ StableRx [] w ∧
      (w.dev = none ∨ NativeRxInv 3 (PtrRing.init MAX_QUEUED_PACKETS) [] w) :=
  ⟨carrier_initial net bare w same,stable_initial net bare w same,
    ring_initial net bare w same⟩

/-- The actual idle guard discharges the supplied stable carrier boundary;
no empty-inventory premise or endpoint after Stop is supplied. -/
theorem original_idle_guard_drains_rx (w v : World) (cs : Ledger) (loans : Reservations)
    (hi : CarrierState cs loans w.wg) (hs : StableRx cs w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) h w.wg)
    (run : Env.requireIdleDevice.run w = .ok ((),v)) :
    cs = [] ∧ ∀ (d : Device) (id : SkbId) (pkt : RxPacket),
      v.wg.dev = some d → d.rxSkbs[id]? ≠ some pkt :=
  idleDevice_empty w v cs loans hi hs physical run

/-- Completion has the same consequence when its actual input flags include
the decrypt ring. Omitting that caller fact would not justify draining RX. -/
theorem original_completion_guard_drains_rx (what : String) (flags : List Bool)
    (w v : World) (cs : Ledger) (loans : Reservations)
    (hi : CarrierState cs loans w.wg) (hs : StableRx cs w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) h w.wg)
    (ringFlag : ∀ d, w.wg.dev = some d → (!d.decryptQueue.empty) ∈ flags)
    (run : (Env.requireDrained what flags).run w = .ok ((),v)) :
    cs = [] ∧ ∀ (d : Device) (id : SkbId) (pkt : RxPacket),
      v.wg.dev = some d → d.rxSkbs[id]? ≠ some pkt :=
  requireDrained_empty what flags w v cs loans hi hs physical ringFlag run

/-- Native decrypt preparation keeps the same carriers and restores their
stable ring/head boundary. A published packet leaves its actual acquired peer
reservation outstanding for the later IRQ callback and payment. -/
theorem original_decrypt_preparation_carriers (cs : Ledger) (loans : Reservations)
    (w v : WGWorld) (result : Option PeerId) (ambient ambient' : Ambient)
    (hi : CarrierState cs loans w) (hs : StableRx cs w)
    (physical : NativeRxInv epoch (PtrRing.init n) h w)
    (run : ((Queues.RxWorkers.prepareSource).run w).run ambient = .ok ((result,v),ambient')) :
    DecryptCarrier.Prepared cs loans result v ∧ StableRx cs v :=
  ⟨DecryptCarrier.prepare_state hi ambient ambient' run,
    DecryptStable.prepare_stable hi hs physical ambient ambient' run⟩

/-- An explicitly source-owned reservation pays one actual release, including
final peer deletion, while the remaining receive obligations stay funded. -/
theorem original_rx_reservation_payment (cs : Ledger) (loans : Reservations) (o : Owner)
    (w v : WGWorld) (ambient ambient' : Ambient)
    (hi : CarrierState cs (o :: loans) w) (hs : StableRx cs w)
    (run : ((peerPut (some o.slot)).run w).run ambient = .ok (((),v),ambient')) :
    CarrierState cs loans v ∧ StableRx cs v :=
  reservation_payment_stable hi hs ambient ambient' run

/-- The exact timer callback either adds no reservation or appends one clear
work item backed by its actual entry peer get. Existing queue funding is not
inferred from membership or unexplained count slack. -/
theorem original_clear_timer_rx_reservation (pid : PeerId) (cs : Ledger) (loans : Reservations)
    (w v : WGWorld) (ambient ambient' : Ambient)
    (hi : ClearWork.Inv cs loans w)
    (run : ((expiredZeroKeyMaterial pid).run w).run ambient = .ok (((),v),ambient')) :
    ∃ added : Reservations,
      (added = [] ∨ ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧
        added = [⟨d.ifindex,pid,p.internalId⟩]) ∧
      ClearWork.Inv cs (added ++ loans) v ∧
      ClearWork.queueView v = (ClearWork.queueView w).map
        (fun q => (q.1,q.2 ++ added.map Owner.slot)) :=
  ClearWork.timer_normal hi ambient ambient' run

/-- The queued clear worker consumes its supplied queue reservation after the
original handshake/key-slot clearing. Slot aliases and absent keys are allowed;
failed getters or puts retain their original Stop behavior. -/
theorem original_clear_worker_rx_reservation (cs : Ledger) (loans : Reservations) (o : Owner)
    (w v : WGWorld) (ambient ambient' : Ambient)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (run : ((queuedExpiredZeroKeyMaterial o.slot).run w).run ambient = .ok (((),v),ambient')) :
    ClearWork.Inv cs loans v := ClearWork.queued_normal o hi ambient ambient' run

/-- Slot-bounded nullable compatibility is sufficient for actual session and
responder rotation. The session gets its self word from configured identity;
neither call assumes full affiliation, peer residency or a successful result. -/
theorem original_nullable_key_slot_preservation (pid : PeerId) (kid : KeypairId)
    (word : Option PeerId) (now : Bool) :
    Framing.Hoare (beginSession pid)
      (fun w => CurrentSlots.Inv w ∧ ConfiguredIdentity.Inv w) (fun _ => CurrentSlots.Inv) ∧
    Framing.Preserves CurrentSlots.Inv (receivedWithKeypair pid kid) ∧
    Framing.Preserves CurrentSlots.Inv (keypairCreate word) ∧
    Framing.Preserves CurrentSlots.Inv (keypairPut (some kid) now) ∧
    Framing.Preserves CurrentSlots.Inv (keypairsClear pid) :=
  ⟨CurrentSlots.beginSession_preserves pid,CurrentSlots.receivedWithKeypair_preserves pid kid,
    CurrentSlots.keypairCreate_preserves word,CurrentSlots.keypairPut_preserves (some kid) now,
    CurrentSlots.keypairsClear_preserves pid⟩

/-- An arbitrary local state can satisfy current compatibility and RX owner
bounds yet lose compatibility at the next fresh key allocation. This refutes
that insufficient local invariant; it is not an initialized mirror finding. -/
theorem local_current_compatibility_requires_frontier (ambient : Ambient) :
    ∃ v, ((keypairCreateCore (some 1)).run CurrentKeys.danglingWorld).run ambient =
        .ok ((0,v),ambient) ∧
      OwnerBounds.Carrier CurrentKeys.danglingWorld ∧
      CurrentsCompatible CurrentKeys.danglingWorld ∧ ¬ CurrentsCompatible v :=
  CurrentKeys.actual_core_counterexample ambient

/-- Receive completion and the actual product Stack retain every surviving
peer's NAPI bit. Separate inventory, queue and ring contracts supply the other
stable-boundary facts; this bit frame alone is not poll conservation. -/
theorem original_completion_stack_napi_bits (pid : PeerId) (pkt : RxPacket)
    (endpoint : Endpoint) (packets : List (List UInt8)) (initial : PeerId → Option Bool) :
    Framing.Preserves (Queues.NapiFrames.Retained initial) (consumeDataDone pid pkt endpoint) ∧
    Framing.Preserves (fun w : World => Queues.NapiFrames.Retained initial w.wg)
      (packets.forM Env.deliverInner) :=
  ⟨Queues.NapiFrames.consumeDataDone_preserves pid pkt endpoint initial,
    Queues.NapiFrames.stack_preserves packets initial⟩

/-- Actual receive completion preserves the supplied stable receive ledger.
It may delete a peer; all surviving cold heads retain their packet-state fact. -/
theorem original_completion_stable_rx (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (cs : Ledger) (w v : WGWorld) (ambient ambient' : Ambient)
    (hs : StableRx cs w)
    (run : ((consumeDataDone pid pkt endpoint).run w).run ambient = .ok ((result,v),ambient')) :
    StableRx cs v := stable_consumeDataDone pid pkt endpoint hs ambient ambient' run

/-- The concrete Stack callback preserves the stable receive boundary even
when it produces reply traffic. Nullable key compatibility supplies the same
existing TX handoff frame used by the carrier proof. -/
theorem original_stack_stable_rx (packets : List (List UInt8)) (cs : Ledger) (w v : World)
    (hs : StableRx cs w.wg) (hk : KeysCompatible w.wg)
    (run : (packets.forM Env.deliverInner).run w = .ok ((),v)) : StableRx cs v.wg :=
  stable_stack packets hs hk run


open Leanux Leanux.WG Queues Queues.RxCredits Framing Logged Lifetimes

/-- The original poll restores a stable carrier boundary, subtracting exactly
its own seeded removal journal. The supplied reservations survive unchanged;
this is local normal-endpoint conservation, not initialized runner closure. -/
theorem original_poll_stable_rx (pid : PeerId) (budget : Nat) (w v : World) (n : Nat)
    (initial : Ledger) (loans : Reservations) (prior : List LifetimeEvent)
    (hi : CarrierState initial loans w.wg) (hs : StableRx initial w.wg)
    (run : (WG.rxPoll pid budget (fun packets => packets.forM Env.deliverInner)).run w = .ok (n,v)) :
    let h := (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed prior)).2
    CarrierState (remaining initial (PollCarrier.removedPackets h)) loans v.wg ∧
      StableRx (remaining initial (PollCarrier.removedPackets h)) v.wg ∧
      ∀ p ∈ PollCarrier.removedPackets h, packetAt v.wg p = none :=
  poll_normal_stable pid budget w v n initial loans prior hi hs run

/-- Callback contracts retain exact ledger/history cuts and the publication
loan through IRQ. The normal iteration restores stability for the resulting
ledger; its ended, yielded and continued paths are all the actual source paths. -/
theorem original_decrypt_iteration_stable_rx
    (softirq irq : RxHistory.Obs Unit) (afterItem : RxHistory.Obs Bool)
    (RS RI : Ledger → DecryptIteration.Journal → World → Ledger → DecryptIteration.Journal → World → Prop)
    (RA : Ledger → DecryptIteration.Journal → World → Bool → Ledger → DecryptIteration.Journal → World → Prop)
    (soft : DecryptIteration.Advances softirq RS) (interrupt : DecryptIteration.Advances irq RI)
    (softPhysical : ∀ w h v k, DecryptIteration.Physical w →
      runPrefix softirq w h = (.ok ((),v),k) → DecryptIteration.Physical v)
    (after : ∀ cs loans w h v k more, DecryptIteration.Stable cs loans w →
      runPrefix afterItem w h = (.ok (more,v),k) →
      ∃ ds, RA cs h w more ds k v ∧ DecryptIteration.Stable ds loans v)
    (hi : DecryptIteration.Stable cs loans w) (physical : DecryptIteration.Physical w)
    (run : runPrefix (workerIterPrefix .decryptWorker none
      (RxWorkers.decryptWith Origins.HistoryAdapters.prepare
        (fun pid => RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))) softirq irq)
      afterItem) w h = (.ok (result,v),k)) :
    ∃ ds, DecryptIteration.Stable ds loans v ∧
      DecryptIteration.IterationPath softirq irq afterItem RS RI RA cs loans w h result ds v k :=
  DecryptIteration.iteration_normal softirq irq afterItem RS RI RA soft interrupt softPhysical after hi physical run

/-- Actual read/release/creation and receive admission preserve all three
bounded nullable key slots. No freshness, residency or non-NULL premise is
introduced into these operations. -/
theorem original_nullable_key_slots_admission (kinds : List IndexKind) (index : Nat)
    (peer : Option PeerId) (key : Key) (psk : Option Key) (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves CurrentSlots.Inv (indexLookup kinds index) ∧
    Preserves CurrentSlots.Inv (peerPut peer) ∧
    Preserves CurrentSlots.Inv (peerCreate key psk) ∧
    Preserves CurrentSlots.Inv (consumeData msg src ds) ∧
    Preserves CurrentSlots.Inv (wgReceive msg src) :=
  ⟨CurrentSlots.indexLookup_preserves kinds index,CurrentSlots.peerPut_preserves peer,
    CurrentSlots.peerCreate_preserves key psk,CurrentSlots.consumeData_preserves msg src ds,
    CurrentSlots.wgReceive_preserves msg src⟩

/-- The original queued initiation and staged-send paths retain all three
slots through actual key/peer release, batch publication and queue coalescing. -/
theorem original_nullable_key_slots_traffic (pid : PeerId) (retry : Bool) :
    Preserves CurrentSlots.Inv (sendQueuedHandshakeInitiation pid retry) ∧
    Preserves CurrentSlots.Inv (sendStagedPackets pid) :=
  ⟨CurrentSlots.sendQueuedHandshakeInitiation_preserves pid retry,
    CurrentSlots.sendStagedPackets_preserves pid⟩

/-- Constructing/sending a handshake preserves existing receive obligations.
The queued worker additionally pays its supplied source-owned reservation. -/
theorem original_send_worker_rx_reservation (pid : PeerId) (o : Owner)
    (cs : Ledger) (loans : Reservations) (w v : WGWorld) (a b : Ambient)
    (hi : CarrierState cs (o :: loans) w) (hs : StableRx cs w)
    (run : ((handshakeSendWorker o.slot).run w).run a = .ok (((),v),b)) :
    Preserves (fun g => CarrierState cs loans g ∧ StableRx cs g) (sendHandshakeInitiation pid) ∧
    CarrierState cs loans v ∧ StableRx cs v :=
  ⟨SendWork.initiation_preserves pid,SendWork.worker_normal o hi hs a b run⟩

/-- A flush chooses one funded owner from the actual clear queue and pays it.
Every later duplicate remains in both the queue and the reservation ledger. -/
theorem original_clear_flush_rx_reservations (owners loans : Reservations) (cs : Ledger)
    (w v : WGWorld) (epoch pid : Nat) (a b : Ambient)
    (hi : ClearWork.Inv cs (owners ++ loans) w)
    (queue : ClearWork.queueView w = some (epoch,owners.map Owner.slot))
    (present : pid ∈ owners.map Owner.slot)
    (run : ((runFlushedClearWork pid).run w).run a = .ok (((),v),b)) :
    ∃ o restOwners, WorkReservations.Selected owners pid o restOwners ∧
      ClearWork.Inv cs (restOwners ++ loans) v ∧
      ClearWork.queueView v = some (epoch,restOwners.map Owner.slot) :=
  ClearWork.flushed_normal hi queue present a b run

/-- Ordered queue accounting begins at the actual timer's acquisition. A
coalesced enqueue repays it; an accepted enqueue appends that stamped owner. -/
theorem original_clear_timer_queue_accounts (owners loans : Reservations) (cs : Ledger)
    (w v : WGWorld) (epoch pid : Nat) (a b : Ambient)
    (hi : ClearWork.Inv cs (owners ++ loans) w)
    (queue : ClearWork.queueView w = some (epoch,owners.map Owner.slot))
    (run : ((expiredZeroKeyMaterial pid).run w).run a = .ok (((),v),b)) :
    ∃ added : Reservations,
      (added = [] ∨ ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧
        added = [⟨d.ifindex,pid,p.internalId⟩]) ∧
      ClearWork.Inv cs ((owners ++ added) ++ loans) v ∧
      ClearWork.queueView v = some (epoch,(owners ++ added).map Owner.slot) :=
  ClearWork.timer_accounts hi queue a b run

/-- Receive completion retains the three bounded nullable slots through
promotion, timer updates, staged transmission, source lookup and release. -/
theorem original_nullable_key_slots_completion (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves CurrentSlots.Inv (consumeDataDone pid pkt endpoint) :=
  CurrentSlots.consumeDataDone_preserves pid pkt endpoint

/-- The concrete NAPI, inline and IRQ callers preserve the stable receive
boundary relative to the actual incoming history. Only their fresh removal
records subtract carriers, and every supplied reservation remains funded. -/
theorem original_napi_stable_rx (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (NapiCarrier.At initial loans before) (fun _ => True) RxHistory.napiSoftirq ∧
    PrefixPreserves (NapiCarrier.At initial loans before) (fun _ => True) RxHistory.pollScheduledInline ∧
    PrefixPreserves (NapiCarrier.At initial loans before) (fun _ => True) RxHistory.napiIrqExit :=
  ⟨NapiCarrier.softirq_preserves initial loans before,NapiCarrier.inline_preserves initial loans before,
    NapiCarrier.irq_preserves initial loans before⟩

/-- Both recorded-unit and default-head clear dispatch select an occurrence
from the actual queue before spending its explicitly supplied reservation. -/
theorem original_environment_clear_rx_reservations (owners loans : Reservations) (cs : Ledger)
    (w v : World) (epoch : Nat) (hi : ClearWork.Inv cs (owners ++ loans) w.wg)
    (queue : ClearWork.queueView w.wg = some (epoch,owners.map Owner.slot))
    (run : Env.runOneClearWorker.run w = .ok ((),v)) :
    ∃ pid o restOwners, WorkReservations.Selected owners pid o restOwners ∧
      ClearWork.Inv cs (restOwners ++ loans) v.wg ∧
      ClearWork.queueView v.wg = some (epoch,restOwners.map Owner.slot) :=
  ClearWork.runOneClearWorker_normal w v hi queue run

/-- Native send flush retains the pending guard and clears or restores the
pending bit from the actual remaining queue, then pays one selected owner. -/
theorem original_send_flush_rx_reservations (owners loans : Reservations) (cs : Ledger)
    (w v : WGWorld) (epoch pid : Nat) (a b : Ambient)
    (hi : SendDispatch.Inv cs (owners ++ loans) w)
    (queue : SendDispatch.queueView w = some (epoch,owners.map Owner.slot))
    (present : pid ∈ owners.map Owner.slot)
    (run : ((runFlushedSendWork pid).run w).run a = .ok (((),v),b)) :
    ∃ o restOwners, WorkReservations.Selected owners pid o restOwners ∧
      SendDispatch.Inv cs (restOwners ++ loans) v ∧
      SendDispatch.queueView v = some (epoch,restOwners.map Owner.slot) :=
  SendDispatch.flushed_normal hi queue present a b run

/-- Actual environment send dispatch proves queue membership before the
native pending guard and selected payment; the remaining order is exact. -/
theorem original_environment_send_rx_reservations (owners loans : Reservations) (cs : Ledger)
    (w v : World) (epoch : Nat) (hi : SendDispatch.Inv cs (owners ++ loans) w.wg)
    (queue : SendDispatch.queueView w.wg = some (epoch,owners.map Owner.slot))
    (run : Env.runOneSendWorker.run w = .ok ((),v)) :
    ∃ pid o restOwners, WorkReservations.Selected owners pid o restOwners ∧
      SendDispatch.Inv cs (restOwners ++ loans) v.wg ∧
      SendDispatch.queueView v.wg = some (epoch,restOwners.map Owner.slot) :=
  SendEnvironment.runOneSendWorker_normal w v hi queue run

/-- The actual decrypt iteration has no outstanding callback premise. It
restores stable funded carriers and a physical ring witness, retaining the
exact concrete receive path; the physical ring witness remains separate. -/
theorem original_concrete_decrypt_stable_rx (cs : Ledger) (loans : Reservations)
    (w v : World) (result : IterResult) (history : DecryptIteration.Journal)
    (hi : DecryptIteration.Stable cs loans w) (physical : DecryptIteration.Physical w)
    (run : (WG.decryptIter Env.napiSoftirq Env.napiIrqExit
      (Env.condResched .decryptWorker)).run w = .ok (result,v)) :
    let k := (runPrefix RxHistory.decryptIteration w history).2
    ∃ ds, DecryptIteration.Stable ds loans v ∧ DecryptIteration.Physical v ∧
      DecryptConcrete.Path cs loans w history result ds v k :=
  DecryptConcrete.native_normal hi physical run history


open Queues.RxCredits.PollCarrier

open BaseCreation in
/-- Actual creation adds its initial stamped reference to the funded base list. -/
theorem original_base_creation_account (key : Key) (psk : Option Key)
    (hi : CarrierState cs (owners ++ loans) w) (hs : StableRx cs w)
    (configured : ConfiguredIdentity.Inv w) (hd : w.dev = some d)
    (list : d.peerList = owners.map Owner.slot) (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a = .ok ((.ok pid,v),b)) :
    pid = d.nextPeer ∧
      CarrierState cs ((owners ++ [owner w d]) ++ loans) v ∧ StableRx cs v ∧
      v.dev.map Device.peerList = some ((owners ++ [owner w d]).map Owner.slot) ∧
      pid ∉ d.peerList :=
  BaseCreation.peerCreate_accounts key psk hi hs configured hd list a b run

open BaseRemoval in
/-- Detaching a peer retains every base reservation until its actual payment. -/
theorem original_base_detachment_account (pid : PeerId)
    (hi : CarrierState cs (owners ++ loans) w) (hs : StableRx cs w)
    (listed : w.dev.map Device.peerList = some (owners.map Owner.slot))
    (a b : Ambient) (hr : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) :
    CarrierState cs (live owners pid ++ (detached owners pid ++ loans)) v ∧
      StableRx cs v ∧ v.dev.map Device.peerList = some ((live owners pid).map Owner.slot) :=
  BaseRemoval.peerMakeDead_accounts pid hi hs listed a b hr

open BaseRemoval in
/-- Bulk removal saves the actual ordered base list after clearing the trie. -/
theorem original_bulk_removal_saved_account (hi : CarrierState cs (owners ++ loans) w) (hs : StableRx cs w)
    (listed : w.dev.map Device.peerList = some (owners.map Owner.slot))
    (a b : Ambient) (hr : (entry.run w).run a = .ok ((dead,v),b)) :
    dead = owners.map Owner.slot ∧ CarrierState cs (owners ++ loans) v ∧
      StableRx cs v ∧ v.dev.map Device.peerList = some dead :=
  BaseRemoval.entry_normal hi hs listed a b hr

open DurableHolders in
/-- The original fixture starts with a complete empty durable-holder account. -/
theorem original_durable_holders_initial (net bare : Bool) : Boundary [] [] (Runner.initialWG net bare) :=
  DurableHolders.boundary_initial net bare

open DurableHolders in
/-- Receive completion retains its actual new TX/send holders and all supplied obligations. -/
theorem original_completion_durable_holders {holders : DurableHolders} {c : Carrier}
    (hi : holders.Funded cs loans w) (hs : StableRx stable w)
    (stored : packetAt w c.packet = some pkt) (guard : pkt.peer = pid)
    (a b : Ambient)
    (run : ((consumeDataDone pid pkt ep).run w).run a = .ok ((result,v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧
      (holders.absorb delta).Funded cs loans v ∧ StableRx stable v :=
  DurableHolders.consume_normal hi hs stored guard a b run

open DurableHolders in
/-- Concrete Stack replies retain complete durable-holder alignment and funding. -/
theorem original_stack_durable_holders {holders : DurableHolders} {w v : World}
    (packets : List (List UInt8)) (hi : holders.Funded cs loans w.wg)
    (hs : StableRx stable w.wg)
    (run : (packets.forM Leanux.Env.deliverInner).run w = .ok ((),v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧
      (holders.absorb delta).Funded cs loans v.wg ∧ StableRx stable v.wg :=
  DurableHolders.stack_normal packets hi hs run

open DurableHolders in
/-- The original poll consume cut retains new holders with its actual selected-carrier phase. -/
theorem original_poll_consume_durable_holders (initial : Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) (guard : pkt.peer = pid) :
    PrefixEnsures
      (Accounted (fun ls h w => Live initial ls pid skb stamp pkt h w ∧ StableAt initial h w) loans)
      (fun _ => True) (consume pid n skb stamp pkt ep)
      (fun _ => Accounted (fun ls h w => Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans) :=
  DurableHolders.consume_accounted initial loans pid n skb stamp pkt ep guard

open DurableHolders in
/-- The original GRO receive cut retains new holders before selected-packet cleanup. -/
theorem original_poll_gro_durable_holders (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (g : Gro) (entry : Entry) :
    PrefixPreserves
      (Accounted (fun ls h w => Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans)
      (fun _ => True) (receive g entry) :=
  DurableHolders.receive_bare_accounted initial loans pid skb stamp g entry

open DurableHolders in
/-- The original GRO flush retains the actual remaining ledger and every new holder. -/
theorem original_poll_flush_durable_holders (front initial : Ledger) (loans : Reservations) (g : Gro) :
    PrefixPreserves (Accounted (fun ls h w => Context front initial ls h w ∧ StableAt initial h w) loans)
      (fun _ => True) (flushAll g) :=
  DurableHolders.flush_context_accounted front initial loans g

open TxReservation in
/-- The actual DEAD transmit step debits one batch and pays its supplied owner, allowing final deletion. -/
theorem original_dead_tx_batch_account (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (queue : ∃ p, resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .dead w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ClearWork.Inv cs loans v ∧
      (∀ id ∈ first :: rest, TxDisposition.txPackets v id = none) ∧ v.sent = w.sent ∧
      (∀ other, other ≠ o.slot → TxDisposition.txQueues v other = TxDisposition.txQueues w other) ∧
      (∀ before after, TxDisposition.txQueues w o.slot = some before →
        TxDisposition.txQueues v o.slot = some after → after.all = before.all.tail) :=
  TxReservation.dead_step_account o first rest hi queue head a b hr

open TxReservation in
/-- The actual TX freshness check retains acquired handoff reservations in the combined budget. -/
theorem original_tx_freshness_reservations (pid : PeerId) (hi : CarrierState cs loans w)
    (hs : StableRx cs w) (a b : Ambient)
    (hr : ((keepKeyFresh pid).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧
      CarrierState cs (loans ++ delta.owners) v ∧ StableRx cs v :=
  TxReservation.keepKeyFresh_funded pid hi hs a b hr

open DumpReservation in
/-- Dump completion pays the supplied optional cursor after its actual hasWg record. -/
theorem original_dump_cursor_payment (ctx : DumpCtx) (old : Option Owner)
    (cursor : ctx.nextPeer = old.map Owner.slot)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (run : ((wgGetDeviceDone ctx).run w).run a = .ok (((),v),b)) :
    ClearWork.Inv cs loans v :=
  DumpReservation.done_normal ctx old cursor hi a b run

open DumpReservation in
/-- The literal dump replacement acquires the new cursor before paying the old, including aliasing. -/
theorem original_dump_cursor_exchange (ctx : DumpCtx) (old : Option Owner) (nextCursor : Option PeerId) (done : Bool)
    (cursor : ctx.nextPeer = old.map Owner.slot)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (run : ((replaceSource ctx nextCursor done).run w).run a = .ok (((),v),b)) :
    ∃ next : Option Owner,
      next.map Owner.slot = (if done then none else nextCursor) ∧
      (∀ o, next = some o → ∃ d p, w.dev=some d ∧ d.peers[o.slot]?=some p ∧
        o=⟨d.ifindex,o.slot,p.internalId⟩ ∧ 0<p.refcount) ∧
      ClearWork.Inv cs (next.toList ++ loans) v :=
  DumpReservation.replace_normal ctx old nextCursor done cursor hi a b run


open Leanux Leanux.WG Queues Queues.RxCredits Framing Logged Lifetimes
open Queues.RxJoint Queues.RxCredits.PollCarrier
open WorkReservations

open DurableHolders in
/-- The actual poll retains all durable holders and subtracts its exact removal suffix. -/
theorem original_funded_poll (pid : PeerId) (budget : Nat) (w v : World) (n : Nat)
    (initial : Ledger) (loans : Reservations) (prior : List LifetimeEvent)
    (hi : Boundary initial loans w.wg)
    (hr : (WG.rxPoll pid budget (fun packets => packets.forM Leanux.Env.deliverInner)).run w = .ok (n,v)) :
    let h := (runPrefix (poll pid budget) w (seed prior)).2
    Boundary (remaining initial (removedPackets h)) loans v.wg ∧
      ∀ p ∈ removedPackets h, packetAt v.wg p = none :=
  DurableHolders.poll_normal_funded pid budget w v n initial loans prior hi hr

open HolderDecryptHistory in
/-- The actual decrypt iteration retains its funded holder account and physical ring witness. -/
theorem original_funded_decrypt_iteration (hi : DurableHolders.Boundary cs loans w.wg) (physical : Queues.RxCredits.DecryptIteration.Physical w)
    (run : (WG.decryptIter Env.napiSoftirq Env.napiIrqExit
      (Env.condResched .decryptWorker)).run w = .ok (result,v)) (h : Queues.RxCredits.DecryptIteration.Journal) :
    let k := (runPrefix RxHistory.decryptIteration w h).2
    (∃ suffix, k = h ++ suffix ∧ DurableHolders.Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧
      Queues.RxCredits.DecryptIteration.Physical v :=
  HolderDecryptHistory.native_normal hi physical run h

open HolderAdmission in
/-- The complete holder account accompanies the exact admission and enqueue receipt. -/
theorem original_funded_admission {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w) (a b : Ambient)
    (run : ((consumeData msg src ds).run w).run a = .ok (((),v),b)) :
    holders.Aligned v ∧
      ∃ receipt, StableConsumption cs (holders.owners ++ loans) msg src ds w v a b receipt :=
  HolderAdmission.consume_funded hi stable fresh physical a b run

open DurableHolders in
/-- One actual send dispatch pays its selected ordered holder occurrence. -/
theorem original_send_worker_holders {holders : DurableHolders} (w v : World)
    (hi : holders.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (hr : Env.runOneSendWorker.run w = .ok ((),v)) :
    ∃ pid o rest, Selected holders.send pid o rest ∧
      (holders.withoutSend rest).Funded cs loans v.wg ∧ StableRx cs v.wg :=
  DurableHolders.runOneSendWorker_funded w v hi stable hr

open DurableHolders in
/-- One actual clear dispatch pays its selected ordered holder occurrence. -/
theorem original_clear_worker_holders {holders : DurableHolders} (w v : World)
    (hi : holders.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (hr : Env.runOneClearWorker.run w = .ok ((),v)) :
    ∃ pid o rest, Selected holders.clear pid o rest ∧
      (holders.withoutClear rest).Funded cs loans v.wg ∧ StableRx cs v.wg :=
  DurableHolders.runOneClearWorker_funded w v hi stable hr

open DurableHolders in
/-- The actual bounded drain retains all holders except the work occurrences it pays. -/
theorem original_work_drain_holders (upTo : Option PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (hr : ((drainHandshakeSendWq upTo).run w).run a = .ok (((),v),b)) :
    DuringWork holders cs loans v :=
  DurableHolders.drain_normal upTo hi stable a b hr

open DurableHolders in
/-- Timer stopping and its conditional drain retain supplied caller loans. -/
theorem original_timer_stop_holders (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (hr : ((timersStop pid).run w).run a = .ok (((),v),b)) :
    DuringWork holders cs loans v :=
  DurableHolders.timersStop_normal pid hi stable a b hr

open DumpReservation in
/-- A full dump chunk derives cursor alignment from its actual serialization walk. -/
theorem original_dump_serialization_funding (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) (old : Option Owner)
    (cursor : ctx.nextPeer=old.map Owner.slot)
    (hi : ClearWork.Inv cs (old.toList ++ loans) w) (a b : Ambient)
    (run : ((wgGetDeviceDump ctx prevSeq skb).run w).run a=.ok ((result,v),b)) :
    ∃ next : Option Owner, result.ctx.nextPeer=next.map Owner.slot ∧
      ClearWork.Inv cs (next.toList ++ loans) v :=
  DumpReservation.dump_normal ctx prevSeq skb old cursor hi a b run

open DurableHolders in
/-- The original dump start establishes active-cursor accounting through its source guards. -/
theorem original_dump_start_holders {h : DurableHolders} (fd : Nat) (ref : DeviceRef)
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((netlinkDumpStart fd ref).run w).run a = .ok (((),v),b)) :
    ∃ next : Option Owner, (h.withCursor fd next).Funded cs loans v ∧ StableRx cs v :=
  DurableHolders.netlinkDumpStart_funded fd ref hi stable a b run

open DurableHolders in
/-- The original receive call retains or pays its socket cursor and all other holders. -/
theorem original_dump_recv_holders {h : DurableHolders} (fd : Nat)
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((netlinkRecvmsg fd).run w).run a = .ok ((result,v),b)) :
    ∃ next : Option Owner, (h.withCursor fd next).Funded cs loans v ∧ StableRx cs v :=
  DurableHolders.netlinkRecvmsg_funded fd hi stable a b run

open TxReservation in
/-- The actual encrypted TX step debits one batch and retains its send-only freshness delta. -/
theorem original_crypted_tx_account (o : Owner) (first : SkbId) (rest : List SkbId)
    (hi : ClearWork.Inv cs (o :: loans) w)
    (queue : ∃ p, resident w o = some p ∧ p.txQueue.all.head? = some (first :: rest))
    (head : TxDisposition.HeadState first .crypted w) (a b : Ambient)
    (hr : ((txStep o.slot).run w).run a = .ok ((result,v),b)) :
    result = true ∧ ∃ delta : HandoffDelta,
      delta.tx = [] ∧ ClearWork.Inv cs (loans ++ delta.owners) v ∧
      sendView v = (sendView w).map (· ++ delta.send.map Owner.slot) ∧
      (∀ other, other ≠ o.slot → handoffTxView v other = handoffTxView w other) ∧
      (∀ before after, handoffTxView w o.slot = some before →
        handoffTxView v o.slot = some after → after = before.tail) :=
  TxReservation.crypted_step_account o first rest hi queue head a b hr

open TxReservation in
/-- The send-only completion handoff is anchored at the original completion entry. -/
theorem original_tx_completion_handoff (pid : PeerId) (item : List SkbId)
    (hi : ClearWork.Inv cs loans w) (a b : Ambient)
    (hr : ((createDataDone pid item).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ delta.tx = [] ∧
      ClearWork.Inv cs (loans ++ delta.owners) v :=
  TxReservation.createDataDone_handoff pid item hi a b hr

/-- All three original NAPI dispatch forms retain the same fixed accounting cut. -/
theorem original_funded_napi (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) RxHistory.napiSoftirq ∧
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) RxHistory.pollScheduledInline ∧
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) RxHistory.napiIrqExit :=
  ⟨HolderNapi.softirq_preserves initial loans before,HolderNapi.inline_preserves initial loans before,
    HolderNapi.irq_preserves initial loans before⟩


open Leanux Leanux.WG Queues Queues.RxCredits Framing Logged Lifetimes

/-- The actual creation call publishes only its source-funded base occurrence. -/
theorem original_peer_creation_holders (key : Key) (psk : Option Key)
    {holders : DurableHolders} (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (configured : ConfiguredIdentity.Inv w) (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    match result with
    | .error _ => holders.Funded cs loans v ∧ StableRx cs v
    | .ok pid => ∃ d, w.dev = some d ∧ pid = d.nextPeer ∧
        (HolderCreation.addBase holders (BaseCreation.owner w d)).Funded cs loans v ∧ StableRx cs v :=
  HolderCreation.peerCreate_funded key psk hi stable configured a b run

/-- Bulk removal pays the saved base occurrences in order through its actual drains. -/
theorem original_bulk_retirement_holders {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : (peerRemoveAll.run w).run a = .ok (((),v),b)) :
    DurableHolders.DuringWork (holders.withoutBase []) cs loans v :=
  DurableHolders.peerRemoveAll_funded hi stable a b run

/-- Every normal TX step retains idle holders or pays its actual selected batch. -/
theorem original_full_tx_step_holders {holders : DurableHolders} (pid : PeerId)
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) :
    (result = false ∧ holders.Funded cs loans v ∧ StableRx cs v) ∨
    (result = true ∧ ∃ chosen rest delta,
      DurableHolders.TxSelected holders.tx pid chosen rest ∧ chosen.item ≠ [] ∧ delta.tx = [] ∧
      ((holders.withoutTx rest).absorb delta).Funded cs loans v ∧ StableRx cs v) :=
  DurableHolders.txStep_funded pid hi stable a b run

/-- Native TX publication acquires and repays its own temporary reference. -/
theorem original_tx_publication_holders (item : List SkbId) (state : PacketState)
    {holders : DurableHolders} (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (a b : Ambient)
    (run : ((enqueuePerPeerTx item state).run w).run a = .ok (((),v),b)) :
    holders.Funded cs loans v ∧ StableRx cs v :=
  DurableHolders.enqueuePerPeerTx_funded item state hi stable a b run

/-- The complete original bounded dump caller changes only its selected cursor account. -/
theorem original_whole_dump_holders (ref : DeviceRef) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((wgGetDevice ref).run w).run a = .ok ((result,v),b)) :
    DurableHolders.DuringDump holders 7 cs loans v :=
  DurableHolders.wgGetDevice_funded ref hi stable a b run

/-- All three actual dump dispatcher arms retain their supplied complete account. -/
theorem original_dump_dispatch_holders (ref : DeviceRef) {holders : DurableHolders}
    (w v : World) (hi : holders.Funded cs loans w.wg) (stable : StableRx cs w.wg) :
    ((dispatch (.wgGet ref)).run w = .ok (result,v) → DurableHolders.DuringDump holders 7 cs loans v.wg) ∧
    ((dispatch (.wgGetStart ref)).run w = .ok (result,v) → DurableHolders.DuringDump holders DUMP_FD cs loans v.wg) ∧
    ((dispatch .wgGetRecv).run w = .ok (result,v) → DurableHolders.DuringDump holders DUMP_FD cs loans v.wg) :=
  ⟨DurableHolders.dispatchGet_funded ref w v hi stable,
    DurableHolders.dispatchStart_funded ref w v hi stable,
    DurableHolders.dispatchRecv_funded w v hi stable⟩

/-- Encryption and its actual NAPI callback retain the same removal suffix and ring witness. -/
theorem original_funded_encrypt_iteration (hi : DurableHolders.Boundary cs loans w.wg)
    (physical : Queues.RxCredits.DecryptIteration.Physical w)
    (run : (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)).run w = .ok (result,v))
    (h : List RxHistory.Event) :
    let k := (runPrefix RxHistory.encryptIteration w h).2
    (∃ suffix, k = h ++ suffix ∧ DurableHolders.Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧
      Queues.RxCredits.DecryptIteration.Physical v :=
  HolderEncrypt.native_funded hi physical run h

/-- The actual session supplies endpoint key facts from the stated entry bounds. -/
theorem original_session_holder_account (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (configured : ConfiguredIdentity.Inv w) (owners : OwnerBounds.Carrier w)
    (slots : CurrentSlots.Inv w) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    holders.Funded cs loans v ∧ StableRx cs v ∧ ConfiguredIdentity.Inv v ∧
      OwnerBounds.Carrier v ∧ CurrentSlots.Inv v :=
  SessionCarrier.beginSession_funded pid hi stable configured owners slots a b run

/-- Single-peer removal pays its unique supplied live base occurrence. -/
theorem original_single_peer_retirement (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (unique : (holders.base.map Owner.slot).Nodup)
    (present : pid ∈ holders.base.map Owner.slot) (a b : Ambient)
    (run : ((peerRemove (some pid)).run w).run a = .ok (((),v),b)) :
    DurableHolders.DuringWork (holders.withoutBase (BaseRemoval.live holders.base pid)) cs loans v :=
  DurableHolders.peerRemove_some_funded pid hi stable unique present a b run

/-- The actual zero-key timer adds only the reservation acquired in its source. -/
theorem original_zero_key_timer_holders (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((expiredZeroKeyMaterial pid).run w).run a = .ok (((),v),b)) :
    ∃ added : Reservations,
      (added = [] ∨ ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧
        added = [⟨d.ifindex,pid,p.internalId⟩]) ∧
      (HolderTimers.addClear holders added).Funded cs loans v ∧ StableRx cs v :=
  HolderTimers.expiredZero_funded pid hi stable a b run

/-- The new-handshake timer retains its endpoint-reset cut and funded queue delta. -/
theorem original_new_handshake_timer_holders (pid : PeerId) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((expiredNewHandshake pid).run w).run a = .ok (((),v),b)) :
    ∃ u middle delta,
      ((clearPeerEndpointSrc pid).run w).run a = .ok (((),u),middle) ∧
      ((sendQueuedHandshakeInitiation pid false).run u).run middle = .ok (((),v),b) ∧
      Handoff u v [] [] delta ∧ (holders.absorb delta).Funded cs loans v ∧ StableRx cs v :=
  HolderTimers.expiredNew_funded pid hi stable a b run

/-- The actual TX activation includes crypt-ahead and its NAPI removal suffix. -/
theorem original_tx_activation_holders (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (activation : Activation)
    (worker : activation.worker = .txWorker) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.activationIteration activation) :=
  HolderTxHistory.activationIteration_preserves initial loans before activation worker

/-- The actual initiation consumer accounts for its optional acquired reference. -/
theorem original_initiation_holder_loan (msg : List UInt8) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((consumeInitiation msg).run w).run a=.ok ((result,v),b)) :
    HandshakeLoans.FundedResult holders cs loans result v :=
  HandshakeLoans.consumeInitiation_funded msg hi stable a b run

/-- The actual response consumer accounts for its optional acquired reference. -/
theorem original_response_holder_loan (msg : List UInt8) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((consumeResponse msg).run w).run a=.ok ((result,v),b)) :
    HandshakeLoans.FundedResult holders cs loans result v :=
  HandshakeLoans.consumeResponse_funded msg hi stable a b run

/-- Each original timer callback retains a complete funded account, including new work. -/
theorem original_timer_callback_account (pid : PeerId) (timer : PeerTimer) :
    Preserves (DurableHolders.Boundary cs loans) (timerCallback pid timer) :=
  HolderTimers.callback_boundary pid timer

/-- The whole original TX activation uses its committed removal suffix. -/
theorem original_tx_run_account (a : Activation) (worker : a.worker = .txWorker)
    (hi : DurableHolders.Boundary cs loans w.wg)
    (run : (Env.Activation.run a).run w = .ok ((),v)) (h : List RxHistory.Event) :
    let k := (runPrefix (RxHistory.activationRun a) w h).2
    ∃ suffix, k = h ++ suffix ∧ DurableHolders.Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg :=
  HolderTxActivation.activationRun_normal a worker hi run h

/-- A whole nonreceive activation retains its account and physical ring witness. -/
theorem original_nonreceive_run_account (a : Activation) (other : a.worker ≠ .receiveWorker)
    (funded : DurableHolders.Boundary cs loans w.wg) (physical : Queues.RxCredits.DecryptIteration.Physical w)
    (run : (Env.Activation.run a).run w = .ok ((),v)) (h : List RxHistory.Event) :
    (∃ suffix, (runPrefix (RxHistory.activationRun a) w h).2 = h ++ suffix ∧
      DurableHolders.Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧ Queues.RxCredits.DecryptIteration.Physical v :=
  HolderScheduler.run_normal a other funded physical run h

/-- Actual nonreceive dispatch uses the selected activation and the same removal history. -/
theorem original_nonreceive_dispatch_account (worker : Worker) (other : worker ≠ .receiveWorker)
    (funded : DurableHolders.Boundary cs loans w.wg) (physical : Queues.RxCredits.DecryptIteration.Physical w)
    (run : (Env.dispatch worker).run w = .ok (result,v)) (h : List RxHistory.Event) :
    (∃ suffix, (runPrefix (RxHistory.dispatch worker) w h).2 = h ++ suffix ∧
      DurableHolders.Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧ Queues.RxCredits.DecryptIteration.Physical v :=
  HolderScheduler.dispatch_normal worker other funded physical run h

/-- Whole scheduling retains the exact remaining receive-worker contract explicitly. -/
theorem original_schedule_account_conditional (stack : Option Worker) (h : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv cs loans h) (fun _ => True) Origins.HistoryAdapters.receiveIteration)
    (funded : DurableHolders.Boundary cs loans w.wg) (physical : Queues.RxCredits.DecryptIteration.Physical w)
    (run : (Env.schedule stack).run w = .ok ((),v)) :
    (∃ suffix, (runPrefix (RxHistory.schedule stack) w h).2 = h ++ suffix ∧
      DurableHolders.Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧ Queues.RxCredits.DecryptIteration.Physical v :=
  HolderScheduler.schedule_normal stack h receive funded physical run

/-- Every deferred constructor uses concrete timers and workers, with the receive contract explicit. -/
theorem original_deferred_account_conditional (call : EnvDeferredCall) {result : call.Result} (h : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv cs loans h) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration)
    (funded : DurableHolders.Boundary cs loans w.wg) (physical : Queues.RxCredits.DecryptIteration.Physical w)
    (run : call.original.run w = .ok (result,v)) :
    (∃ suffix, (runPrefix (RxHistory.deferred call) w h).2 = h ++ suffix ∧
      DurableHolders.Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧
      Queues.RxCredits.DecryptIteration.Physical v :=
  HolderTimerPhysical.deferred_normal call h receive funded physical run

/-- Actual creation retains unique base slots and public-key target membership. -/
theorem original_creation_base_coherence (key : Key) (psk : Option Key) {h : DurableHolders}
    (hi : BaseCoherence.Inv w) (funded : h.Funded cs loans w) (configured : ConfiguredIdentity.Inv w)
    (a b : Ambient) (run : ((peerCreate key psk).run w).run a=.ok ((result,v),b)) : BaseCoherence.Inv v :=
  BaseCoherence.creation_preserves key psk hi funded configured a b run

/-- The actual lookup and removal pay the separate base and caller references. -/
theorem original_lookup_removal_accounts (key : Key) (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    {h : DurableHolders} (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (remove : (flags &&& WGPEER_F_REMOVE_ME != 0)=true) (a middle b : Ambient)
    (lookup : ((pubkeyLookup key).run w).run a=.ok ((some pid,u),middle))
    (update : ((Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run middle=.ok ((result,v),b)) :
    result=0 ∧ DurableHolders.DuringWork (h.withoutBase (BaseRemoval.live h.base pid)) cs loans v :=
  BaseLookupRemoval.lookup_update_remove key attrs flags psk hi stable coherent configured remove a middle b lookup update

/-- Original allowed-IP configuration retains the complete holder account. -/
theorem original_allowedip_holder_account (pid : PeerId) (ip : AllowedIpAttrs) :
    Preserves (DurableHolders.Boundary cs loans) (setAllowedip pid ip) :=
  HolderAllowedIps.setAllowedip_boundary pid ip

/-- At the real session entry, explicit key facts suffice for the final caller payment. -/
theorem original_response_session_payment (o : Owner) (msg : List UInt8) :
    Hoare (HandshakeReceive.responseSession o.slot >>= fun _ => HandshakeReceive.finishSelected (some o.slot) msg)
      (fun w => DurableHolders.Boundary cs (o::loans) w ∧ ConfiguredIdentity.Inv w ∧
        OwnerBounds.Carrier w ∧ CurrentSlots.Inv w)
      (fun _ => DurableHolders.Boundary cs loans) :=
  HandshakeReceive.response_paid o msg

/-- The complete actual configuration tail pays its acquired caller loan. -/
theorem original_configuration_tail_payment (attrs : PeerAttrs) (o : Owner) :
    Hoare (Configuration.peerConfigTailSource attrs (some o.slot) o.slot)
      (DurableHolders.Boundary cs (o::loans)) (fun _ => DurableHolders.Boundary cs loans) :=
  HolderConfigTail.tail attrs o

/-- Actual lookup and either update arm retain the sourced complete account. -/
theorem original_lookup_update_account (key : Key) (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    {holders : DurableHolders} (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (ambient middle final : Ambient)
    (lookup : ((pubkeyLookup key).run w).run ambient = .ok ((some pid,u),middle))
    (run : ((Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run middle =
      .ok ((result,v),final)) : DurableHolders.Boundary cs loans v :=
  HolderConfigUpdate.lookup_update key attrs flags psk hi stable coherent configured ambient middle final lookup run

/-- Actual single and bulk removal preserve the structural base invariant. -/
theorem original_removal_base_coherence (peer : Option PeerId) :
    Preserves BaseCoherence.Inv (peerRemove peer) ∧ Preserves BaseCoherence.Inv peerRemoveAll :=
  ⟨BaseCoherence.peerRemove_preserves peer,BaseCoherence.peerRemoveAll_preserves⟩

/-- Complete actual peer updates retain list/table coherence, including deletion. -/
theorem original_update_base_coherence (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Preserves BaseCoherence.Inv (Configuration.peerConfigUpdateSource attrs peer flags psk pid) :=
  BaseCoherence.update_preserves attrs peer flags psk pid

/-- All original handshake consumers retain three-slot compatibility. -/
theorem original_handshake_slot_compatibility (msg : List UInt8) :
    Preserves CurrentSlots.Inv (consumeInitiation msg) ∧
    Preserves CurrentSlots.Inv (consumeResponse msg) ∧
    Preserves CurrentSlots.Inv (cookieMessageConsume msg) :=
  ⟨HandshakeSlots.consumeInitiation msg,HandshakeSlots.consumeResponse msg,HandshakeSlots.cookieMessageConsume msg⟩

/-- The concrete Stack callback closes the original poll's slot contract. -/
theorem original_stack_poll_slot_compatibility (pid : PeerId) (budget : Nat) :
    Preserves (fun w : World => CurrentSlots.Inv w.wg)
      (WG.rxPoll pid budget (fun packets => packets.forM Env.deliverInner)) :=
  CurrentSlots.poll_stack pid budget

/-- Original crypt iterations retain slots on the same arbitrary incoming history. -/
theorem original_crypt_iteration_slot_compatibility :
    PrefixPreserves (fun _ w => CurrentSlots.Inv w.wg) (fun _ => True) RxHistory.decryptIteration ∧
    PrefixPreserves (fun _ w => CurrentSlots.Inv w.wg) (fun _ => True) RxHistory.encryptIteration :=
  ⟨CurrentSlots.decryptIteration_observed,CurrentSlots.encryptIteration_observed⟩

/-- Session accounting and auxiliary ownership facts share one actual observed run. -/
theorem original_session_auxiliary_account (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (Origins.HistoryAdapters.session pid) :=
  HolderAuxiliary.session_preserves initial loans before pid

/-- Actual response acquisition preserves both its attributed loan and sourced entry facts. -/
theorem original_response_funded_entry (msg : List UInt8) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (entry : HandshakeEntry.Entry w) (a b : Ambient)
    (run : ((consumeResponse msg).run w).run a = .ok ((result,v),b)) :
    HandshakeLoans.FundedResult holders cs loans result v ∧ HandshakeEntry.Entry v :=
  HandshakeEntry.response_funded msg hi stable entry a b run

/-- Creation funds its published base and the actual subsequent caller loan separately. -/
theorem original_creation_caller_account (key : Key) (psk : Option Key) {holders : DurableHolders}
    (funded : holders.Funded cs loans w) (stable : StableRx cs w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (a middle b : Ambient)
    (create : ((peerCreate key psk).run w).run a=.ok ((.ok pid,u),middle))
    (acquire : ((peerGet pid).run u).run (CounterWindow.record middle .peerCreateErr false)=.ok (((),v),b)) :
    ∃ d, w.dev=some d ∧ pid=d.nextPeer ∧
      (HolderCreation.addBase holders (BaseCreation.owner w d)).Funded cs (BaseCreation.owner w d::loans) v ∧
      StableRx cs v ∧ BaseCoherence.Inv v ∧ ConfiguredIdentity.Inv v ∧ pid ∈ BaseCoherence.slots v :=
  CreationLoan.creation_acquire key psk funded stable coherent configured a middle b create acquire

/-- Original TX execution preserves three-slot compatibility with its real reschedule callback. -/
theorem original_transmit_slot_compatibility (pid : PeerId) :
    PrefixPreserves (fun _ w => CurrentSlots.Inv w.wg) (fun _ => True)
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  CurrentSlots.TxSource.tx_observed pid

/-- The original scheduler shares one complete account and owner history; its remaining receive contract uses that same domain. -/
theorem original_schedule_auxiliary_conditional (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (stack : Option Worker)
    (receive : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      Origins.HistoryAdapters.receiveIteration) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (RxHistory.schedule stack) :=
  HolderAuxScheduler.schedule_preserves initial loans before receive stack

/-- The actual admission/enqueue receipt chooses the new ledger while retaining every durable charge. -/
theorem original_admission_selected_account {holders : DurableHolders}
    (funded : holders.Funded cs loans w) (stable : StableRx cs w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w) (a b : Ambient)
    (run : ((consumeData msg src ds).run w).run a=.ok (((),v),b)) :
    ∃ r next, AdmissionOutcome.Outcome cs next msg src ds w v a b r ∧
      holders.Funded next loans v ∧ StableRx next v :=
  AdmissionOutcome.consume funded stable fresh physical a b run

/-- Source receipts and their complete ledger updates are unique on the same actual native entry. -/
theorem original_admission_ledger_unique
    (left : AdmissionOutcome.Outcome cs xs msg src ds w v a b r)
    (right : AdmissionOutcome.Outcome cs ys msg src ds w v a b s) : r=s ∧ xs=ys :=
  AdmissionOutcome.unique left right

/-- An independently supplied source receipt reconstructs the exact original consumption call. -/
theorem original_admission_receipt_execution
    (outcome : AdmissionOutcome.Outcome cs next msg src ds w v a b r) :
    ((consumeData msg src ds).run w).run a=.ok (((),v),b) :=
  AdmissionOutcome.source outcome

/-- The complete original peer command discharges lookup/creation loans and retains base coherence on every normal return. -/
theorem original_peer_command_account (attrs : PeerAttrs) :
    Hoare (WG.setPeerCmd attrs)
      (fun w => DurableHolders.Boundary cs loans w ∧ BaseCoherence.Inv w ∧ ConfiguredIdentity.Inv w)
      (fun _ w => DurableHolders.Boundary cs loans w ∧ BaseCoherence.Inv w) :=
  SetPeerBoundary.setPeerCmd attrs

/-- Guarded original device creation preserves the account and initializes a new physical ring only when a device is created. -/
theorem original_device_creation_account :
    Preserves (DurableHolders.Boundary cs loans) wgCreate ∧
    Preserves HolderDeviceCreate.OptionalPhysical wgCreate :=
  ⟨HolderDeviceCreate.create,HolderDeviceCreate.create_physical⟩

/-- The optional receipt observer preserves the original return and exact audit projection, including stopped prefixes. -/
theorem original_admission_journal_projection (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (w : World) (h : List RxHistory.Event) (hi : AuditInv (RxHistory.auditHistory h) w) :
    ((runPrefix (AdmissionJournal.observe msg src ds) w h).1,
      (runPrefix (AdmissionJournal.observe msg src ds) w h).2.filterMap RxHistory.auditEvent) =
    ((runPrefix (RxHistory.mixed (liftWGObserver (consumeDataPrefix msg src ds))) w h).1,
      (runPrefix (RxHistory.mixed (liftWGObserver (consumeDataPrefix msg src ds))) w h).2.filterMap RxHistory.auditEvent) :=
  AdmissionJournal.original_audit msg src ds w h hi

/-- A normal rich observation selects one actual admission occurrence and the same funded ledger; the runner does not yet use this splice. -/
theorem original_admission_funded_occurrence
    (run : runPrefix (AdmissionJournal.observe msg src ds) w h = (.ok ((),v),k))
    (hi : DurableHolders.Boundary cs loans w.wg) (fresh : Packets.Inv w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) ringHistory w.wg) :
    ∃ receipt next front tail,
      AdmissionOutcome.Outcome cs next msg src ds w.wg v.wg w.ambient v.ambient receipt ∧
      k=h++front++[.rx (.admission msg src ds receipt)]++tail ∧
      DurableHolders.Boundary next loans v.wg :=
  AdmissionJournal.normal run hi fresh physical

/-- The unchanged original admission observer establishes a source transition and its funded ledger; neither is an output premise. -/
theorem original_dynamic_admission_step
    (run : runPrefix (AdmissionPath.consume msg src ds) w h = (.ok ((),v),k))
    (hi : DurableHolders.Boundary cs loans w.wg) (fresh : Packets.Inv w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) ringHistory w.wg) :
    ∃ next, AdmissionPath.Step cs w h next v k ∧ DurableHolders.Boundary next loans v.wg :=
  AdmissionPath.admission_step run hi fresh physical

/-- The original after-MAC dispatcher retains cookie/drop early returns and pays only a source-selected peer. -/
theorem original_handshake_dispatch_account (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (mac : MacState) :
    Hoare (Cookies.afterMac msg src loaded mac) (HandshakeResponse.Input cs loans)
      (fun _ => DurableHolders.Boundary cs loans) :=
  HandshakeAfterMac.afterMac msg src loaded mac

/-- The complete original handshake receiver obtains all session entry facts from its input and retains the funded account on every normal return. -/
theorem original_handshake_receive_account (msg : List UInt8) (src : SkbSource) :
    Hoare (receiveHandshakePacket msg src) (HandshakeResponse.Input cs loans)
      (fun _ => DurableHolders.Boundary cs loans) :=
  HandshakeReception.receive msg src


open Leanux Leanux.WG Leanux.Proofs Leanux.Proofs.Logged
open Framing Lifetimes Queues Queues.RxCredits

/-- The original observed receive worker retains one complete funded account,
physical ring and auxiliary domain, including its safe stopped histories. -/
theorem original_receive_worker_account (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      Origins.HistoryAdapters.receiveIteration :=
  HandshakeWorker.iteration_preserves initial loans before

/-- Every recorded scheduler branch now uses the concrete receive worker;
there is no remaining receive-callback premise. The entry account is explicit. -/
theorem original_schedule_auxiliary_account (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (stack : Option Worker) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (RxHistory.schedule stack) :=
  HandshakeWorker.schedule initial loans before stack

/-- Nested rescheduling retains that same combined invariant and incoming journal. -/
theorem original_nested_auxiliary_account (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (worker : Worker) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe (RxHistory.nestedResched worker) :=
  HandshakeWorker.nestedResched initial loans before worker

/-- The next actual command receives its configured identity from this command's run. -/
theorem original_peer_command_complete_entry (attrs : PeerAttrs) :
    Preserves (DeviceBoundary.Entry cs loans) (WG.setPeerCmd attrs) := DeviceBoundary.command attrs

/-- The actual device peer-list stage preserves one account through every command and error exit. -/
theorem original_device_peers_account (attrs : DeviceAttrs) :
    Preserves (DeviceBoundary.Entry cs loans) (Configuration.devicePeersSource attrs) := DeviceBoundary.peers attrs

/-- Shutdown retains supplied carriers and the real physical alternative through actual work drains. -/
theorem original_device_stop_account :
    Preserves (fun w => DurableHolders.Boundary cs loans w ∧ HolderDeviceCreate.OptionalPhysical w) wgStop ∧
    Preserves (fun w => DurableHolders.Boundary cs loans w ∧ HolderDeviceCreate.OptionalPhysical w) wgDown :=
  ⟨HolderStopPhysical.stop,HolderStopPhysical.down⟩

/-- The original fixture establishes all local entry facts for both flags;
absent-device cases carry no fabricated physical ring. -/
theorem original_holder_fixture (net bare : Bool) (w : World)
    (same : wgStoreView w.wg=wgStoreView (Runner.initialWG net bare)) :
    DurableHolders.Boundary [] [] w.wg ∧ HolderDeviceCreate.OptionalPhysical w.wg ∧
      OwnerChecks.Inv [] w ∧ CurrentSlots.Inv w.wg ∧ BaseCoherence.Inv w.wg :=
  HolderInitial.initial net bare w same

/-- A new accounting cut retains exactly the ledger selected by the old cut's actual removal suffix. -/
theorem original_holder_rebase (hi : HolderAuxiliary.Inv cs loans before h w) :
    ∃ suffix, h=before++suffix ∧
      HolderAuxiliary.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans h h w :=
  HolderInitial.rebase hi

end Leanux.Proofs.WG.DeliveryOrder
