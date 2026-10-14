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
    (callback : List (List UInt8) → M Unit) :
    Logged.ErasesPrefix (Queues.rxPollRemovals pid budget callback) (rxPoll pid budget callback) :=
  Queues.rxPollRemovals_erases pid budget callback

/-- The outer poll body removes an initial segment of the current resident's exact
entry queue, in order, even when a later helper or callback stops. Events are
emitted after the original two-getter drop. Repeated entry IDs remain possible;
callback-internal removals are outside this log. Successful batch callbacks
must explicitly retain surviving queues. This theorem does not assert
packet ownership or stack delivery. -/
theorem original_poll_removal_prefix (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → M Unit) (w : World) (cell : Queues.RxQueueCell)
    (hcallback : ∀ bytes, Queues.RetainsRx (callback bytes))
    (hc : Queues.rxQueues w pid = some cell) :
    Queues.RemovalPrefix cell.queue.all
      (Logged.runPrefix (Queues.rxPollRemovals pid budget callback) w []).2 :=
  Queues.rxPollRemovals_prefix pid budget callback w cell hcallback hc

/-- At the outer poll's original two-getter drop site, normal completion
appends exactly its one skb ID, while a failed update appends nothing. -/
theorem original_poll_drop_observation (pid : PeerId) (id : SkbId)
    (w : World) (h : List SkbId) :
    Logged.runPrefix (Queues.dropRxPrefix pid id) w h =
      match (Queues.dropRxQueue pid).run w with
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
      match (consumeDataDone pid pkt endpoint).run w with
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
theorem original_gro_held_then_normal (callback : List (List UInt8) → M Unit)
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
    Queues.RetainsRx (packets.forM Leanux.Env.deliverInner) :=
  Queues.stackForM_rxQueues packets

/-- With the concrete stack callback, outer removals are a prefix of the
initial resident's exact entry queue for every normal or stopped poll.
The initial cell identifies that queue; no callback frame, live-peer or
packet-ID-validity assumption is required from the caller. -/
theorem original_poll_concrete_removal_prefix (pid : PeerId) (budget : Nat)
    (w : World) (cell : Queues.RxQueueCell) (hc : Queues.rxQueues w pid = some cell) :
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
    (w : World) (cell : Queues.RxQueueCell) (hc : Queues.rxQueues w pid = some cell) :
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
theorem original_tx_admission_not_full (pid : PeerId) (item : List SkbId) (w v : World)
    (hr : (enqueuePerDeviceAndPeer pid item).run w = .ok (0, v)) :
    ∃ r, Queues.encryptRing w = some r ∧ r.full = false :=
  Queues.enqueue_success_free pid item w v hr

/-- The same independent successful-admission guard for original RX enqueue,
without queue geometry, ownership or packet-ID validity assumptions. -/
theorem original_rx_admission_not_full (id : SkbId) (w v : World)
    (hr : (enqueuePerDeviceAndPeerRx id).run w = .ok (0, v)) :
    ∃ r, Queues.decryptRing w = some r ∧ r.full = false :=
  Queues.enqueue_rx_success_free id w v hr


/-- The complete original RX enqueue and consumeData retain their exact
result, World on success and Stop on failure, for every input and history.
The ring log records admission/refusal only at the corresponding source cut. -/
theorem original_rx_ring_entry_erasure (id : SkbId) (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Logged.ErasesPrefix (Queues.RxRing.enqueue id) (enqueuePerDeviceAndPeerRx id) ∧
      Logged.ErasesPrefix (Queues.RxRing.consume msg src ds) (consumeData msg src ds) :=
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
    Logged.ErasesPrefix (Queues.TxRing.enqueue pid item) (enqueuePerDeviceAndPeer pid item) ∧
      Logged.ErasesPrefix (Queues.TxRing.create pid item) (createData pid item) :=
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
behavior for arbitrary Worlds and callback implementations. Softirq precedes
the ring read; checksum remains between its original guards and later reads. -/
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

end Leanux.Proofs.WG.DeliveryOrder
