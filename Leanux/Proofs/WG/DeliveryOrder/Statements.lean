import Leanux.Proofs.WG.Queues.FullRing
import Leanux.Proofs.WG.Queues.Enqueue
import Leanux.Proofs.WG.Queues.PrevQueue
import Leanux.Proofs.WG.Queues.RxCompletionFrame
import Leanux.Proofs.WG.Queues.RxPollOrder
import Leanux.Proofs.WG.Queues.RxPollGroOrder
import Leanux.Proofs.WG.Queues.SelectedGro
import Leanux.Proofs.WG.Queues.RxPollProjection
import Leanux.Proofs.WG.Queues.RxPollProvenance

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

end Leanux.Proofs.WG.DeliveryOrder
