import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriverProjection
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeSend
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeReceive
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeData
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeScheduler
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDeferred
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDecoration
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeLifecycle
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeEnvironment
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDeviceConfiguration
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeInitialized
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeSessionEffects
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeJointWorker
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeNativeFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeOrigins
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeObservation
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeRemovalProjection
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeRemovalErasure
import Leanux.Proofs.WG.HandshakeSecurity.ResponderPriorConfirmation
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverInitialized
import Leanux.Proofs.WG.HandshakeSecurity.ResponderJournalConfirmation
import Leanux.Proofs.WG.HandshakeSecurity.TimestampDriverProjection
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDeviceFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDeferred
import Leanux.Proofs.WG.HandshakeSecurity.ResponderGlobalFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderStackFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderLabels
import Leanux.Proofs.WG.HandshakeSecurity.ResponderRetention
import Leanux.Proofs.WG.HandshakeSecurity.Frames
import Leanux.Proofs.WG.HandshakeSecurity.ReplayClaims
import Leanux.Proofs.WG.HandshakeSecurity.StopClaims
import Leanux.Proofs.WG.HandshakeSecurity.Increasing
import Leanux.Proofs.WG.HandshakeSecurity.ConsumerRefusal
import Leanux.Proofs.WG.HandshakeSecurity.WorkerClaims
import Leanux.Proofs.WG.HandshakeSecurity.HistoryClaims
import Leanux.Proofs.WG.HandshakeSecurity.ResponseReplay
import Leanux.Proofs.WG.HandshakeSecurity.AllocationClaims
import Leanux.Proofs.WG.HandshakeSecurity.SessionReplay
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationPollClaims
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationH1
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationInitialized
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationUnique
import Leanux.Proofs.WG.HandshakeSecurity.StagingSelectionClaims
import Leanux.Proofs.WG.HandshakeSecurity.StagingSelectionFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderStagingFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderNativeClaims
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveKeepalive
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTimerCalls
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchivePoll
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveStack
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveWorker
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveScheduler
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTimers
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTraffic
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveDeviceConfig
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveInitialized
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderDriver

/-! Native T4 replay and T5 confirmation claims. Timestamp and exchange
histories are transported from initialization; native C2 dependencies remain
visible. Responder encryption exclusion and the remaining campaign composition
are separate obligations; these statements do not claim campaign completion. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- The original initiation consumer emits only actual timestamp writes whose
received value exceeds the value used by its timestamp comparison. Its exact
normal result or Stop is preserved, and receipts before Stop remain covered.
This is a native-call claim, not an initialized retained-peer history theorem. -/
theorem original_initiation_timestamp_receipts (msg : List UInt8)
    (w : WGWorld) (a : Ambient) :
    (runWGPrefix (consumeObserved msg) w a []).1 =
      ((consumeInitiation msg).run w).run a ∧
    SoundReceipts (runWGPrefix (consumeObserved msg) w a []).2 := by
  refine ⟨consume_erases msg w a [], ?_⟩
  obtain ⟨_, _, safe, _⟩ := consume_sound msg w a [] (by intro r h; cases h)
  exact safe

/-- Every recorded initiation timestamp write changes exactly the timestamp
in the retained peer's handshake projection, preserving its allocation identity,
handshake material, tag and key slots at that write. -/
theorem original_initiation_written_projection (msg : List UInt8)
    (w : WGWorld) (a : Ambient) (r : TimestampReceipt)
    (occurs : r ∈ (runWGPrefix (consumeObserved msg) w a []).2) :
    r.Newer ∧ ∃ p,
      peerView r.execution.before r.peer = some (handshakeView p) ∧
      peerView r.execution.after r.peer =
        some { handshakeView p with timestamp := r.received } := by
  obtain ⟨valid, newer⟩ := (original_initiation_timestamp_receipts msg w a).2 r occurs
  exact ⟨newer, receipt_written_view r valid⟩

/-- The original timestamp-write arm cannot overwrite peer state with a value
that fails its strict comparison. This local guard statement excludes the
surrounding consumer's reference release and is not full replay rejection. -/
theorem original_stale_timestamp_arm (pid : PeerId) (old t : List UInt8)
    (w : WGWorld) (a : Ambient) (stale : memcmp t old ≠ .gt) :
    ((timestampStep pid old t).run w).run a =
      .ok (((), w), CounterWindow.record a .consumeNewerTimestamp false) :=
  stale_timestamp_step pid old t w a stale

/-- A stale decrypted initiation timestamp takes the original refusal suffix,
returns no peer and preserves every surviving peer's handshake and freshness
projection. Cleanup may delete a peer. This source-cut claim starts at the
actual comparison; transport from initialized execution remains separate. -/
theorem original_stale_initiation_suffix (msg e ck hash t : List UInt8)
    (peer : Option PeerId) (pid : PeerId) (p : Peer) (w v : WGWorld)
    (a b : Ambient) (result : Option PeerId)
    (stale : memcmp t p.latestTimestamp ≠ .gt)
    (run : ((checkedWith (fun a => a) timestampStep msg e ck hash t peer pid p).run w).run a =
      .ok ((result, v), b)) :
    result = none ∧ RetainsHandshake w v :=
  checked_stale_result msg e ck hash t peer pid p w v a b result stale run

/-- Every committed timestamp write in the original initiation consumer is
strictly newer than that peer's actual pre-write timestamp, including receipts
before a later Stop. This local native-call result has no supplied coherence
or freshness invariant; initialized lifetime history remains a separate claim. -/
theorem original_initiation_timestamp_increases (msg : List UInt8)
    (w : WGWorld) (a : Ambient) :
    IncreasingReceipts (runWGPrefix (consumeObserved msg) w a []).2 := by
  obtain ⟨_, _, safe, _⟩ := consume_increasing msg w a [] (by intro r h; cases h)
  exact safe

/-- A normally rejected original initiation cannot change a surviving peer's
handshake material, freshness state or key slots. This includes the real
public-key lookup and reference cleanup; deletion is permitted. The result is
local to the consumer, so queue, load and outer receive effects are separate. -/
theorem original_initiation_refusal_retains (msg : List UInt8) (w v : WGWorld)
    (a b : Ambient)
    (run : ((consumeInitiation msg).run w).run a = .ok ((none, v), b)) :
    RetainsHandshake w v := original_none_retains msg w v a b run

/-- Every timestamp receipt committed by the original handshake receive worker
records a real write strictly newer than that peer's actual prior timestamp.
The observer preserves the worker's full normal result or Stop and retains
receipts before failure. This is worker transport, not initialized lifetime
history or a claim about unobserved fixture operations. -/
theorem original_worker_timestamp_increases (w : WGWorld) (a : Ambient) :
    (runWGPrefix Worker.observed w a []).1 = (receiveStep.run w).run a ∧
    IncreasingReceipts (runWGPrefix Worker.observed w a []).2 := by
  refine ⟨Worker.erases w a [], ?_⟩
  obtain ⟨_, _, safe, _⟩ := Worker.increasing w a [] (by intro r h; cases h)
  exact safe

/-- A sequence of original initiation-consumer calls retains a chronological
history: each committed write is strictly newer than the preceding timestamp
for that allocation identity, and every surviving peer agrees with the replay
of those writes. Receipts before a later Stop remain covered. This starts from
the supplied native state; fixture initialization and intervening allocation,
worker and driver operations are separate transport obligations. -/
theorem original_consumer_sequence_timestamp_history (messages : List (List UInt8))
    (w : WGWorld) (a : Ambient) :
    (runWGPrefix (consumeManyObserved messages) w a []).1 =
      ((consumeMany messages).run w).run a ∧
    TimestampHistory w (runWGPrefix (consumeManyObserved messages) w a []).2 ∧
    ∀ v b, (runWGPrefix (consumeManyObserved messages) w a []).1 = .ok (((), v), b) →
      TimestampCoherent w (runWGPrefix (consumeManyObserved messages) w a []).2 v := by
  refine ⟨consumeMany_erases messages w a [], ?_⟩
  obtain ⟨_, _, safe, post⟩ := consumeMany_history w messages w a [] (TimestampInv.initial w)
  refine ⟨safe, ?_⟩
  intro v b run
  have run' : (runPrefix ((consumeManyObserved messages).run w) a []).1 = .ok (((), v), b) := run
  rw [run'] at post
  exact post.2

/-- Under the explicitly named H1 response-edge contract, any sequence of
original response consumers accepts at most one response for each peer until
another operation refreshes its initiation state. Exact native results and
Stops are preserved, including completed receipts before Stop. This sequence
contains no initiation creation, peer allocation or intervening driver work. -/
theorem original_response_sequence_no_repeat (H1 : H1ResponseEdges)
    (messages : List (List UInt8)) (w : WGWorld) (a : Ambient) :
    (runWGPrefix (ResponseReplay.sequence messages) w a []).1 =
      ((ResponseReplay.original messages).run w).run a ∧
    ResponseReplay.Safe (runWGPrefix (ResponseReplay.sequence messages) w a []).2 := by
  refine ⟨ResponseReplay.sequence_erases messages w a [], ?_⟩
  obtain ⟨_, _, safe, _⟩ := ResponseReplay.sequence_preserves H1 messages w a []
    (ResponseReplay.initial w)
  exact safe

/-- The original session allocation site executes at most once, and every
normally completed session has exactly one successful allocation receipt.
The receipt is emitted before derivation, zeroing and publication, so it remains
visible after any later Stop. This source-boundary result does not assert final
key residency, slot coherence or uniqueness across different exchanges. -/
theorem original_session_allocation_boundary (pid : PeerId) (w : WGWorld) (a : Ambient) :
    (runWGPrefix (Installation.observed pid) w a []).1 = ((beginSession pid).run w).run a ∧
    Installation.Evidence [] (runWGPrefix (Installation.observed pid) w a []).2 ∧
    ∀ v b, ((beginSession pid).run w).run a = .ok ((true, v), b) →
      ∃ kp, Installation.Allocated [] (some kp) (runWGPrefix (Installation.observed pid) w a []).2 := by
  refine ⟨Installation.erases pid w a [], ?_⟩
  obtain ⟨_, _, safe, post⟩ := Installation.evidence [] pid w a [] rfl
  refine ⟨safe, ?_⟩
  intro v b run
  have run' : (runPrefix ((Installation.observed pid).run w) a []).1 = .ok ((true, v), b) :=
    (Installation.erases pid w a []).trans run
  rw [run'] at post
  exact post.2 rfl

/-- Under the explicitly named H1 session-effect contract, repeated original
session calls without handshake recreation complete at most once per peer.
Each completed receipt increments the allocation counter once, and a normally
returned sequence's total increment equals its number of completions. Receipts
for earlier completed calls remain covered after Stop; a stopped call's own
allocation is covered by the separate allocation-boundary observer. -/
theorem original_session_sequence_consumes_once (H1 : H1SessionEffects)
    (peers : List PeerId) (w : WGWorld) (a : Ambient) :
    (runWGPrefix (SessionReplay.sequence peers) w a []).1 =
      ((SessionReplay.original peers).run w).run a ∧
    SessionReplay.Safe (runWGPrefix (SessionReplay.sequence peers) w a []).2 ∧
    ∀ v b, ((SessionReplay.original peers).run w).run a = .ok (((), v), b) →
      v.keypairCounter = w.keypairCounter +
        (SessionReplay.successes (runWGPrefix (SessionReplay.sequence peers) w a []).2).length := by
  refine ⟨SessionReplay.sequence_erases peers w a [], ?_⟩
  obtain ⟨_, _, safe, post⟩ := SessionReplay.sequence_preserves H1 w.keypairCounter peers w a []
    (SessionReplay.initial w)
  refine ⟨safe, ?_⟩
  intro v b run
  have run' : (runPrefix ((SessionReplay.sequence peers).run w) a []).1 = .ok (((), v), b) :=
    (SessionReplay.sequence_erases peers w a []).trans run
  rw [run'] at post
  exact post.2.2

/-- Actual session installation does not reopen an initiation consumed by a
response: native response consumers interleaved with native session calls
accept at most once per peer. The H1 edge and session contracts stay explicit;
handshake refresh, allocation and arbitrary driver interleaving remain outside
this sequence. Completed receipts survive a later Stop. -/
theorem original_response_session_sequence_no_repeat (responseH1 : H1ResponseEdges)
    (sessionH1 : H1SessionEffects) (actions : List ResponseReplay.Action)
    (w : WGWorld) (a : Ambient) :
    (runWGPrefix (ResponseReplay.mixedSequence actions) w a []).1 =
      ((ResponseReplay.mixedOriginal actions).run w).run a ∧
    ResponseReplay.Safe (runWGPrefix (ResponseReplay.mixedSequence actions) w a []).2 := by
  refine ⟨ResponseReplay.mixed_erases actions w a [], ?_⟩
  obtain ⟨_, _, safe, _⟩ := ResponseReplay.mixed_preserves responseH1 sessionH1 actions w a []
    (ResponseReplay.initial w)
  exact safe

/-- The native receive consumer records its actual confirmation attempt before
later timers, staged sends or routing may Stop. At most one attempt is recorded,
and every normal completion records exactly one. This boundary does not infer
authentication or promotion from an arbitrary supplied consumer input. -/
theorem original_consumer_confirmation_boundary (pid : PeerId) (pkt : RxPacket)
    (ep : Endpoint) (w : WGWorld) (a : Ambient) :
    (runWGPrefix (Confirmation.observed pid pkt ep) w a []).1 =
      ((consumeDataDone pid pkt ep).run w).run a ∧
    Confirmation.Evidence [] (runWGPrefix (Confirmation.observed pid pkt ep) w a []).2 ∧
    ∀ result v b, ((consumeDataDone pid pkt ep).run w).run a = .ok ((result, v), b) →
      Confirmation.Completed [] (runWGPrefix (Confirmation.observed pid pkt ep) w a []).2 := by
  refine ⟨Confirmation.erases pid pkt ep w a [], ?_⟩
  obtain ⟨_, _, safe, post⟩ := Confirmation.evidence [] pid pkt ep w a [] rfl
  refine ⟨safe, ?_⟩
  intro result v b run
  have run' : (runPrefix ((Confirmation.observed pid pkt ep).run w) a []).1 =
      .ok ((result, v), b) := (Confirmation.erases pid pkt ep w a []).trans run
  rw [run'] at post
  exact post

/-- Every confirmation receipt emitted at the original poll's consume site is
an actual native confirmation attempt, retained even if a later suffix Stops.
The observer erases to the complete native poll with the supplied native stack
callback. This source-coverage theorem does not yet connect crypted packets to
AEAD history or assert promotion uniqueness or prior-send exclusion. -/
theorem original_poll_confirmation_receipts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → WG.M Unit) (w : WGWorld) (a : Ambient) :
    (runWGPrefix (Confirmation.Poll.observed pid budget toStack) w a []).1 =
      ((rxPoll pid budget toStack).run w).run a ∧
    Confirmation.Valid (runWGPrefix (Confirmation.Poll.observed pid budget toStack) w a []).2 := by
  refine ⟨Confirmation.Poll.erases pid budget toStack w a [], ?_⟩
  obtain ⟨_, _, safe, _⟩ := Confirmation.Poll.valid_preserves pid budget toStack w a []
    (by intro r member; cases member)
  exact safe

/-- Each confirmation receipt from the original poll's consume site has a
crypted packet and an actual successful replay-window check for that packet's key and nonce.
These inner receipts survive later Stop and erase to the full original poll.
Crypted-state provenance from successful AEAD, initialized uniqueness, and
prior encryption exclusion remain explicit separate transport obligations. -/
theorem original_poll_confirmation_replay_checked (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → WG.M Unit) (w : WGWorld) (a : Ambient) :
    (runWGPrefix (Confirmation.Authorization.Poll.observed pid budget toStack) w a []).1 =
      ((rxPoll pid budget toStack).run w).run a ∧
    Confirmation.Authorization.Valid
      (runWGPrefix (Confirmation.Authorization.Poll.observed pid budget toStack) w a []).2 := by
  refine ⟨Confirmation.Authorization.Poll.erases pid budget toStack w a [], ?_⟩
  obtain ⟨_, _, safe, _⟩ := Confirmation.Authorization.Poll.valid_preserves
    pid budget toStack w a [] (by intro r member; cases member)
  exact safe

/-- Under H1's visible native confirmation contract, a replay-accepted poll
receipt promotes exactly its received pending slot, keeps the peer allocation
identity, and clears pending state. No repeated-promotion or initialized
key-identity conclusion is inferred from this single native effect. -/
theorem original_poll_confirmation_slot_effect (H1 : H1ConfirmationEdges)
    (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → WG.M Unit)
    (w : WGWorld) (a : Ambient) (r : Confirmation.Authorization.Receipt)
    (occurs : r ∈ (runWGPrefix (Confirmation.Authorization.Poll.observed pid budget toStack) w a []).2) :
    ∃ before after,
      Confirmation.slotsAt r.confirmation.execution.before r.confirmation.peer = some before ∧
      Confirmation.slotsAt r.confirmation.execution.after r.confirmation.peer = some after ∧
      (r.confirmation.execution.value = true ↔ before.next = some r.confirmation.packet.keypair) ∧
      after.identity = before.identity ∧
      (r.confirmation.execution.value = true →
        after.current = some r.confirmation.packet.keypair ∧ after.next = none ∧
        after.previous = before.current) ∧
      (r.confirmation.execution.value = false → after = before) :=
  Confirmation.Authorization.receipt_slots H1 r
    ((original_poll_confirmation_replay_checked pid budget toStack w a).2 r occurs)

/-- Every completed consume occurrence in the actual initialized fixture is
linked to a strictly earlier successful native AEAD decrypt for its packet,
key slot and nonce, and to its actual native confirmation call. This includes
normal nondelivery and completed occurrences before a later Stop. The inherited
journal omits a consumer that itself Stops after confirmation; its inner-journal
runner transport and cross-call key-allocation identity remain separate. -/
theorem original_initialized_completed_confirmation_authenticated
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Queues.RxHistory.Event) (occurrence : Nat) (id : SkbId)
    (stamp : Lifetimes.PacketStamp) (r : Queues.RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed occurrence id stamp r :: post) :
    Confirmation.AuthenticatedSource pre id r :=
  Confirmation.initialized_authenticated trace placeholders pre post occurrence id stamp r position

/-- An actual initialized completed consume has an earlier successful native
AEAD decrypt and its actual confirmation cut; if that cut promotes, its key
allocation identity occurs in no other completed confirmation before or after
it. H1's initialized completed-label uniqueness and completeness are the named
visible premise. Consumers that themselves Stop after confirmation remain in
the separate inner-journal result, and prior-send exclusion is not inferred. -/
theorem original_initialized_completed_confirmation_authenticated_unique
    (H1 : H1InitializedCompletedConfirmation) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Queues.RxHistory.Event) (occurrence : Nat) (id : SkbId)
    (stamp : Lifetimes.PacketStamp) (r : Queues.RxDisposition.ConsumeReceipt)
    (position : Confirmation.initializedHistory trace placeholders =
      pre ++ .consumed occurrence id stamp r :: post) :
    Confirmation.AuthenticatedUnique pre post id r :=
  Confirmation.initialized_authenticated_unique H1 trace placeholders pre post occurrence id stamp r position

/-- Native staged sends retain the actual initial peer read and successful
current-key borrow beside every admitted packet batch, with the real key read,
clock guard and packet allocation. Receipts precede submission and survive its
later Stop. This all-input source claim does not assume initialized chronology. -/
theorem original_staging_selection_receipts (pid : PeerId) (w : WGWorld) (a : Ambient) :
    (runWGPrefix (StagingSelection.observed pid) w a []).1 =
      ((sendStagedPackets pid).run w).run a ∧
    StagingSelection.Good (runWGPrefix (StagingSelection.observed pid) w a []).2 := by
  refine ⟨StagingSelection.erases pid w a [], ?_⟩
  obtain ⟨_, _, good, _⟩ := StagingSelection.safe pid w a []
    ⟨(by intro r member; cases member), trivial⟩
  exact good

/-- Every admitted native staged batch uses the current slot returned by its
actual initial peer read and an actual resident key at its key read. This is
the local selection link needed for responder confirmation ordering; promotion
history and packet transit to a later encryption remain separate obligations. -/
theorem original_staging_selected_current (pid : PeerId) (w : WGWorld) (a : Ambient)
    (r : StagingSelection.Receipt)
    (occurs : r ∈ (runWGPrefix (StagingSelection.observed pid) w a []).2) :
    r.peerRead.value.keypairCurrent = some r.admission.slot ∧
    (∃ d, r.peerRead.before.dev = some d ∧
      d.peers[r.admission.peer]? = some r.peerRead.value) ∧
    (∃ d, r.admission.keyRead.before.dev = some d ∧
      d.keypairs[r.admission.slot]? = some r.admission.keyRead.value) ∧
    (∀ p ∈ r.admission.packets, p.peer = r.admission.peer ∧
      some p.keypair = r.peerRead.value.keypairCurrent ∧ p.nonce < REJECT_AFTER_MESSAGES) := by
  have valid := (original_staging_selection_receipts pid w a).2 r occurs
  have selected := StagingSelection.receipt_selected r valid
  obtain ⟨peer, key⟩ := StagingSelection.receipt_resident r valid
  refine ⟨selected, peer, key, ?_⟩
  intro p member
  obtain ⟨samePeer, slot, nonce⟩ := valid.2.2.2.2.2.2.2.1 p member
  exact ⟨samePeer, by rw [slot, selected], nonce⟩

/-- The original staging prefix through current-key borrowing preserves the
current allocation identity, initiator/responder role and sending key. It
cannot itself make an unconfirmed responder allocation current. The actual
fixture starts with no such current allocation; whole-driver preservation of
the confirmation-history invariant is still a separate obligation. -/
theorem original_staging_selection_current_material (pid : PeerId) :
    sendStagedPackets pid = Responder.selectionPrefix pid >>= Responder.selectionTail pid ∧
    (∀ w a result v b, ((Responder.selectionPrefix pid).run w).run a = .ok ((result, v), b) →
      Responder.current v = Responder.current w) ∧
    (∀ net bare, Responder.Authorized [] (Runner.initialWG net bare)) := by
  refine ⟨Responder.selection_factor pid, ?_, Responder.initial⟩
  intro w a result v b run
  exact (Framing.hoare_iff_run_ambient _ _ _).mp
    (Responder.selectionPrefix_current pid (Responder.current w)) w a result v b rfl run

/-- Under the visible H1 slot/material source contract, native confirmation
preserves responder-current authorization while recording the received key's
actual entry allocation. This is the local chronology transition: authentication
of its caller and transport from the initialized driver remain separate. -/
theorem original_responder_confirmation_history_step (H1 : H1ResponderCurrentEdges)
    (pid : PeerId) (kid : KeypairId) (confirmed : List Nat) (w v : WGWorld)
    (a b : Ambient) (result : Bool) (entry : Responder.Authorized confirmed w)
    (run : ((receivedWithKeypair pid kid).run w).run a = .ok ((result, v), b)) :
    Responder.Authorized (confirmed ++ Responder.confirmedAt w kid result) v :=
  Responder.confirmation_authorized H1 pid kid confirmed w v a b result entry run

/-- Every surviving key in a complete original staged send retains its allocation,
role and sending key, and the operation preserves responder-current authorization.
All drop branches and last-reference deletion are included. This is native
transport from an explicit entry invariant, not initialized chronology. -/
theorem original_staging_retains_responder_authorization (pid : PeerId)
    (confirmed : List Nat) (w v : WGWorld) (a b : Ambient)
    (entry : Responder.Authorized confirmed w)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((), v), b)) :
    Responder.Retains (Responder.pool w) (Responder.pool v) ∧
    Responder.Authorized confirmed v := by
  exact ⟨(Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
      (Responder.sendStagedPackets_core pid) w a () v b run,
    (Framing.hoare_iff_run_ambient _ _ _).mp
      (Responder.sendStagedPackets_authorized pid confirmed) w a () v b entry run⟩

/-- A completed original consumer retains responder-current authorization through
endpoint updates, confirmation, staged sends, timers and routing. The exact
existing C1 completed-event label records the promotion, under the visible H1
source contracts. The incoming history invariant still requires driver transport. -/
theorem original_completed_consumer_responder_history
    (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (confirmed : List Nat) (r : Queues.RxDisposition.ConsumeReceipt) (valid : r.Valid)
    (entry : Responder.Authorized confirmed r.run.before) :
    Responder.Authorized (confirmed ++ (Confirmation.completedLabel r).toList) r.run.after :=
  Responder.completed_consumer_history H1 slots confirmed r valid entry

/-- The actual receive poll, including its concrete Stack replies, carries
responder-current authorization across each completed confirmation and preserves
every consumer's incoming history through a later Stop. H1 source contracts and
the poll-entry invariant remain explicit; initialized runner closure is separate. -/
theorem original_poll_responder_history
    (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (pid : PeerId) (budget : Nat) (confirmed : List Nat) :
    PrefixPreserves (Responder.History.State confirmed) (Responder.History.Checks confirmed)
      (Queues.RxJoint.poll pid budget) :=
  Responder.History.poll H1 slots Responder.deliverInner_native pid budget confirmed

/-- The persistent receive journal carries responder authorization through both
actual NAPI delivery paths, preserving each completed consumer's exact incoming
confirmation prefix even if later work Stops. The real fixture satisfies the
empty-history invariant; other runner actors still require transport. -/
theorem original_napi_responder_history
    (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) :
    Responder.Global.Preserves Queues.RxHistory.napiSoftirq ∧
    Responder.Global.Preserves Queues.RxHistory.pollScheduledInline ∧
    Responder.Global.Preserves Queues.RxHistory.napiIrqExit :=
  ⟨Responder.Global.napiSoftirq H1 slots, Responder.Global.pollScheduledInline H1 slots,
    Responder.Global.napiIrqExit H1 slots⟩

/-- Both actual crypt workers preserve responder-current authorization with
all nested NAPI confirmations in the same journal. Encryption is framed here;
this theorem does not yet authorize each packet encrypted by the worker. -/
theorem original_crypt_workers_responder_history
    (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) :
    Responder.Global.Preserves Queues.RxHistory.decryptIteration ∧
    Responder.Global.Preserves Queues.RxHistory.encryptIteration :=
  ⟨Responder.Global.decryptIteration H1 slots, Responder.Global.encryptIteration H1 slots⟩

/-- The original session observer preserves responder-current authorization
using H1's slot/material contract and C1's configured self-word invariant in
the same execution. A fresh responder session cannot newly become current. -/
theorem original_session_responder_history (H1 : H1ResponderCurrentEdges) (pid : PeerId) :
    Responder.Joint.Preserves (Origins.HistoryAdapters.session pid) :=
  Responder.Joint.session H1 pid

/-- The real handshake receive worker retains responder-current authorization
through Noise consumers, session installation, timers, cookie replies and
keepalive staging. Its configured/slot entry facts come from C1's same-run
journal; H1's slot/material edge contract remains visible. Other driver actors
and packet-to-encryption chronology remain separate obligations. -/
theorem original_handshake_worker_responder_history (H1 : H1ResponderCurrentEdges) :
    Responder.Joint.Preserves Origins.HistoryAdapters.receiveStep ∧
    Responder.Joint.Preserves Origins.HistoryAdapters.receiveIteration :=
  ⟨Responder.Joint.receiveStep H1, Responder.Joint.receiveIteration H1⟩

/-- The actual queued handshake/clear workers and recorded timer dispatch
preserve responder-current authorization and the existing confirmation prefix.
All five callbacks, detachment, section guards and native failures are included;
the outer scheduler and initialized driver transport remain separate. -/
theorem original_deferred_units_responder_history (H1 : H1ResponderCurrentEdges)
    (worker : Worker) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (step : Option UInt64) (j : UInt64) :
    Responder.Joint.Preserves (Queues.RxHistory.audit Lifetimes.runOneSendWorkerAudit) ∧
    Responder.Joint.Preserves (Queues.RxHistory.audit Lifetimes.runOneClearWorkerAudit) ∧
    Responder.Joint.Preserves (Queues.RxHistory.audit (Lifetimes.timerDispatchAudit worker pid timer entry step)) ∧
    Responder.Joint.Preserves (Queues.RxHistory.audit (Queues.RxHistory.placeholderTimerPassAudit j)) :=
  ⟨Responder.Joint.sendOne, Responder.Joint.clearOne H1,
    Responder.Joint.timerDispatch worker pid timer entry step, Responder.Joint.placeholderPass j⟩

/-- The native scheduler and its actual TX worker preserve responder-current
authorization across all dispatch kinds, nested rescheduling and crypt-ahead.
Each completed confirmation remains in the same persistent journal, including
prefixes retained before Stop. H1 is explicit; initialized driver closure and
each encrypted packet's staging provenance remain separate obligations. -/
theorem original_scheduler_responder_history
    (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (worker : Worker) (pid : PeerId) :
    Responder.Joint.Preserves (Queues.RxHistory.schedule none) ∧
    Responder.Joint.Preserves (Queues.RxHistory.nestedResched worker) ∧
    Responder.Joint.Preserves (Queues.RxHistory.mixed
      (Lifetimes.txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  ⟨Responder.Joint.schedule H1 slots none, Responder.Joint.nestedResched H1 slots worker,
    Responder.Joint.txIteration pid⟩

/-- All fourteen real deferred-call variants preserve responder-current
confirmation history, including ordered timer-wheel scans, saved-peer reads,
crypt/send loops and both timer modes. The source H1 contracts remain explicit;
this is actor closure, with initialized syscall transport still separate. -/
theorem original_deferred_responder_history
    (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (call : Lifetimes.EnvDeferredCall) :
    Responder.Joint.Preserves (Queues.RxHistory.deferred call) :=
  Responder.Deferred.deferred H1 slots call

/-- Full native peer/device configuration preserves responder-current
confirmation history through creation, removal, allowed-IP changes, private-key
replacement and normal errno returns. The same-run observer retains stopped
prefixes; no source command is replaced by a desired postcondition. -/
theorem original_configuration_responder_history (H1 : H1ResponderCurrentEdges)
    (attrs : DeviceAttrs) :
    Responder.Joint.Preserves (Queues.RxHistory.mixed
      (liftWGObserver (Lifetimes.wgSetDevicePrefix attrs))) :=
  Responder.Joint.wgSetDevice H1 attrs

/-- Native device setup, open, stop, destruction and namespace pre-exit
cannot leave an unconfirmed responder allocation current, from the stated
entry invariant and H1 clear contract. Reset devices discharge old obligations
by removing their peers. Initialized outer transport remains separate. -/
theorem original_device_lifecycle_responder_authorization
    (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Framing.Preserves (Responder.History.Native confirmed) wgCreate ∧
    Framing.Preserves (Responder.History.Native confirmed) wgUp ∧
    Framing.Preserves (Responder.History.Native confirmed) wgDown ∧
    Framing.Preserves (Responder.History.Native confirmed) wgDestruct ∧
    Framing.Preserves (Responder.History.Native confirmed) netnsPreExit :=
  ⟨Responder.create_native confirmed, Responder.up_native confirmed,
    Responder.down_native H1 confirmed, Responder.destruct_native H1 confirmed,
    Responder.preExit_native confirmed⟩

/-- On every actual initialized trace, each completed consumer entry carries
responder-current authorization from its strictly earlier confirmation prefix.
All syscall actors and both placeholder modes are covered, including prior
completed events before an indexed Stop. Only named H1 source contracts remain;
no entry invariant, trace validity or successful-run premise is supplied. -/
theorem initialized_responder_history (H1 : H1ResponderCurrentEdges)
    (slots : H1ConfirmationEdges) (trace : Runner.Trace) (placeholders : Bool) :
    Responder.Joint.Safe
      (runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 :=
  Responder.Initialized.executeTrace H1 slots trace placeholders

/-- A responder allocation current at a captured initialized consumer entry
has a strictly earlier native authenticated receive whose confirmation returned
true for that allocation. This is initialized slot chronology, with the separate
staged-packet-to-encryption bridge still required for no-prior-encryption. -/
theorem initialized_current_responder_previously_confirmed
    (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Queues.RxHistory.Event) (occurrence : Nat) (id : SkbId)
    (stamp : Lifetimes.PacketStamp) (r : Queues.RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed occurrence id stamp r :: post)
    (pid : PeerId) (core : Responder.KeyCore)
    (resident : Responder.current r.run.before pid = some core)
    (responder : core.initiator = false) :
    Responder.Initialized.PriorConfirmation pre core.allocation :=
  Responder.Initialized.current_has_earlier_authenticated_confirmation H1 slots trace placeholders
    pre post occurrence id stamp r position pid core resident responder

/-- The actual initialized completed receive combines earlier native AEAD,
prior responder authorization and allocation-labelled confirmation uniqueness.
The named H1 uniqueness boundary is visible beside its source edge contracts;
inside-consumer stopped prefixes and encrypted-packet transport retain their
separate scope. -/
theorem initialized_authenticated_responder_history
    (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (unique : H1InitializedCompletedConfirmation) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Queues.RxHistory.Event) (occurrence : Nat) (id : SkbId)
    (stamp : Lifetimes.PacketStamp) (r : Queues.RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed occurrence id stamp r :: post) :
    Responder.History.Native (Confirmation.completedLabels pre) r.run.before ∧
    Confirmation.AuthenticatedUnique pre post id r ∧
    Responder.Authorized (Confirmation.completedLabels pre ++
      (Confirmation.completedLabel r).toList) r.run.after :=
  Responder.Initialized.authenticated_history H1 slots unique trace placeholders
    pre post occurrence id stamp r position

/-- A native staging borrow selects the actual peers current allocation and
sending material. A responder allocation therefore has an earlier confirmation
in the same cut history when that cut carries authorization. Initialized TX
transport remains a separate obligation rather than an assumed trace fact. -/
theorem original_staging_selected_responder_confirmation
    (pid : PeerId) (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (valid : r.Valid (Responder.selectionPrefix pid)) (p : Peer) (kid : KeypairId)
    (selected : r.value = some (p, some kid)) (core : Responder.KeyCore)
    (material : Responder.pool r.before kid = some core) (confirmed : List Nat)
    (entry : Responder.Authorized confirmed r.before) (responder : core.initiator = false) :
    core.allocation ∈ confirmed :=
  Responder.DriverCuts.selected_responder_confirmed pid r valid p kid selected core material
    confirmed entry responder

/-- A native promotion receipt remains in its actual shared journal before any
later stopped staging or clock continuation. Confirmation is therefore observed
at the source cut, without requiring a normally completed consumer. -/
theorem original_confirmation_journal_retains
    (pid : PeerId) (kid : KeypairId) (w v : WGWorld) (a b : Ambient)
    (h : List Responder.DriverCuts.Event) (value : Bool)
    (run : ((receivedWithKeypair pid kid).run w).run a = .ok ((value, v), b))
    (next : Bool → WGPrefix Responder.DriverCuts.Event α)
    (appends : ∀ value, StateAppends (next value)) :
    ∃ suffix, (runWGPrefix (Responder.DriverCuts.confirmation pid kid >>= next) w a h).2 =
      h ++ [.confirmed pid kid ⟨value, w, v, a, b⟩] ++ suffix :=
  Responder.DriverCuts.confirmation_retained pid kid w v a b h value run next appends

/-- The actual shared-driver staging path carries checked responder selection
through every nonce, allocation and refusal branch. A later Stop retains the
source receipt. The configured/current entry carrier remains explicit until
initialized driver transport closes; this is not yet an AEAD claim. -/
theorem original_staging_responder_cut_history (pid : PeerId) :
    Responder.DriverCuts.Preserves
      (TransmitSecurity.Driver.stagingObserved Responder.DriverCuts.hooks pid) :=
  Responder.DriverCuts.staging pid

/-- Native receive confirmation advances the shared responder history before
receive-triggered staging. Receipts remain checked through a later consumer
Stop; the configured/current entry carrier and H1 slot-edge contract are
explicit while initialized shared-driver transport is being discharged. -/
theorem original_consumer_responder_cut_history (H1 : H1ResponderCurrentEdges)
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Responder.DriverCuts.Preserves
      (TransmitSecurity.Driver.consumeObserved Responder.DriverCuts.hooks pid pkt ep) :=
  Responder.DriverCuts.consume H1 pid pkt ep

/-- The actual shared poll carries responder confirmation through its native
stack callback, including reply-triggered transmissions. All receipts before a
later Stop stay checked. The explicit incoming carrier is the remaining
initialized-runner transport obligation; native AEAD provenance is separate. -/
theorem original_poll_responder_cut_history (H1 : H1ResponderCurrentEdges)
    (pid : PeerId) (budget : Nat) :
    Responder.DriverCuts.ProductPreserves
      (TransmitSecurity.Driver.nativePollObserved Responder.DriverCuts.hooks pid budget) :=
  Responder.DriverCuts.native_poll H1 pid budget

/-- The committed native scheduler carries responder authorization through
handshake, encrypt, decrypt and transmit workers and their NAPI callbacks in
one shared journal, including receipts before Stop. Copied consistency trials
add no committed receipts. Initialization and native authentication linkage
remain separate obligations; the carrier and named H1 edge contract are visible. -/
theorem original_scheduler_responder_cut_history (H1 : H1ResponderCurrentEdges)
    (stack : Option Worker) :
    Responder.DriverCuts.ProductPreserves
      (TransmitSecurity.Driver.scheduleObserved Responder.DriverCuts.hooks stack) :=
  Responder.DriverCuts.schedule H1 stack

/-- Actual timer passes carry responder authorization through keepalive staging,
send and clear work, and the shared native scheduler. Both concrete and
placeholder timing modes preserve checked receipts before Stop. The incoming
carrier remains explicit until initialized outer-driver transport closes. -/
theorem original_timer_pass_responder_cut_history (H1 : H1ResponderCurrentEdges)
    (j : UInt64) :
    Responder.DriverCuts.ProductPreserves
      (TransmitSecurity.Driver.timersObserved Responder.DriverCuts.hooks j) ∧
    Responder.DriverCuts.ProductPreserves
      (TransmitSecurity.Driver.placeholderTimersObserved Responder.DriverCuts.hooks j) :=
  ⟨Responder.DriverCuts.timers H1 j, Responder.DriverCuts.placeholder_timers H1 j⟩

/-- Native device configuration carries responder authorization through peer
creation, deleting releases and configuration-triggered staging in the same
journal. Saved peer writes use their actual reads. The configured/current
incoming carrier remains explicit pending outer initialized-driver closure. -/
theorem original_configuration_responder_cut_history (H1 : H1ResponderCurrentEdges)
    (attrs : DeviceAttrs) :
    Responder.DriverCuts.Preserves
      (TransmitSecurity.Driver.configDevice Responder.DriverCuts.hooks attrs) :=
  Responder.DriverCuts.config_device H1 attrs

/-- Every responder current-key selection on the initialized shared driver
has a strictly earlier successful native confirmation for its actual key
allocation. No incoming state/history invariant is assumed, and later Stops
retain the evidence. H1's slot edges remain explicit. Authenticated receive
provenance and the deferred packet-to-AEAD link are separate obligations. -/
theorem initialized_selection_has_prior_native_confirmation
    (H1 : H1ResponderCurrentEdges) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Responder.DriverCuts.Event) (pid : PeerId)
    (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (position : (runPrefixOuter (Responder.DriverCuts.execute trace placeholders) []).2 =
      pre ++ .selected pid r :: post)
    (p : Peer) (kid : KeypairId) (selected : r.value = some (p,some kid))
    (core : Responder.KeyCore) (material : Responder.pool r.after kid = some core)
    (responder : core.initiator = false) :
    Responder.DriverCuts.PriorNativeConfirmation pre core.allocation :=
  Responder.DriverCuts.initialized_selected_prior_confirmation H1 trace placeholders
    pre post pid r position p kid selected core material responder

/-- Every timestamp write committed during any initialized native runner
execution is strictly greater than the retained peer's timestamp at that
write. The exact JSON or indexed Stop is unchanged, and a later Stop retains
the write receipt. Linking successive writes across peer creation and all
intervening native actors remains a separate history obligation. -/
theorem initialized_timestamp_writes_increase (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (TimestampDriver.execute trace placeholders) (Runner.executeTrace trace placeholders) ∧
    IncreasingReceipts (runPrefixOuter (TimestampDriver.execute trace placeholders) []).2 :=
  ⟨TimestampDriver.execute_erases trace placeholders, TimestampDriver.initialized_increasing trace placeholders⟩

open AuthenticatedEffects ConfirmationTransportOrder in
/-- A native confirmation receipt is authorized by the immediately preceding
successful replay check for the same peer and key. Joining the two safety
properties of this one journal gives the actual earlier authenticated packet;
initialized transport of the ordering property remains explicit here. -/
theorem native_confirmation_authenticated_in_same_history {E : Type}
    (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (decode : E → Option ResponderEvent) (inverse : ∀ r, replay (record r) = some r)
    (history pre post : List E) (event : E) (pid : PeerId) (kid : KeypairId) (r : WGRunWitness Bool)
    (ordered : Safe record decode history) (accepted : TransportReplay.Safe origin replay history)
    (position : history = pre ++ event :: post)
    (recorded : decode event = some (.confirmed pid kid r)) :
    r.Valid (receivedWithKeypair pid kid) ∧
    ∃ earlier counter, pre = earlier ++ [record counter] ∧
      counter.packet.peer = pid ∧ counter.packet.keypair = kid ∧ counter.run.value = true ∧
      TransportReplay.Certified (earlier.filterMap origin) counter :=
  ConfirmationTransportOrder.authenticated origin replay record decode inverse
    history pre post event pid kid r ordered accepted position recorded

/-- The full native initiation consumer carries a strictly advancing timestamp
archive indexed by peer allocation, so deleting cleanup and future slot reuse
cannot conflate two peers. Writes preceding a later Stop remain in the history.
The actual entry archive invariant is explicit until full driver transport. -/
theorem original_initiation_allocation_timestamp_archive (msg : List UInt8) :
    StatePrefixPreserves (fun h w _ => TimestampArchive.StateInv h w)
      TimestampArchive.History (consumeObserved msg) :=
  TimestampArchive.consume_history msg

/-- Native peer construction creates a fresh timestamp incarnation and retains
the histories of earlier allocations, even if it reuses a numeric peer slot.
The complete constructor discharges its actual allocation core and saved writes;
only the incoming archive carrier remains explicit. -/
theorem original_peer_creation_timestamp_archive (key : Key) (psk : Option Key)
    (history : List TimestampReceipt) :
    Framing.Preserves (TimestampArchive.StateInv history) (peerCreate key psk) :=
  TimestampArchive.peer_create key psk history

/-- Staging and keepalive transmission on the common native driver preserve
the allocation-indexed timestamp archive through nonce limits, packet allocation
and queue refusal, including prefixes before Stop. The entry carrier remains
explicit while the initialized outer driver transport is being discharged. -/
theorem original_staging_timestamp_archive (pid : PeerId) :
    TimestampArchive.Preserves
      (TransmitSecurity.Driver.stagingObserved TimestampDriver.hooks pid) ∧
    TimestampArchive.Preserves
      (TransmitSecurity.Driver.keepaliveObserved TimestampDriver.hooks pid) :=
  ⟨TimestampArchive.staging pid,TimestampArchive.keepalive pid⟩

open ConfirmationTransportOrder AuthenticatedEffects TransmitSecurity.Driver in
/-- Every confirmation reached by the native receive poll follows its exact
successful replay check for the same peer and key. The source derives that
precondition before calling confirmation; other hooks must preserve history.
Initialized authentication and packet-to-encryption transport remain separate. -/
theorem original_poll_preserves_confirmation_order {E : Type}
    (record : TransportDriver.Replay → E) (responder : ResponderEvent → E)
    (decode : E → Option ResponderEvent)
    (inverse : ∀ event, decode (responder event) = some event)
    (quiet : ∀ r, Unconfirmed decode (record r)) (hooks : Hooks E)
    (h : QuietHooksSafe (Safe record decode) hooks)
    (counter : hooks.counterCheck = TransportDriver.counter record)
    (confirmed : hooks.confirmation = confirmation responder decode) (pid : PeerId) (budget : Nat) :
    ProductHistorySafe (Safe record decode) (nativePollObserved hooks pid budget) :=
  quiet_nativePoll record responder decode inverse quiet h counter confirmed pid budget

/-- Native timer arming and deletion retain the replay archive for each peer
allocation. The saved peer write keeps its actual read witness, so a stale
timer copy cannot silently reset a retained timestamp in this contract. -/
theorem original_timer_maintenance_timestamp_archive (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (jc : Option UInt64) (history : List TimestampReceipt) :
    Framing.Preserves (TimestampArchive.StateInv history) (armTimer pid timer delay jc) ∧
    Framing.Preserves (TimestampArchive.StateInv history) (delTimer pid timer) :=
  ⟨TimestampArchive.arm_timer pid timer delay jc history,
    TimestampArchive.del_timer pid timer history⟩

/-- The native receive poll cannot reset the timestamp history of a retained
peer allocation, including confirmation, staging, routing cleanup and stopped
prefixes. The actual stack callback's archive contract remains explicit. -/
theorem original_receive_poll_timestamp_archive (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM TimestampReceipt Unit)
    (callbacks : ∀ packets, TimestampArchive.ProductPreserves (callback packets)) :
    TimestampArchive.ProductPreserves
      (TransmitSecurity.Driver.pollObserved TimestampDriver.hooks pid budget callback) :=
  TimestampArchive.poll pid budget callback callbacks

/-- Native handshake work carries each peer allocation's advancing timestamp
archive through refusal, committed initiation writes, key installation and
keepalive sends. The native receive poll also retains it through actual stack
replies, so no callback preservation premise remains at these actor cuts. -/
theorem original_handshake_and_receive_timestamp_archive (pid : PeerId) (budget : Nat) :
    TimestampArchive.Preserves
      (TransmitSecurity.Driver.handshakeObserved TimestampDriver.hooks) ∧
    TimestampArchive.ProductPreserves
      (TransmitSecurity.Driver.nativePollObserved TimestampDriver.hooks pid budget) :=
  ⟨TimestampArchive.handshake_worker,TimestampArchive.native_poll pid budget⟩

/-- Committed native worker scheduling retains the timestamp archive across
handshake reception, encryption, decryption, transmit disposal and either NAPI
mode. Failed copied scheduling trials add no committed receipts. The incoming
archive carrier remains explicit until initialized runner transport closes. -/
theorem original_scheduler_timestamp_archive (stack : Option Worker) :
    TimestampArchive.ProductPreserves
      (TransmitSecurity.Driver.scheduleObserved TimestampDriver.hooks stack) :=
  TimestampArchive.schedule stack

/-- Every native peer-timer callback retains the timestamp archive across
retry accounting, queue purge, key retirement and actual keepalive staging.
The archive's initialized outer transport is a separate obligation. -/
theorem original_timer_callbacks_timestamp_archive (pid : PeerId) (timer : PeerTimer) :
    TimestampArchive.Preserves
      (TransmitSecurity.Driver.timerObserved TimestampDriver.hooks pid timer) :=
  TimestampArchive.timer pid timer

open TransmitSecurity in
/-- A responder allocation selected by native staging has already undergone
a successful confirmation triggered by the exact authenticated, replay-accepted
packet in this initialized execution. H1's source slot rules remain explicit.
Lifetime continuity from the earlier AEAD key to the confirmation allocation,
and from staging to a later encryption, remain separate claims. -/
theorem initialized_responder_selection_authenticated
    (H1 : H1ResponderCurrentEdges) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (event : Journal.Event) (pid : PeerId)
    (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 = pre ++ event :: post)
    (recorded : Journal.responder? event = some (.selected pid r))
    (p : Peer) (kid : KeypairId) (selected : r.value = some (p,some kid))
    (core : Responder.KeyCore) (material : Responder.pool r.after kid = some core)
    (responder : core.initiator = false) :
    Responder.PriorAuthenticatedConfirmation pre core.allocation :=
  Responder.journal_selected_authenticated_confirmation H1 trace placeholders
    pre post event pid r position recorded p kid selected core material responder

/-- Native traffic batches and timer passes retain the peer-allocation
timestamp archive across actual worker dispatch, receive admission, transmit
staging and deleting releases, including stopped prefixes. Initialization and
configuration transport remain separate obligations. -/
theorem original_traffic_and_timers_timestamp_archive (items : List Env.BatchItem) :
    TimestampArchive.ProductPreserves
      (TransmitSecurity.Driver.batchObserved TimestampDriver.hooks items) ∧
    TimestampArchive.ProductPreserves
      (TransmitSecurity.Driver.afterAdvanceObserved TimestampDriver.hooks) :=
  ⟨TimestampArchive.batch items,TimestampArchive.after_advance⟩

/-- Native device configuration preserves each peer allocation's timestamp
history through creation, removal, route-list updates, key changes and sends
caused by keepalive configuration. The saved peer writes use their source read;
the initialized outer runner transport remains a separate obligation. -/
theorem original_device_configuration_timestamp_archive (attrs : DeviceAttrs) :
    TimestampArchive.Preserves
      (TransmitSecurity.Driver.configDevice TimestampDriver.hooks attrs) :=
  TimestampArchive.config_device attrs

/-- In every initialized native execution, each committed initiation timestamp
is linked to the earlier history of the same peer allocation and strictly
exceeds its previous value. Deletion and numeric-slot reuse do not erase that
history. The observer exactly retains the native result and stopped prefix;
no incoming invariant or completed-consumer premise is required. -/
theorem initialized_timestamp_archive (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (TimestampDriver.execute trace placeholders) (Runner.executeTrace trace placeholders) ∧
    TimestampArchive.History (runPrefixOuter (TimestampDriver.execute trace placeholders) []).2 :=
  ⟨TimestampDriver.execute_erases trace placeholders,TimestampArchive.initialized trace placeholders⟩

/-- An actual initiation write for a peer allocation strictly exceeds its
last archived timestamp in this same initialized execution. The archive input
is the real execution prefix, so a reset through another actor cannot justify
accepting an old timestamp. -/
theorem initialized_timestamp_exceeds_archive (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List TimestampReceipt) (r : TimestampReceipt)
    (position : (runPrefixOuter (TimestampDriver.execute trace placeholders) []).2 = pre ++ r :: post)
    (identity : Nat) (old : List UInt8)
    (allocation : (freshnessAt r.execution.before r.peer).map Prod.fst = some identity)
    (archived : TimestampArchive.replay pre identity = some old) : memcmp r.received old = .gt :=
  TimestampArchive.initialized_advances_archive trace placeholders pre post r position identity old allocation archived

/-- Observing initiation creation and its send suffix through the shared
callbacks preserves the exact native worker, including failures. This source
boundary prevents a later send failure from forcing the exchange observer to
wait for whole-worker completion; initialized exchange uniqueness is separate. -/
theorem native_send_exchange_erasure {E : Type} (ops : SendExchange.Ops (WGPrefix E))
    (callbacks : ops.Erases) (pid : PeerId) :
    ErasesStatePrefix (SendExchange.workerWith ops pid) (handshakeSendWorker pid) :=
  SendExchange.worker_erases callbacks pid

/-- Direct configuration removal can observe the same queued-send callbacks
as scheduled workers without skipping any native drain, guard or Stop. This
local erasure contract exposes the removal path needed by exchange coverage. -/
theorem native_removal_exchange_erasure {E : Type}
    (step : {α : Type} → WG.M α → WGPrefix E α)
    (nativeStep : ∀ {α} (a : WG.M α), ErasesStatePrefix (step a) a)
    (drain : Option PeerId → WGPrefix E Unit)
    (nativeDrain : ∀ peer, ErasesStatePrefix (drain peer) (drainHandshakeSendWq peer))
    (peer : Option PeerId) :
    ErasesStatePrefix (SendExchange.removeWith step drain peer) (peerRemove peer) ∧
    ErasesStatePrefix (SendExchange.removeAllWith step drain) peerRemoveAll :=
  ⟨SendExchange.remove_erases step nativeStep drain nativeDrain peer,
    SendExchange.removeAll_erases step nativeStep drain nativeDrain⟩

/-- Given the native exchange-history carrier, two successful response
consumptions for one peer require different initiation epochs. The carrier is
an explicit boundary: initialized whole-driver transport is still required. -/
theorem exchange_response_consumed_once {history : List Exchange.Event} {ledger : Exchange.Ledger}
    (carrier : Exchange.History history ledger)
    (pre between post : List Exchange.Event) (first second : List UInt8)
    (r s : WGRunWitness (Option PeerId)) (pid : PeerId)
    (position : history = pre ++ Exchange.Event.consumeResponse first r :: between ++
      Exchange.Event.consumeResponse second s :: post)
    (accepted₁ : r.value = some pid) (accepted₂ : s.value = some pid) :
    ∃ epoch₁ epoch₂, Exchange.ResponseAt pre pid epoch₁ ∧
      Exchange.ResponseAt (pre ++ Exchange.Event.consumeResponse first r :: between) pid epoch₂ ∧
      epoch₁ < epoch₂ :=
  Exchange.response_no_repeat carrier pre between post first second r s pid position accepted₁ accepted₂

/-- Given the native exchange-history carrier, a completed session has an
earlier native exchange start and advances the key-allocation counter exactly
once. H1's source effect and the history premise remain visible. -/
theorem exchange_installation_count (H1 : H1SessionEffects)
    {history : List Exchange.Event} {ledger : Exchange.Ledger}
    (carrier : Exchange.History history ledger) (pre post : List Exchange.Event)
    (pid : PeerId) (r : WGRunWitness Bool)
    (position : history = pre ++ Exchange.Event.session pid r :: post) (success : r.value = true) :
    r.after.keypairCounter = r.before.keypairCounter + 1 ∧
    ∃ epoch, Exchange.InstallAt pre pid epoch ∧ Exchange.Origin pre pid epoch := by
  obtain ⟨epoch,binding⟩ := carrier.install_epoch pre post pid r position success
  exact ⟨Exchange.installation_count H1 carrier pre post pid r position success,
    epoch,binding,carrier.install_origin pre post pid r position epoch binding⟩

/-- Exchange replay claims use the actual native execution: the shared driver
with completed exchange receipts returns the original runner's JSON or indexed
Stop. The initialized exchange-history invariant remains a separate obligation. -/
theorem initialized_exchange_driver_erasure (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (ExchangeDriver.execute trace placeholders) (Runner.executeTrace trace placeholders) :=
  ExchangeDriver.execute_erases trace placeholders

/-- A queued initiation send advances the native exchange ledger only through
its completed creator receipt. Native dequeue, timestamp, timer and send
suffixes preserve that ledger, including receipts retained before a later Stop.
The C2 H1 edge and source-frame facts are explicit operational assumptions;
initialized whole-driver exchange transport is a separate obligation. -/
theorem queued_send_exchange_history (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames)
    (pid : PeerId) : Exchange.Preserves (ExchangeDriver.flushed pid) :=
  Exchange.flushed_checked H1 frames pid

/-- Actual handshake receive consumes each exchange through the native
receipt cuts before response creation or installation. Later suffix failures
retain that ledger. Session and keepalive callback transport remains explicit;
this is the receive-worker source contract, not initialized driver closure. -/
theorem receive_worker_exchange_history (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames)
    (session : PeerId → WGPrefix Exchange.Event Bool)
    (keepalive : PeerId → WGPrefix Exchange.Event Unit)
    (sessions : ∀ pid, Exchange.Preserves (session pid))
    (keepalives : ∀ pid, Exchange.Preserves (keepalive pid)) :
    Exchange.Preserves (ExchangeDriver.worker session keepalive) :=
  Exchange.receive_worker_checked H1 frames session keepalive sessions keepalives

/-- The shared driver's actual handshake worker preserves the exchange ledger
through native response consumption, installation and keepalive staging.
Callback-safety premises are discharged; only the named C2 operational edge and
tag-frame packages remain. Initialized outer-driver transport is still separate. -/
theorem actual_handshake_exchange_history (H1 : H1ExchangeEdges)
    (handshake : H1HandshakeTagFrames) (data : H1DataTagFrames) :
    Exchange.Preserves (TransmitSecurity.Driver.handshakeObserved ExchangeDriver.hooks) :=
  Exchange.handshake_checked H1 handshake data

/-- Every committed worker activation preserves the exchange ledger through
the actual scheduler, including data delivery and handshake installation.
Named C2 native edge/frame packages remain visible. Initialization and outer
configuration, lifecycle and traffic transport remain separate obligations. -/
theorem scheduled_exchange_history (H1 : H1ExchangeEdges)
    (handshake : H1HandshakeTagFrames) (data : H1DataTagFrames)
    (workers : H1WorkerTagFrames) (stack : Option Worker) :
    Exchange.ProductPreserves (TransmitSecurity.Driver.scheduleObserved ExchangeDriver.hooks stack) :=
  Exchange.schedule_checked H1 handshake data workers stack

/-- Deferred sends and both native timer modes preserve the same exchange
ledger, including Stop prefixes. The visible C2 package contains only native
edge and tag-frame facts; it assumes no exchange history or reachability.
Lifecycle, configuration and outer initialization are separate obligations. -/
theorem deferred_exchange_history (facts : H1DriverSourceFacts) :
    Exchange.ProductPreserves
      (TransmitSecurity.Driver.afterXmitObserved ExchangeDriver.hooks) ∧
    Exchange.ProductPreserves
      (TransmitSecurity.Driver.afterAdvanceObserved ExchangeDriver.hooks) :=
  ⟨Exchange.after_xmit facts, Exchange.after_advance facts⟩

/-- A completed exchange receipt can decorate the existing authenticated
callback without replacing its execution. Exact native erasure and an
independent exchange-history frame project the same callback to the T4
receipt, including every stopped prefix. -/
theorem observed_exchange_receipt_projection (decode : E → Option Exchange.Event)
    (encode : Exchange.Event → E) (roundtrip : ∀ e, decode (encode e) = some e)
    (callback : WGPrefix E α) (native : WG.M α)
    (erases : ErasesStatePrefix callback native)
    (quiet : StateHistoryFrame decode callback) (record : WGRunWitness α → Exchange.Event) :
    StateProjectsPrefix decode id (receiptWGObserved callback (encode ∘ record))
      (receiptWGObserved (liftWGPrefix native) record) :=
  Exchange.decorated_native_projection decode encode roundtrip callback native erases quiet record

/-- Shutdown and destruction retain the exchange ledger across every actual
queued-send drain, including the nested timersStop drain. Deleting the device
does not delete the completed history. Only named C2 native edge and tag-frame
facts are assumed; initialized outer-driver transport remains separate. -/
theorem lifecycle_exchange_history (facts : H1DriverSourceFacts) :
    Exchange.Preserves (TransmitSecurity.Driver.downObserved ExchangeDriver.hooks) ∧
    Exchange.Preserves (TransmitSecurity.Driver.destructObserved ExchangeDriver.hooks) :=
  ⟨Exchange.down_checked facts,Exchange.destruct_checked facts⟩

/-- Actual environment up, down and delete operations preserve exchange
history through their routing notifications and observed lifecycle callbacks.
Native C2 source facts remain explicit; outer initialized execution is separate. -/
theorem environment_exchange_history (facts : H1DriverSourceFacts) :
    Exchange.ProductPreserves (TransmitSecurity.Driver.envUpObserved ExchangeDriver.hooks) ∧
    Exchange.ProductPreserves (TransmitSecurity.Driver.envDownObserved ExchangeDriver.hooks) ∧
    Exchange.ProductPreserves (TransmitSecurity.Driver.envDeleteObserved ExchangeDriver.hooks) :=
  ⟨Exchange.env_up_checked facts,Exchange.env_down_checked facts,Exchange.env_delete_checked facts⟩

/-- Device and peer configuration preserve the exchange ledger through the
actual command path, including nested queued sends during peer removal. Native
C2 edge and tag-frame assumptions are named explicitly; initialized runner
transport remains separate. -/
theorem configuration_exchange_history (facts : H1DriverSourceFacts)
    (config : H1ConfigurationTagFrames) (attrs : DeviceAttrs) :
    Exchange.Preserves (TransmitSecurity.Driver.configDevice ExchangeDriver.hooks attrs) :=
  Exchange.config_device facts config attrs

/-- The actual initialized native execution has a valid exchange history,
including completed exchanges before a later Stop. Only named native C2 edge
and tag-frame facts are assumed; the caller supplies no initialized invariant,
reachability or exchange-history premise. The source returns exactly the
original runner result or indexed Stop. -/
theorem initialized_native_exchange_history (facts : H1DriverSourceFacts)
    (config : H1ConfigurationTagFrames) (traffic : H1TrafficTagFrames)
    (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (ExchangeDriver.execute trace placeholders) (Runner.executeTrace trace placeholders) ∧
    Exchange.History (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2
      (Exchange.replay (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2) :=
  ⟨ExchangeDriver.execute_erases trace placeholders,Exchange.initialized facts config traffic trace placeholders⟩

/-- Replaying a response cannot consume the same initiation exchange twice:
two successful native response receipts for one peer have strictly different
start epochs in this initialized execution. Named C2 native source facts remain
explicit, and completed receipts survive a later Stop. -/
theorem initialized_response_consumed_once (facts : H1DriverSourceFacts)
    (config : H1ConfigurationTagFrames) (traffic : H1TrafficTagFrames)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre between post : List Exchange.Event) (first second : List UInt8)
    (r s : WGRunWitness (Option PeerId)) (pid : PeerId)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Exchange.Event.consumeResponse first r :: between ++ Exchange.Event.consumeResponse second s :: post)
    (accepted₁ : r.value = some pid) (accepted₂ : s.value = some pid) :
    ∃ epoch₁ epoch₂, Exchange.ResponseAt pre pid epoch₁ ∧
      Exchange.ResponseAt (pre ++ Exchange.Event.consumeResponse first r :: between) pid epoch₂ ∧ epoch₁ < epoch₂ :=
  Exchange.initialized_response_once facts config traffic trace placeholders
    pre between post first second r s pid position accepted₁ accepted₂

/-- A completed native session advances the allocation counter once and is
linked to an actual earlier native exchange start in the same initialized execution.
C2 H1's native allocation effect is explicit inside the source-facts package;
no session or history invariant is assumed by this result. -/
theorem initialized_exchange_installation_count (facts : H1DriverSourceFacts)
    (config : H1ConfigurationTagFrames) (traffic : H1TrafficTagFrames)
    (trace : Runner.Trace) (placeholders : Bool) (pre post : List Exchange.Event)
    (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Exchange.Event.session pid r :: post) (success : r.value = true) :
    r.after.keypairCounter = r.before.keypairCounter + 1 ∧
    ∃ epoch, Exchange.InstallAt pre pid epoch ∧ Exchange.Origin pre pid epoch :=
  Exchange.initialized_install_count facts config traffic trace placeholders pre post pid r position success

/-- Replay cannot install a second keypair for the same native exchange:
two successful session receipts have strictly different exchange epochs in
this initialized execution. Named native C2 facts remain explicit; no incoming
history or reachability premise is required. -/
theorem initialized_exchange_installed_once (facts : H1DriverSourceFacts)
    (config : H1ConfigurationTagFrames) (traffic : H1TrafficTagFrames)
    (trace : Runner.Trace) (placeholders : Bool) (pre between post : List Exchange.Event)
    (r s : WGRunWitness Bool) (pid : PeerId)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Exchange.Event.session pid r :: between ++ Exchange.Event.session pid s :: post)
    (accepted₁ : r.value = true) (accepted₂ : s.value = true) :
    ∃ epoch₁ epoch₂, Exchange.InstallAt pre pid epoch₁ ∧
      Exchange.InstallAt (pre ++ Exchange.Event.session pid r :: between) pid epoch₂ ∧ epoch₁ < epoch₂ :=
  Exchange.initialized_install_once facts config traffic trace placeholders
    pre between post r s pid position accepted₁ accepted₂

/-- Replay claims and authenticated effects can observe one handshake
execution: callback-level exchange projections compose through the actual
cookie/MAC prefix and worker, retaining every stopped prefix. This source
projection does not identify unrelated histories from native-result erasure. -/
theorem joint_handshake_exchange_projection (decode : E → Option Exchange.Event)
    (callbacks : AuthenticatedEffects.HandshakeMac → Origins.HandshakeSources.Ops (WGPrefix E))
    (session : PeerId → WGPrefix Exchange.Event Bool) (keepalive : PeerId → WGPrefix Exchange.Event Unit)
    (projects : ∀ mac, AuthenticatedEffects.HandshakeWorker.OpsProjects decode
      (callbacks mac) (ExchangeDriver.receiveOps session keepalive)) :
    StateProjectsPrefix decode id
      (AuthenticatedEffects.HandshakeWorker.observedWith callbacks)
      (ExchangeDriver.worker session keepalive) :=
  ExchangeJoint.worker_exchange decode callbacks session keepalive projects

/-- A successful native session in the initialized execution creates the
actual derived key identified by the entry allocation counter and passes its
slot to the clear/rotation/index suffix. That same receipt zeroes its handshake
tag, preserves every other peer's tag and advances the counter once. Final
role-slot residency remains distinct from this creation and clearing claim. -/
theorem initialized_session_creation_and_clear (facts : H1DriverSourceFacts)
    (config : H1ConfigurationTagFrames) (traffic : H1TrafficTagFrames)
    (trace : Runner.Trace) (placeholders : Bool) (pre post : List Exchange.Event)
    (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Exchange.Event.session pid r :: post) (success : r.value = true) :
    Exchange.SessionMaterialCut pid r ∧ handshakeTagAt r.after pid = some HANDSHAKE_ZEROED ∧
    (∀ target, target ≠ pid → handshakeTagAt r.after target = handshakeTagAt r.before target) ∧
    r.after.keypairCounter = r.before.keypairCounter + 1 :=
  ⟨Exchange.initialized_session_material facts config traffic trace placeholders pre post pid r position success,
    Exchange.initialized_session_clears facts config traffic trace placeholders pre post pid r position success⟩

/-- Every successful initialized session contains exactly one actual
keypairCreate receipt returning a key slot. Its native allocation endpoint
identifies the created allocation rather than inferring existence from a
counter increment; later slot residency is a separate lifetime claim. -/
theorem initialized_session_single_allocation (facts : H1DriverSourceFacts)
    (config : H1ConfigurationTagFrames) (traffic : H1TrafficTagFrames)
    (trace : Runner.Trace) (placeholders : Bool) (pre post : List Exchange.Event)
    (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Exchange.Event.session pid r :: post) (success : r.value = true) :
    ∃ slot allocation device,
      (runWGPrefix (Installation.observed pid) r.before r.ambientBefore []).2 = [allocation] ∧
      allocation.Valid ∧ allocation.execution.value = some slot ∧
      allocation.execution.before.dev = some device ∧ slot = device.nextKeypairId ∧
      allocation.execution.after = Lifetimes.keyAllocationWorld allocation.execution.before device allocation.word :=
  Exchange.initialized_session_allocation facts config traffic trace placeholders pre post pid r position success

/-- A normally refused session leaves the complete WireGuard state unchanged,
including every handshake tag, the key store and allocation counter. This is
tied to its actual receipt in the initialized execution; no incoming state
invariant or successful session premise is assumed. -/
theorem initialized_refused_session_unchanged (facts : H1DriverSourceFacts)
    (config : H1ConfigurationTagFrames) (traffic : H1TrafficTagFrames)
    (trace : Runner.Trace) (placeholders : Bool) (pre post : List Exchange.Event)
    (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (ExchangeDriver.execute trace placeholders) []).2 =
      pre ++ Exchange.Event.session pid r :: post) (refused : r.value = false) : r.after = r.before :=
  Exchange.initialized_session_refusal_world facts config traffic trace placeholders pre post pid r position refused

end Leanux.Proofs.WG.HandshakeSecurity
