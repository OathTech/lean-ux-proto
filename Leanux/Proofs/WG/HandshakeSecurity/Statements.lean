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

/-! Native T4 replay and T5 confirmation boundaries. Initialized history,
authentication linkage and responder-send exclusion remain separate obligations;
these statements do not claim campaign completion. -/
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

end Leanux.Proofs.WG.HandshakeSecurity
