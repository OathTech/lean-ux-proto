import Leanux.Proofs.WG.Noise.DriverTagClaims
import Leanux.Proofs.WG.Noise.DriverTagProductClaims
import Leanux.Proofs.WG.Noise.DriverTagScheduledSource
import Leanux.Proofs.WG.Noise.DriverTagDumpSource
import Leanux.Proofs.WG.Noise.DriverTagConsumeSource
import Leanux.Proofs.WG.Noise.DriverTagConfigurationSource
import Leanux.Proofs.WG.Noise.DriverTagProductSource
import Leanux.Proofs.WG.Noise.DriverTagControlCompleteSource
import Leanux.Proofs.WG.Noise.DriverTagAllowedFrames
import Leanux.Proofs.WG.Noise.ConfirmationUniqueClaims
import Leanux.Proofs.WG.Noise.PendingDispatchSource
import Leanux.Proofs.WG.Noise.PendingPollCompleteSource
import Leanux.Proofs.WG.Noise.PendingReceptionSource
import Leanux.Proofs.WG.Noise.PendingConsumeHistorySource
import Leanux.Proofs.WG.Noise.PendingInvariantFrames
import Leanux.Proofs.WG.Noise.ConfirmationOrderLabels
import Leanux.Proofs.WG.Noise.PendingTicketHandshakeFrames
import Leanux.Proofs.WG.Noise.InitiationCoverageClaims
import Leanux.Proofs.WG.Noise.ConfirmationLabelSource
import Leanux.Proofs.WG.Noise.PendingTicketClearFrames
import Leanux.Proofs.WG.Noise.PendingTicketTimerFrames
import Leanux.Proofs.WG.Noise.ReceiveStepCallerClaims
import Leanux.Proofs.WG.Noise.SocketTagFrames
import Leanux.Proofs.WG.Noise.ReceptionCallerClaims
import Leanux.Proofs.WG.Noise.ClearDispatchClaims
import Leanux.Proofs.WG.Noise.ClearWorkerClaims
import Leanux.Proofs.WG.Noise.SessionEvaluationClaims
import Leanux.Proofs.WG.Noise.InitiationCallerClaims
import Leanux.Proofs.WG.Noise.PeerCreationClaims
import Leanux.Proofs.WG.Noise.SessionRefusalClaims
import Leanux.Proofs.WG.Noise.ResponseCallerClaims
import Leanux.Proofs.WG.Noise.ResponseCallerFinalClaims
import Leanux.Proofs.WG.Noise.CookieReplyTagFrames
import Leanux.Proofs.WG.Noise.PendingTicketFrames
import Leanux.Proofs.WG.Noise.ConsumeConfirmationClaims
import Leanux.Proofs.WG.Noise.ConfirmationTicketClaims
import Leanux.Proofs.WG.Noise.ReceptionTagFrames
import Leanux.Proofs.WG.Noise.ReceiveStepCoverageClaims
import Leanux.Proofs.WG.Noise.ConfirmationOrderClaims
import Leanux.Proofs.WG.Noise.PendingTicketStagingFrames
import Leanux.Proofs.WG.Noise.InitialSlotClaims
import Leanux.Proofs.WG.Noise.InterleavedFreshClaims
import Leanux.Proofs.WG.Noise.FreshHistoryClaims
import Leanux.Proofs.WG.Noise.ConfirmationReinstallClaims
import Leanux.Proofs.WG.Noise.TagSequenceClaims
import Leanux.Proofs.WG.Noise.SessionTagClaims
import Leanux.Proofs.WG.Noise.CreationTagClaims
import Leanux.Proofs.WG.Noise.InitiationTagClaims
import Leanux.Proofs.WG.Noise.ResponseTagClaims
import Leanux.Proofs.WG.Noise.SessionClockClaims
import Leanux.Proofs.WG.Noise.ResponseEdgeClaims
import Leanux.Proofs.WG.Noise.RotationClaims
import Leanux.Proofs.WG.Noise.ConfirmationSequenceClaims
import Leanux.Proofs.WG.Noise.ClearClaims
import Leanux.Proofs.WG.Noise.InitiationReadyClaims
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Noise.ConsumeEdges
import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Noise.RotationSource
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Noise.SessionReadyClaims
import Leanux.Proofs.WG.Noise.ConfirmationSequenceSource

/-! H1's whole-operation contracts and finite mixed native tag histories.
Direct helper reinstallation admits repeated confirmation of one resident key;
the nine-operation confirmation history proves distinct successful IDs under
its explicit initial next/cursor bound. Closure over every driver caller
remains outside this native operation language. -/
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- On normal completion the original rotation implements every C arm:
initiator without next, initiator with next, and responder. -/
theorem original_slot_rotation (pid : PeerId) (newKey : KeypairId)
    (p : Peer) (k : Keypair) :
    Campaign2.Ensures (addNewKeypair pid newKey)
      (fun w => w.peerAt pid = some p ∧
        (w.wg.device.bind fun d => d.keypairs[newKey]?) = some k)
      (fun _ w => ∃ p', w.peerAt pid = some p' ∧
        slots p' = rotate (slots p) k.iAmTheInitiator newKey) :=
  addNewKeypair_slots pid newKey p k

/-- The original confirmation returns true exactly for the pending next
key, then moves current to previous and next to current and clears next. -/
theorem original_confirmation (pid : PeerId) (received : KeypairId) (p : Peer) :
    Campaign2.Ensures (receivedWithKeypair pid received) (fun w => w.peerAt pid = some p)
      (fun ok w => ∃ p', w.peerAt pid = some p' ∧
        (ok, slots p') = confirm (slots p) received) :=
  receivedWithKeypair_slots pid received p

/-- Two adjacent normal confirmation calls for the same key cannot both
succeed. This local result does not assert lifetime uniqueness across intervening rotations. -/
theorem original_confirmation_no_repeat (pid : PeerId) (received : KeypairId)
    (p : Peer) :
    Campaign2.Ensures (do
      let first ← receivedWithKeypair pid received
      let second ← receivedWithKeypair pid received
      pure (first, second))
      (fun s => s.peerAt pid = some p)
      (fun result _ => result.1 = true → result.2 = false) := by
  intro g ambient result final after hp run first
  change (((receivedWithKeypair pid received).run g).run ambient >>= fun ((one, current), middle) =>
    (((receivedWithKeypair pid received).run current).run middle >>= fun ((two, last), ending) =>
      Except.ok (((one, two), last), ending))) = .ok ((result, final), after) at run
  cases hfirst : ((receivedWithKeypair pid received).run g).run ambient with
  | error e => rw [hfirst] at run; cases run
  | ok out =>
    rcases out with ⟨⟨one, current⟩, middle⟩
    rw [hfirst] at run
    change (((receivedWithKeypair pid received).run current).run middle >>= fun ((two, last), ending) =>
      Except.ok (((one, two), last), ending)) = .ok ((result, final), after) at run
    cases hsecond : ((receivedWithKeypair pid received).run current).run middle with
    | error e => rw [hsecond] at run; cases run
    | ok out =>
      rcases out with ⟨⟨two, last⟩, ending⟩
      rw [hsecond] at run
      cases run
      obtain ⟨p', hp', hs⟩ := receivedWithKeypair_slots pid received p
        g ambient one current middle hp hfirst
      have hn : (slots p').next = none := by
        unfold confirm at hs
        split at hs <;> simp_all [Prod.mk.injEq]
      obtain ⟨p'', _, hs'⟩ := receivedWithKeypair_slots pid received p'
        current middle two final after hp' hsecond
      simpa [confirm, hn] using congrArg Prod.fst hs'

/-- Normal keypair clearing empties all three slots and preserves every
other field of the resident peer. Puts occur next, previous, current. -/
theorem original_clear_slots (pid : PeerId) (p : Peer) :
    Campaign2.Ensures (keypairsClear pid) (fun w => w.peerAt pid = some p)
      (fun _ w => w.peerAt pid = some { p with
        keypairNext := none, keypairPrevious := none, keypairCurrent := none }) :=
  keypairsClear_peer pid p

/-- Original handshake zeroing clears exactly the ephemeral material,
hash, chaining key, remote index and state tag, preserving other peer fields. -/
theorem original_handshake_zero (pid : PeerId) (p : Peer) :
    Campaign2.Ensures (handshakeZero pid) (fun w => w.peerAt pid = some p)
      (fun _ w => w.peerAt pid = some { p with
        ephemeralPrivate := List.replicate 32 0, remoteEphemeral := List.replicate 32 0,
        hash := List.replicate 32 0, chainingKey := List.replicate 32 0,
        remoteIndex := 0, handshakeState := 0 }) :=
  handshakeZero_peer pid p

/-- Successful initiation creation sets its owned state tag from any old
state; a normal failure preserves the old tag, not necessarily key material. -/
theorem original_create_initiation_edge (pid : PeerId) (old : Nat) :
    Campaign2.Ensures (createInitiation pid) (fun w => w.tagAt pid = some old)
      (fun result w => w.tagAt pid = some
        (if result.isSome then HANDSHAKE_CREATED_INITIATION else old)) :=
  createInitiation_tag pid old

/-- Response creation succeeds only from consumed initiation and sets
created response; every normal failure preserves the old tag. -/
theorem original_create_response_edge (pid : PeerId) (old : Nat) :
    Campaign2.Ensures (createResponse pid) (fun w => w.tagAt pid = some old)
      (fun result w => w.tagAt pid = some
        (if result.isSome then HANDSHAKE_CREATED_RESPONSE else old) ∧
        (result.isSome → old = HANDSHAKE_CONSUMED_INITIATION)) :=
  createResponse_tag pid old

/-- Normal expiry preserves the peer's three published key slots and
zeroes its handshake tag. Slot clearing is a different operation. -/
theorem original_expiry_slots (pid : PeerId) (p : Peer) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) (fun w => w.peerAt pid = some p)
      (fun _ w => ∃ p', w.peerAt pid = some p' ∧
        slots p' = slots p ∧ p'.handshakeState = 0) :=
  expireCurrentPeerKeypairs_slots pid p

/-- Normal session completion is possible only from created response or
consumed response and zeroes the handshake. A false return preserves its tag. -/
theorem original_begin_session_edge (pid : PeerId) (old : Nat) :
    Campaign2.Ensures (beginSession pid) (fun w => w.tagAt pid = some old)
      (fun ok w => w.tagAt pid = some (if ok then HANDSHAKE_ZEROED else old) ∧
        (ok = true → old = HANDSHAKE_CREATED_RESPONSE ∨ old = HANDSHAKE_CONSUMED_RESPONSE)) :=
  beginSession_tag pid old

/-- A successful initiation consumer returns a resident peer with the
consumed-initiation tag. This endpoint statement does not classify failed prefixes. -/
theorem original_consume_initiation_tag (msg : List UInt8) :
    Campaign2.Ensures (consumeInitiation msg) (fun _ => True)
      (fun result w => ∀ pid, result = some pid →
        w.tagAt pid = some HANDSHAKE_CONSUMED_INITIATION) :=
  consumeInitiation_tag msg

/-- A successful response consumer returns a resident peer with the
consumed-response tag. Authentication provenance is a separate obligation. -/
theorem original_consume_response_tag (msg : List UInt8) :
    Campaign2.Ensures (consumeResponse msg) (fun _ => True)
      (fun result w => ∀ pid, result = some pid →
        w.tagAt pid = some HANDSHAKE_CONSUMED_RESPONSE) :=
  consumeResponse_tag msg

/-- Every normal original clear from a resident peer derives its ordered
next/previous/current release relation. The relation retains the actual slot
writes, table unhashes, reference decrements and final-reference erasures.
Aliases are allowed; no release-readiness witness is assumed. Malformed stores
may stop, so this theorem does not assert completion. -/
theorem original_clear_ordered (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (keypairsClear pid) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧
        ClearRun pid d [.next, .previous, .current] final ∧
        final.peers[pid]? = some { p with
          keypairNext := none, keypairPrevious := none, keypairCurrent := none }) :=
  clear_ordered pid d p resident

/-- Static local reference counts guarantee the original clear completes.
Each referenced key is resident, has a non-NULL peer word, and has at least
as many references as occurrences among the three slots. Repeated identities
are permitted, and the last occurrence may consume the last reference.
No key-owner/peer identity, queue, or record-stream premise is required. -/
theorem original_clear_ready_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (ready : ClearReady d (clearKeys p)) :
    Campaign2.Returns (keypairsClear pid) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧
        ClearRun pid d [.next, .previous, .current] final ∧
        final.peers[pid]? = some { p with
          keypairNext := none, keypairPrevious := none, keypairCurrent := none }) :=
  clear_ready_returns pid d p resident ready

/-- Every normal original rotation derives the exact ordered peer writes and
immediate releases, including table removals, decrements and final erasures.
Aliased slots and aliases of the new key are allowed. This does not assert
completion or residency of every key named by the resulting slots. -/
theorem original_rotation_ordered (pid : PeerId) (newKey : KeypairId)
    (d : Device) (p : Peer) (k : Keypair)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[newKey]? = some k) :
    Campaign2.Ensures (addNewKeypair pid newKey) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧
        RotationRun pid d (rotationPlan p k.iAmTheInitiator newKey) final ∧
        final.peers[pid]? = some (rotationPeer (rotationPlan p k.iAmTheInitiator newKey) p)) :=
  rotation_ordered pid newKey d p k resident key

/-- A resident new key supplies the role test. Static reference multiplicities
for precisely the released old slots guarantee normal completion, without
assuming an ordered run witness or distinct identities. The budget permits a
last release to erase a key still named by a resulting slot; no slot/store
coherence or allocation-lifetime uniqueness is claimed. -/
theorem original_rotation_ready_returns (pid : PeerId) (newKey : KeypairId)
    (d : Device) (p : Peer) (k : Keypair)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[newKey]? = some k)
    (ready : ClearReady d (rotationReleases (rotationPlan p k.iAmTheInitiator newKey))) :
    Campaign2.Returns (addNewKeypair pid newKey) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧
        RotationRun pid d (rotationPlan p k.iAmTheInitiator newKey) final ∧
        final.peers[pid]? = some (rotationPeer (rotationPlan p k.iAmTheInitiator newKey) p)) :=
  rotation_ready_returns pid newKey d p k resident key ready

/-- Normal confirmation either returns false with the original Device, or
performs the exact previous-slot write, old-previous release and current/next
write. No received-key residency, ownership or distinctness premise is added. -/
theorem original_confirmation_ordered (pid : PeerId) (received : KeypairId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (receivedWithKeypair pid received) (fun s => s.wg.device = some d)
      (fun ok s => ∃ final, s.wg.device = some final ∧ ConfirmationEffect pid received d p ok final ∧
        final.peers[pid]? = some (if ok then rotationPeer (confirmationPlan p received) p else p)) :=
  confirmation_ordered pid received d p resident

/-- The next-slot mismatch needs no release budget. When it matches, static
readiness for the old previous slot guarantees completion. The confirmed key
need not be resident, and aliasing may let the release erase it; this is an
exact local effect, not a lifetime or reachable-coherence invariant. -/
theorem original_confirmation_ready_returns (pid : PeerId) (received : KeypairId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (ready : p.keypairNext = some received → ClearReady d [p.keypairPrevious]) :
    Campaign2.Returns (receivedWithKeypair pid received) (fun s => s.wg.device = some d)
      (fun ok s => ∃ final, s.wg.device = some final ∧ ConfirmationEffect pid received d p ok final ∧
        final.peers[pid]? = some (if ok then rotationPeer (confirmationPlan p received) p else p)) :=
  confirmation_ready_returns pid received d p resident ready

/-- Every normal original session return has the exact allocation, role/remote-index,
derived-key, handshake-zero, ordered rotation/release and index-replacement effects.
False returns preserve the Device and allocation counter, even when allocation
records were consumed. True returns use an existential birthdate from the original
derivation; an exposed clock observation is separate. No freshness, distinctness
or successful-release premise is assumed, and aliasing may erase the allocated
key before it is installed in the final table. Completion and lifetime coherence
are not asserted. -/
theorem original_begin_session_ordered (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (beginSession pid)
      (fun s => s.wg.device = some d ∧ s.wg.keypairCounter = counter)
      (fun ok s => ∃ final, s.wg.device = some final ∧
        SessionEffect pid d p counter ok final s.wg.keypairCounter) :=
  beginSession_effect pid d p counter resident

/-- The original session call returns true for every realization with an accepted
live handshake, a non-null stored peer word, a hashed handshake entry, static
release readiness after the actual allocation overwrite, and valid armed
allocation-success and birthdate records. The same run has all ordered
`SessionEffect` effects. Safe allocation-ID aliases are retained; final key
residency/coherence and a reachable-state invariant are not asserted. -/
theorem original_begin_session_ready (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p)
    (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨
      p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE)
    (alive : p.isDead = false) (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (ready : SessionReady d p counter) (allocation clock : List UInt8)
    (allocWidth : allocation.length = 40) (allocSuccess : allocation.headD 2 = 1)
    (clockWidth : clock.length = 8) (rest : List HiddenRecord) :
    Campaign2.Returns (beginSession pid)
      (fun s => (s.wg.device = some d ∧ s.wg.keypairCounter = counter) ∧
        s.ambient.hidden = some (sessionReadyRecords allocation clock rest) ∧
        s.ambient.allocArmed.contains "kzallocKeypair" = true)
      (fun ok s => ok = true ∧ ∃ final, s.wg.device = some final ∧
        SessionEffect pid d p counter ok final s.wg.keypairCounter) :=
  beginSession_ready_projected pid d p counter resident accepted alive word hashed ready
    allocation clock allocWidth allocSuccess clockWidth rest

/-- Consecutive original confirmation calls, without an interleaved next-slot
installation, return true only at the first input matching the initial next slot.
On normal return the whole Device effect is that one ordered confirmation, or
no change if there is no match; all remaining results are false. A successful
match leaves next empty. Only initial caller residency is assumed. Aliased
releases remain allowed, so this is neither key lifetime safety nor confirmation
uniqueness across a larger execution that can install next again. -/
theorem original_confirmation_sequence (pid : PeerId) (ids : List KeypairId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (ids.mapM (receivedWithKeypair pid)) (fun s => s.wg.device = some d)
      (fun results s => ∃ final, s.wg.device = some final ∧
        ConfirmationSequenceEffect pid ids d p results final ∧
        results.length = ids.length ∧ results.count true ≤ 1) :=
  confirmation_sequence pid ids d p resident

/-- Static release readiness for the initial previous slot is required only if
some input matches the initial next slot. It guarantees termination of these
finite original calls and the same first-match effect. No supplied execution
witness, received-key residency or distinctness premise is used; stopped calls
without this readiness premise are not asserted to complete. -/
theorem original_confirmation_sequence_ready_returns (pid : PeerId) (ids : List KeypairId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (ready : (∃ id ∈ ids, p.keypairNext = some id) → ClearReady d [p.keypairPrevious]) :
    Campaign2.Returns (ids.mapM (receivedWithKeypair pid)) (fun s => s.wg.device = some d)
      (fun results s => ∃ final, s.wg.device = some final ∧
        ConfirmationSequenceEffect pid ids d p results final ∧
        results.length = ids.length ∧ results.count true ≤ 1) :=
  confirmation_sequence_ready_returns pid ids d p resident ready

/-- The original initiation returns its exact message and ordered Device/index
updates from a resident peer, an identity, a non-null handshake peer word, pure
crypto success guards, and supplied ephemeral/clock/collision-then-fresh records.
It consumes exactly that prefix and preserves timer-record mode. This needs no
successful-execution premise, owner coherence or previous handshake state.
It does not claim a fixed wire-message length for arbitrary identity fields,
send/rearm behavior, or a reachable-state invariant. -/
theorem original_create_initiation_ready (pid : PeerId) (d : Device) (p : Peer) (mode : Bool)
    (resident : d.peers[pid]? = some p) (identity : d.staticIdentity.hasIdentity = true)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : p.precomputedStaticStatic ≠ List.replicate 32 0)
    (ephemeral clock : List UInt8) (randomWidth : ephemeral.length = 32) (width : clock.length = 16)
    (secretNonNull : clamp ephemeral ≠ nullPoint)
    (pubOk : (curve25519 (clamp ephemeral) basePoint).2 = true)
    (dhOk : (curve25519 (clamp ephemeral) p.remoteStatic).2 = true)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Campaign2.Returns (createInitiation pid)
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some ({site := 1, bytes := ephemeral} ::
        {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest) ∧ s.ambient.armRecords = mode)
      (fun out s => out = some (InitiationReady.result pid d p ephemeral clock fresh.value).1 ∧
        s.wg.device = some (InitiationReady.result pid d p ephemeral clock fresh.value).2 ∧ s.ambient.hidden = some rest ∧ s.ambient.armRecords = mode) :=
  InitiationReady.createInitiation_projected pid d p mode resident identity word nonnull
    ephemeral clock randomWidth width secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh

/-- Whole response consumption returns a peer only from its entry
created-initiation state and leaves it in consumed-response state. This derives
the initial tag from the actual successful run; it assumes no owner coherence,
residency or record readiness and does not describe failed-call rollback. -/
theorem original_consume_response_entry_edge (msg : List UInt8) (before : Campaign2.Snapshot) :
    Campaign2.Ensures (consumeResponse msg) (fun s => s = before)
      (fun result after => ∀ pid, result = some pid →
        before.tagAt pid = some HANDSHAKE_CREATED_INITIATION ∧
        after.tagAt pid = some HANDSHAKE_CONSUMED_RESPONSE) :=
  consumeResponse_entry_edge msg before

/-- The actual session derivation clock supplies the successful birthdate;
normal refusal has no derivation receipt and preserves Device and counter. -/
theorem original_begin_session_clock (pid : PeerId) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures
      (TimerDiscipline.observed (liftWG (beginSession pid)) (sessionClockPath pid))
      (fun s => s = entry)
      (fun result final => SessionClockObservation pid entry result.1 result.2 final) :=
  beginSession_clock_observation pid entry

/-- Every normal response-consumption refusal preserves all peer state tags.
Success changes only the returned peer from created initiation to consumed
response. Absent peers remain absent, and all source Stops retain their domain;
Device rollback, completion and whole-driver edge ownership are not claimed. -/
theorem original_consume_response_tag_map (msg : List UInt8) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (consumeResponse msg) (fun s => s = entry)
      (fun result after =>
        (∀pid, after.tagAt pid = if result = some pid then
          some HANDSHAKE_CONSUMED_RESPONSE else entry.tagAt pid) ∧
        (∀pid, result = some pid → entry.tagAt pid = some HANDSHAKE_CREATED_INITIATION)) :=
  consumeResponse_tagMap_projected msg entry

/-- Every normal initiation-consumption refusal preserves all peer tags;
success changes only the returned peer to consumed initiation. No prior state
tag, reference budget, alias restriction or ready record stream is assumed.
This is a normal-return edge contract, not a completion or rollback claim. -/
theorem original_consume_initiation_tag_map (msg : List UInt8) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (consumeInitiation msg) (fun s => s = entry)
      (fun result after => ∀pid, after.tagAt pid = if result = some pid then
        some HANDSHAKE_CONSUMED_INITIATION else entry.tagAt pid) :=
  consumeInitiation_tagMap_projected msg entry

/-- Whole normal creation effect on every peer tag, with all actual Stops
retained. This makes no completion, full-state rollback or owner-word claim. -/
theorem original_create_initiation_tag_map (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (createInitiation pid) (fun s => s = entry)
      (fun result after => (∀target, after.tagAt target =
        if result.isSome then
          if pid = target then some HANDSHAKE_CREATED_INITIATION else entry.tagAt target
        else entry.tagAt target)) :=
  createInitiation_tagMap_projected pid entry

/-- Whole normal creation effect on every peer tag, with all actual Stops
retained. This makes no completion, full-state rollback or owner-word claim. -/
theorem original_create_response_tag_map (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (createResponse pid) (fun s => s = entry)
      (fun result after => (∀target, after.tagAt target =
        if result.isSome then
          if pid = target then some HANDSHAKE_CREATED_RESPONSE else entry.tagAt target
        else entry.tagAt target) ∧
        (result.isSome → entry.tagAt pid = some HANDSHAKE_CONSUMED_INITIATION)) :=
  createResponse_tagMap_projected pid entry

/-- The whole session operation preserves all tags on normal false and zeroes
only its peer on normal true, from an actual accepted old tag. Arbitrary optional
entry states, aliased slots and records remain; no readiness or budget premise. -/
theorem original_begin_session_tag_map (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (beginSession pid) (fun s => s = entry)
      (fun ok after => (∀target, after.tagAt target =
        if ok then if pid = target then some HANDSHAKE_ZEROED else entry.tagAt target
        else entry.tagAt target) ∧
        (ok = true → entry.tagAt pid = some HANDSHAKE_CREATED_RESPONSE ∨
          entry.tagAt pid = some HANDSHAKE_CONSUMED_RESPONSE)) :=
  beginSession_tagMap_projected pid entry

/-- Original handshake clearing zeroes only the requested tag on normal return.
Missing peers or NULL owner words keep the actual failures. -/
theorem original_handshake_clear_tag_map (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (handshakeClear pid) (fun s => s = entry)
      (fun _ after => ∀target, after.tagAt target =
        if pid = target then some HANDSHAKE_ZEROED else entry.tagAt target) :=
  handshakeClear_tagMap_projected pid entry

/-- Whole expiry zeroes only the requested tag, including the real reset clock
and ordered optional key invalidations. This is normal-return partiality, not
clock readiness, reference safety, or completion. -/
theorem original_expire_current_tag_map (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) (fun s => s = entry)
      (fun _ after => ∀target, after.tagAt target =
        if pid = target then some HANDSHAKE_ZEROED else entry.tagAt target) :=
  expireCurrentPeerKeypairs_tagMap_projected pid entry

/-- A finite supplied list of original native handshake calls has exactly the
linked all-peer tag edges its owners implement, including arbitrary-tag
initiation restarts and normal-refusal stutters. Erasure preserves the first
Stop; this partial claim is not a driver scheduler, lifetime-confirmation or
reachable-state theorem, and does not return a partial history on failure. -/
theorem original_mixed_tag_history (operations : List TagOperation) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observedTagSequence operations) (fun s => s = entry)
      (fun receipts final => TagChain entry operations receipts final) :=
  observedTagSequence_chain operations entry

/-- Direct responder helper reinstallation permits two confirmations of the
same resident key. It is not a fresh-session or initialized-driver trace. -/
theorem original_confirmation_reinstallation_counterexample :
    ∃ d : Device, ∃ k : Keypair,
      d.keypairs[0]? = some k ∧ k.internalId = 17 ∧
      Campaign2.Observes ConfirmationReinstallWitness.calls (fun entry => entry.wg.device = some d)
        (fun entry out => ∃ after final,
          out = .ok ((true, true), after) ∧ after.wg.device = some final ∧
          final.keypairs[0]? = some k ∧
          after.wg.keypairCounter = entry.wg.keypairCounter ∧
          final.nextKeypairId = d.nextKeypairId) :=
  confirmation_same_allocation_reinstallation


/-- The finite nine-operation handshake/session/confirmation/clearing language
executes the original calls and preserves their first Stop. From the explicit initial
next-slot bound, every normal complete history has pairwise distinct successful
confirmation IDs. No readiness, reference-budget, coherence or alias premise
is assumed. This is not a whole-driver or initialized lifetime theorem. -/
theorem original_fresh_confirmation_history (pid : PeerId)
    (operations : List FreshOperation) (entry : Campaign2.Snapshot) :
    Campaign2.AgreesOn (fun _ => True)
      (do let receipts ← observedFreshSequence pid operations
          pure (receipts.map FreshReceipt.result)) (runFreshSequence pid operations) ∧
    Campaign2.Ensures (observedFreshSequence pid operations)
      (fun s => s = entry ∧ FreshNextBound pid entry)
      (fun receipts final => FreshChain pid entry operations receipts final ∧
        (freshConfirmedIds receipts).Nodup) := by
  refine ⟨?_,fresh_confirmation_history pid operations entry⟩
  rw [observedFreshSequence_erase]
  intro g ambient _
  rfl

/-- Arbitrary-peer interleavings of the nine original native lifecycle calls
retain distinct successful confirmation IDs for each tracked peer under its
initial next/cursor bound. Observation erasure preserves complete native
results, state and first Stop. Shared initial next IDs are allowed: global
cross-peer uniqueness, key residency, peer recreation and device reset are
not concluded. This is a finite native history, not initialized runner closure. -/
theorem original_interleaved_confirmation_history (tracked : PeerId)
    (operations : List InterleavedFreshOperation) (entry : Campaign2.Snapshot) :
    Campaign2.AgreesOn (fun _ => True)
      (do let receipts ← observedInterleavedFreshSequence operations
          pure (receipts.map fun receipt => receipt.call.result))
      (runInterleavedFreshSequence operations) ∧
    Campaign2.Ensures (observedInterleavedFreshSequence operations)
      (fun s => s = entry ∧ FreshNextBound tracked entry)
      (fun receipts final => InterleavedFreshChain tracked entry operations receipts final ∧
        (interleavedConfirmedIds tracked receipts).Nodup) := by
  refine ⟨?_,interleaved_fresh_confirmation_history tracked operations entry⟩
  rw [observedInterleavedFreshSequence_erase]
  intro g ambient _
  rfl

/-- Initial per-occurrence slot credits and the shared slot bound ensure
recorded successful session installation. The same run retains enough credits
for the selected peer's final slots. Old-slot aliases are allowed; the cursor
bound excludes an old slot naming the fresh allocation ID. -/
theorem original_session_initial_slot_credits
    (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p)
    (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨
      p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE)
    (alive : p.isDead = false) (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (slots : CurrentSlots.SlotInv (Affiliation.state d))
    (credits : ClearReady d (clearKeys p))
    (allocation clock : List UInt8)
    (allocWidth : allocation.length = 40) (allocSuccess : allocation.headD 2 = 1)
    (clockWidth : clock.length = 8) (rest : List HiddenRecord) :
    Campaign2.Returns (beginSession pid)
      (fun s => (s.wg.device = some d ∧ s.wg.keypairCounter = counter) ∧
        s.ambient.hidden = some (sessionReadyRecords allocation clock rest) ∧
        s.ambient.allocArmed.contains "kzallocKeypair" = true)
      (fun ok s => ok = true ∧ ∃ final, s.wg.device = some final ∧
        SessionEffect pid d p counter ok final s.wg.keypairCounter ∧
        ∃ after, final.peers[pid]? = some after ∧ ClearReady final (clearKeys after)) :=
  beginSession_initial_slots_projected pid d p counter resident accepted alive word hashed
    slots credits allocation clock allocWidth allocSuccess clockWidth rest

/-- The actual response sender records creation alone on refusal, or creation
then session on a created message. Each projected receipt has an actual native
helper witness and its allowed local tag edge. Discarding observation preserves
every original result and Stop. Final tag framing and writes inside a stopped
helper are separate claims. -/
theorem original_response_caller_receipts (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← ResponseCaller.observeProjected pid; pure ())
      (sendHandshakeResponse pid) ∧
    Campaign2.Ensures (ResponseCaller.observeProjected pid) (fun _ => True)
      (fun receipts _ => ResponseCaller.ReceiptShape pid receipts ∧
        ∀ receipt ∈ receipts,
          ResponseCaller.ReceiptValid receipt ∧ TagReceiptEffect receipt) :=
  ⟨ResponseCaller.original_response_receipts_erases pid,
    ResponseCaller.original_response_receipts pid⟩

/-- A resident caller outside the two response states returns false without
allocation, clock or credit assumptions. The device and key counter are unchanged;
Ambient branch observations are retained. -/
theorem original_session_role_refusal (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (resident : d.peers[pid]? = some p)
    (notCreated : p.handshakeState ≠ HANDSHAKE_CREATED_RESPONSE)
    (notConsumed : p.handshakeState ≠ HANDSHAKE_CONSUMED_RESPONSE) :
    Campaign2.Returns (beginSession pid)
      (fun s => s.wg.device = some d ∧ s.wg.keypairCounter = counter)
      (fun ok s => ok = false ∧ s.wg.device = some d ∧ s.wg.keypairCounter = counter) :=
  beginSession_rejected_projected pid d p counter resident notCreated notConsumed

/-- A well-formed armed allocation refusal returns false, consumes exactly its
record and preserves the device and key counter. The suffix is arbitrary and
no liveness, owner-word, slot, hash or clock premise is needed. -/
theorem original_session_allocation_refusal (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (resident : d.peers[pid]? = some p)
    (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨
      p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE)
    (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 40) (refused : bytes.headD 2 = 0) :
    Campaign2.Returns (beginSession pid)
      (fun s => s.wg.device = some d ∧ s.wg.keypairCounter = counter ∧
        s.ambient.hidden = some ({site := (HiddenSite.alloc .kzallocKeypair).info.id, bytes := bytes} :: rest) ∧
        s.ambient.allocArmed.contains "kzallocKeypair" = true)
      (fun ok s => ok = false ∧ s.wg.device = some d ∧
        s.wg.keypairCounter = counter ∧ s.ambient.hidden = some rest) :=
  beginSession_allocation_refused_projected pid d p counter resident accepted
    bytes rest width refused

/-- On normal completion the response caller's initial tags reach its creation receipt unchanged,
and creation's tags reach the session receipt unchanged. With two receipts the
initial tag is consumed initiation and session entry is created response, even
when session returns false. This links actual helper cuts and leaves the final
caller tag map and stopped-helper writes to their separate claims. -/
theorem original_response_caller_tag_provenance
    (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (ResponseCaller.observeProjected pid)
      (fun s => s.tagAt = entry.tagAt)
      (fun receipts _ => ResponseCaller.ReceiptShape pid receipts ∧
        ResponseCaller.ReceiptChain entry receipts ∧
        ResponseCaller.ReceiptRoles pid entry receipts ∧
        ∀ receipt ∈ receipts,
          ResponseCaller.ReceiptValid receipt ∧ TagReceiptEffect receipt) :=
  ResponseCaller.original_response_receipt_chain pid entry

/-- Normal peer creation sets exactly its returned location to the zero tag;
numeric refusal preserves all optional tags. Cursor overwrite is included,
so this is a lifetime initialization effect, not a handshake protocol edge. -/
theorem original_peer_creation_tags (publicKey : Key) (psk : Option Key)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (peerCreate publicKey psk) (fun s => s.tagAt = entry.tagAt)
      (fun result after => ∀ target, after.tagAt target = match result with
        | .error _ => entry.tagAt target
        | .ok pid => if pid = target then some HANDSHAKE_ZEROED else entry.tagAt target) :=
  peerCreate_tag_map publicKey psk entry

/-- The actual initiation sender classifies its rate guard and, when reached,
records the one original creator with its returned value and initial tag map.
Refusal may retain other writes; creation does not imply delivery. Every
original outcome survives discarding observation, including Stops. -/
theorem original_initiation_caller_receipts (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← InitiationCaller.observe pid; pure ()) (sendHandshakeInitiation pid) ∧
    Campaign2.Ensures (InitiationCaller.observe pid) (fun s => s = entry)
      (fun call _ => InitiationCaller.RateObserved pid entry call ∧
        InitiationCaller.CallFacts pid entry call) :=
  ⟨InitiationCaller.original_initiation_receipts_erases pid,
    InitiationCaller.original_initiation_receipts pid entry⟩

/-- The original send worker retains the same actual guard and creator receipt
through its final peer release. Receipt state is the creator cut; the final
release can remove the peer. Later failures remain Stops without a receipt. -/
theorem original_initiation_worker_receipts (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← InitiationCaller.observeWorker pid; pure ()) (handshakeSendWorker pid) ∧
    Campaign2.Ensures (InitiationCaller.observeWorker pid) (fun s => s = entry)
      (fun call _ => InitiationCaller.RateObserved pid entry call ∧
        InitiationCaller.CallFacts pid entry call) :=
  ⟨InitiationCaller.original_initiation_worker_receipts_erases pid,
    InitiationCaller.original_initiation_worker_receipts pid entry⟩

/-- The whole original session agrees on every input with its finite outcome
evaluator: allocation bypasses or calls one concrete native encounter, then
uses the fixed native session suffix. Stops remain exact outcomes; this does
not assert successful completion, a runtime bound or initialized reachability. -/
theorem original_session_finite_evaluation (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (beginSession pid) (SessionEvaluation.evaluate pid) :=
  SessionEvaluation.original_session_finite pid

/-- A normally completed zero-key worker preserves all other optional tags.
Its own tag is absent exactly at the entry peer's last reference, and zero
otherwise. The actual execution supplies initial residency and positivity;
no slot, clock, owner-word or queue readiness premise is assumed. -/
theorem original_clear_worker_tags (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid) (fun s => s = entry)
      (fun _ final => ∃ p, entry.peerAt pid = some p ∧ 0 < p.refcount ∧
        ∀ target, final.tagAt target =
          if pid = target then
            if p.refcount = 1 then none else some HANDSHAKE_ZEROED
          else entry.tagAt target) :=
  ClearWorker.original_queued_clear_tags pid entry

/-- Normal handshake receipt classifies the actual load/MAC dispatch:
cookie input, MAC drop, cookie-reply attempt, initiation or response. Consumer
receipts are nonempty exactly on consumer dispatch and retain actual helper
runs, result order and local edges. All-outcome erasure retains every Stop;
receipt cuts need not agree with each other or the whole caller's final tags. -/
theorem original_reception_caller_dispatch (msg : List UInt8) (src : SkbSource) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← ReceptionCaller.observeClassified msg src; pure ())
      (receiveHandshakePacket msg src) ∧
    Campaign2.Ensures (ReceptionCaller.observeClassified msg src) (fun _ => True)
      (fun call _ =>
        ReceptionCaller.EntryShape msg call ∧
        ReceptionCaller.GateEntryValid msg src call.gate ∧
        ReceptionCaller.dispatchKind msg call.gate ≠ .wrongType ∧
        (call.receipts ≠ [] ↔ ReceptionCaller.dispatchKind msg call.gate = .initiation ∨
          ReceptionCaller.dispatchKind msg call.gate = .response) ∧
        ∀ r ∈ call.receipts, ReceptionCaller.ReceiptValid r ∧ TagReceiptEffect r) :=
  ⟨ReceptionCaller.original_reception_dispatch_erases msg src,
    ReceptionCaller.original_reception_dispatch msg src⟩

/-- Normal actual clear-work dispatch derives its selected queue member and
initial peer/refcount, then preserves other tags and deletes that peer exactly
at its last reference, otherwise retaining zero. Selection and section
failures remain Stops; no readiness or successful-worker premise is supplied. -/
theorem original_clear_worker_dispatch_tags (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures Env.runOneClearWorker (fun s => s = entry)
      (fun _ final => ∃ pid d p,
        Index.clearWorkerSelected entry = some pid ∧
        entry.wg.device = some d ∧ pid ∈ d.clearWorkQueue ∧
        entry.toSnapshot.peerAt pid = some p ∧ 0 < p.refcount ∧
        ∀ target, final.toSnapshot.tagAt target =
          if pid = target then
            if p.refcount = 1 then none else some HANDSHAKE_ZEROED
          else entry.toSnapshot.tagAt target) :=
  ClearWorkerDispatch.original_clear_dispatch_tags entry

/-- The original receive step polls the entry ring. An empty poll returns
false; a consumed packet returns true with its actual reception dispatch and
valid helper receipts. Dequeue precedes reception and counter decrement follows
its success. Discarding receipts preserves every original result and Stop. -/
theorem original_receive_step_dispatch (entry : Campaign2.Snapshot) :
    Campaign2.AgreesOn (fun _ => True)
      (do let r ← ReceiveStepCaller.observeStep; pure r.poll.value) receiveStep ∧
    Campaign2.Ensures ReceiveStepCaller.observeStep (fun s => s = entry)
      (fun r _ => r.entry = entry ∧ ReceiveStepCaller.PollShape r.entry r.poll) :=
  ⟨ReceiveStepCaller.original_receiveStep_receipt_erases,
    ReceiveStepCaller.original_receiveStep_receipt entry⟩

/-- The original response call connects its entry, actual helper receipts, and
final handshake tags, with concrete socket and timer frames. -/
theorem original_response_final_tags (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (ResponseCaller.observeProjected pid)
      (fun s => s.tagAt = entry.tagAt)
      (fun receipts final => ResponseCaller.ReceiptShape pid receipts ∧
        ResponseCaller.ReceiptChain entry receipts ∧
        ResponseCaller.ReceiptRoles pid entry receipts ∧
        ResponseCaller.ReceiptFinalTags receipts final ∧
        ∀ receipt ∈ receipts,
          ResponseCaller.ReceiptValid receipt ∧ TagReceiptEffect receipt) :=
  ResponseCaller.original_response_receipt_final_tags pid entry

/-- Every projected initialized consume occurrence carries its actual resident
allocation identity and the original pending-ticket confirmation transition.
This does not assume the whole-run pending-history invariant. -/
theorem original_initialized_confirmation_allocation (trace : Leanux.Runner.Trace)
    (placeholders : Bool) (n id : Nat) (stamp : Lifetimes.PacketStamp)
    (observation : ConsumeConfirmation.ConfirmationObservation)
    (occurs : CounterConsume.Occurs trace placeholders n id stamp observation) :
    observation.Valid ∧ observation.Facts ∧ ∃ allocation,
      ConsumeConfirmation.projectedStampAt observation.entry observation.packet.keypair =
        some allocation ∧
      PendingTickets.Step (PendingTickets.projected observation.entry)
        (if observation.confirmed then some allocation else none)
        (PendingTickets.projected observation.after) := by
  have facts := CounterConsume.initialized_confirmation_stamped
    trace placeholders n id stamp observation occurs
  exact ⟨facts.1,facts.2.1,CounterConsume.initialized_confirmation_transition
    trace placeholders n id stamp observation occurs⟩

/-- Every surviving final tag of the original normal reception call is traced
through its actual checked consumer receipts. MAC dispatch and receipt validity
remain part of the conclusion; helper frames are discharged, not assumed. -/
theorem original_reception_final_tags (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (ReceptionCaller.observeClassified msg src) (fun s => s = entry)
      (fun call final => ReceiveStepCaller.ReceptionShape msg src call ∧
        TagCoverage entry.tagAt call.receipts final.tagAt) :=
  ReceptionCaller.original_reception_tag_coverage msg src entry

/-- The actual receive step links every surviving final tag to its entry and
ordered reception receipts, including empty polls and peer deletion. This is
a normal-return contract; the separate erasure preserves every original Stop. -/
theorem original_receive_step_final_tags (entry : Campaign2.Snapshot) :
    Campaign2.Ensures ReceiveStepCaller.observeStep (fun s => s = entry)
      (fun r final => r.entry = entry ∧ ReceiveStepCaller.PollShape r.entry r.poll ∧
        TagCoverage entry.tagAt r.poll.receipts final.tagAt) :=
  ReceiveStepCaller.original_receiveStep_tag_coverage entry

/-- Every completed consume receipt in the initialized runner has exactly one
ordered projected observation with its actual allocation identity. The list
includes false confirmations and committed receipts before a later Stop.
The successful identity list is exact; its distinctness remains a separate
lifetime obligation. -/
theorem original_initialized_confirmation_order (trace : Leanux.Runner.Trace)
    (placeholders : Bool) :
    ∃ qs,
      ConfirmationOrder.observations trace placeholders = .ok qs ∧
      ConfirmationOrder.confirmationIds trace placeholders =
        .ok (ConfirmationOrder.successful qs) ∧
      qs.Pairwise (fun a b => a.position < b.position) ∧
      qs.length = ConfirmationOrder.consumedCount (ConfirmationOrder.history trace placeholders) ∧
      (∀ q, q ∈ qs ↔ ConfirmationOrder.OccursAt trace placeholders q) ∧
      (∀ q ∈ qs,
        q.observation.Valid ∧ q.observation.Facts ∧
        ConsumeConfirmation.projectedStampAt q.observation.entry q.observation.packet.keypair =
          some q.internalId ∧
        (q.observation.confirmed = true → q.observation.ConfirmedStamp q.internalId)) :=
  ConfirmationOrder.initialized_complete trace placeholders

/-- The normal original initiation sender connects entry and final tags through
its actual creator receipt, retaining the rate guard and receipt validity. -/
theorem original_initiation_final_tags (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (InitiationCaller.observe pid) (fun s => s = entry)
      (fun call final => InitiationCaller.RateObserved pid entry call ∧
        InitiationCaller.CallFacts pid entry call ∧
        TagCoverage entry.tagAt call.receipts final.tagAt) :=
  InitiationCaller.original_initiation_tag_coverage pid entry

/-- The original send worker retains the same entry-to-final tag coverage
through final peer release, including actual peer deletion without an initial
reference-readiness premise. Successful creation does not imply delivery. -/
theorem original_initiation_worker_final_tags (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (InitiationCaller.observeWorker pid) (fun s => s = entry)
      (fun call final => InitiationCaller.RateObserved pid entry call ∧
        InitiationCaller.CallFacts pid entry call ∧
        TagCoverage entry.tagAt call.receipts final.tagAt) :=
  InitiationCaller.original_initiation_worker_tag_coverage pid entry

/-- Every completed initialized consume transports its actual internalId
confirmation transition through the original caller's final state, including
normal packet drops. The whole initialized history's distinctness is separate. -/
theorem original_initialized_complete_confirmation_transition (trace : Leanux.Runner.Trace)
    (placeholders : Bool) (n id : Nat) (stamp : Lifetimes.PacketStamp)
    (observation : ConsumeConfirmation.ConfirmationObservation)
    (occurs : CounterConsume.Occurs trace placeholders n id stamp observation) :
    observation.Valid ∧ observation.Facts ∧ ∃ allocation,
      ConsumeConfirmation.projectedStampAt observation.entry observation.packet.keypair =
        some allocation ∧
      PendingTickets.Step (PendingTickets.projected observation.entry)
        (if observation.confirmed then some allocation else none)
        (PendingTickets.projected observation.finish) :=
  CounterConsume.initialized_completed_transition trace placeholders n id stamp observation occurs

/-- Direct labels of the actual initialized journal equal the ordered
extractor's successful internalId list, preserving order and multiplicity.
Completed prefixes before an outer Stop are included; no uniqueness premise
or conclusion is added. -/
theorem original_initialized_confirmation_labels (trace : Leanux.Runner.Trace)
    (placeholders : Bool) :
    ConfirmationOrder.confirmationIds trace placeholders =
      .ok (CounterConsume.confirmationLabels (ConfirmationOrder.history trace placeholders)) :=
  ConfirmationOrder.initialized_confirmationIds_labels trace placeholders

/-- The original initialized runner's successful completed confirmations have
distinct internalId values. This includes device recreation, either placeholder
mode and committed receipts before a later outer Stop. No supplied invariant,
successful termination or callback-preservation premise remains. -/
theorem original_initialized_confirmation_unique (trace : Leanux.Runner.Trace)
    (placeholders : Bool) :
    ∃ ids, ConfirmationOrder.confirmationIds trace placeholders = .ok ids ∧ ids.Nodup :=
  ConfirmationOrder.initialized_distinct trace placeholders

/-- Actual peer creation records its normal allocation and tag-initialization
receipt. Inspection reports the original result or Stop; normal outcomes have
tag coverage, and every emitted receipt has its own original execution witness. -/
theorem original_peer_creation_driver_tags (key : Key) (psk : Option Key)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved (DriverTags.peerCreateObserved key psk))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved (DriverTags.peerCreateObserved key psk); pure out.1)
      (Campaign2.inspect (peerCreate key psk)) :=
  ⟨DriverTags.peerCreate_inspection key psk entry,
    DriverTags.inspection_erases _ _ (DriverTags.peerCreateObserved_erases key psk)⟩

/-- The original bounded work drain traces surviving normal final tags through
actual helper receipts, including work on other peers and the selected-clear early return.
Its exact original failures are retained; Stop guarantees receipt validity,
not coverage of writes inside an incomplete worker callback. -/
theorem original_work_drain_driver_tags (upTo : Option PeerId)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved (DriverTags.Flush.drainObserved upTo))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved (DriverTags.Flush.drainObserved upTo); pure out.1)
      (Campaign2.inspect (drainHandshakeSendWq upTo)) :=
  ⟨DriverTags.inspection_facts _ (fun tags => DriverTags.Flush.drainObserved_preserves tags upTo) entry,
    DriverTags.inspection_erases _ _ (DriverTags.Flush.drainObserved_erases upTo)⟩

/-- Timer stop includes its actual conditional work drain, rather than treating
that drain as tag-silent. Normal tag coverage and valid reported receipts hold
without a readiness premise; inspection retains every original outcome. -/
theorem original_timer_stop_driver_tags (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved (DriverTags.Flush.timersStopObserved pid))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved (DriverTags.Flush.timersStopObserved pid); pure out.1)
      (Campaign2.inspect (timersStop pid)) :=
  ⟨DriverTags.inspection_facts _ (fun tags => DriverTags.Flush.timersStopObserved_preserves tags pid) entry,
    DriverTags.inspection_erases _ _ (DriverTags.Flush.timersStopObserved_erases pid)⟩

/-- Complete device stop preserves its saved peer order, inline worker drains,
clearing and final queue/socket checks. Its actual journal covers every
surviving normal final tag and contains only valid helper/birth receipts. -/
theorem original_device_stop_driver_tags (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved DriverTags.Control.stopObserved)
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved DriverTags.Control.stopObserved; pure out.1)
      (Campaign2.inspect wgStop) :=
  ⟨DriverTags.inspection_facts _ DriverTags.Control.stopObserved_preserves entry,
    DriverTags.inspection_erases _ _ DriverTags.Control.stopObserved_erases⟩

/-- Device down clears running before the complete original stop. Every
outcome agrees with the original call; normal final tags are accounted for by
the actual journal, with all callback obligations discharged. -/
theorem original_device_down_driver_tags (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved DriverTags.Control.downObserved)
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved DriverTags.Control.downObserved; pure out.1)
      (Campaign2.inspect wgDown) :=
  ⟨DriverTags.inspection_facts _ DriverTags.Control.downObserved_preserves entry,
    DriverTags.inspection_erases _ _ DriverTags.Control.downObserved_erases⟩

/-- Actual peer removal exposes nested timer and queue drains. Normal surviving tags trace to entry tags or actual receipts; emitted receipts remain valid on Stop. -/
theorem original_peer_removal_driver_tags (peer : Option PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved (DriverTags.Removal.removeObserved peer))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved (DriverTags.Removal.removeObserved peer); pure out.1)
      (Campaign2.inspect (peerRemove peer)) :=
  ⟨DriverTags.inspection_facts _ (fun tags => DriverTags.Removal.removeObserved_preserves tags peer) entry,
    DriverTags.inspection_erases _ _ (DriverTags.Removal.removeObserved_erases peer)⟩

/-- Bulk removal follows its saved peer list and every original after-dead drain. Original errors are preserved, including unfinished callback failures. -/
theorem original_all_peer_removal_driver_tags  (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved (DriverTags.Removal.removeAllObserved))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved (DriverTags.Removal.removeAllObserved); pure out.1)
      (Campaign2.inspect (peerRemoveAll)) :=
  ⟨DriverTags.inspection_facts _ (DriverTags.Removal.removeAllObserved_preserves) entry,
    DriverTags.inspection_erases _ _ (DriverTags.Removal.removeAllObserved_erases)⟩

/-- Device destruction keeps actual removal receipts before deleting the device. Final absence alone is not used to hide nested helper executions. -/
theorem original_device_destruction_driver_tags  (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved (DriverTags.Removal.destructObserved))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved (DriverTags.Removal.destructObserved); pure out.1)
      (Campaign2.inspect (wgDestruct)) :=
  ⟨DriverTags.inspection_facts _ (DriverTags.Removal.destructObserved_preserves) entry,
    DriverTags.inspection_erases _ _ (DriverTags.Removal.destructObserved_erases)⟩

/-- Actual peer configuration records births and receipt-bearing removals while retaining tag-silent field updates. No attribute-shape or readiness premise. -/
theorem original_peer_configuration_driver_tags (attrs : PeerAttrs) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved (DriverTags.Configuration.observePeer attrs))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved (DriverTags.Configuration.observePeer attrs); pure out.1)
      (Campaign2.inspect (setPeerCmd attrs)) :=
  ⟨DriverTags.inspection_facts _ (fun tags => DriverTags.Configuration.observePeer_preserves tags attrs) entry,
    DriverTags.inspection_erases _ _ (DriverTags.Configuration.observePeer_erases attrs)⟩

/-- Mixed device configuration exposes private-key expiry, births, and both removal paths. Inspection retains every original outcome. -/
theorem original_device_configuration_driver_tags (attrs : DeviceAttrs) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved (DriverTags.Configuration.observeDevice attrs))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved (DriverTags.Configuration.observeDevice attrs); pure out.1)
      (Campaign2.inspect (wgSetDevice attrs)) :=
  ⟨DriverTags.inspection_facts _ (fun tags => DriverTags.Configuration.observeDevice_preserves tags attrs) entry,
    DriverTags.inspection_erases _ _ (DriverTags.Configuration.observeDevice_erases attrs)⟩

/-- Actual data completion preserves surviving handshake tags through endpoint updates, confirmation rotation, counters, timers and staged sends. It emits no tag-owner receipt. -/
theorem original_data_completion_driver_tags (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved (Leanux.Proofs.Logged.liftWGPrefix (consumeDataDone pid packet endpoint)))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved (Leanux.Proofs.Logged.liftWGPrefix (consumeDataDone pid packet endpoint)); pure out.1)
      (Campaign2.inspect (consumeDataDone pid packet endpoint)) :=
  ⟨DriverTags.inspection_facts _ (fun tags => DriverTags.Silent.consumeDataDone_preserves tags pid packet endpoint) entry,
    DriverTags.inspection_erases _ _ (Leanux.Proofs.Logged.erasesStatePrefix_lift _)⟩

/-- Actual inner transmit preserves surviving handshake tags through lookup, queue handling and release. Normal errno outcomes and original Stops remain. -/
theorem original_transmit_driver_tags (family addr : Nat) (packets : List Packet) (mtu : Nat) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (DriverTags.inspectObserved (Leanux.Proofs.Logged.liftWGPrefix (wgXmit family addr packets mtu)))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectObserved (Leanux.Proofs.Logged.liftWGPrefix (wgXmit family addr packets mtu)); pure out.1)
      (Campaign2.inspect (wgXmit family addr packets mtu)) :=
  ⟨DriverTags.inspection_facts _ (fun tags => DriverTags.Silent.lift_preserves tags _ (fun initial => DriverTags.Transmit.native initial family addr packets mtu)) entry,
    DriverTags.inspection_erases _ _ (Leanux.Proofs.Logged.erasesStatePrefix_lift _)⟩

/-- All seven original dump calls preserve surviving tags. Existing cursor/serializer behavior and every original outcome are retained. -/
theorem original_dump_driver_tags (call : Leanux.Proofs.WG.Lifetimes.NetlinkDumpCall) (entry : Campaign2.Snapshot) :
    DriverTags.ProductEnsures (DriverTags.inspectProduct (DriverTags.Dump.observed call))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    DriverTags.ProductAgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectProduct (DriverTags.Dump.observed call); pure out.1)
      (DriverTags.inspectOriginalProduct (Leanux.liftWG call.original)) :=
  ⟨DriverTags.product_inspection_facts _ (fun tags => DriverTags.Dump.observed_preserves tags call) entry,
    DriverTags.product_inspection_erases _ _ (DriverTags.Dump.observed_erases call)⟩

/-- The actual complete scheduler uses concrete worker and NAPI callbacks. Normal surviving tags trace to the entry state or actual receipts; copied consistency probes add no committed receipt. -/
theorem original_scheduler_driver_tags (stack : Option Worker) (entry : Campaign2.Snapshot) :
    DriverTags.ProductEnsures (DriverTags.inspectProduct (DriverTags.Scheduled.schedule stack))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    DriverTags.ProductAgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectProduct (DriverTags.Scheduled.schedule stack); pure out.1)
      (DriverTags.inspectOriginalProduct (Leanux.Env.schedule stack)) :=
  ⟨DriverTags.product_inspection_facts _ (fun tags => DriverTags.Scheduled.schedule_preserves tags stack) entry,
    DriverTags.product_inspection_erases _ _ (DriverTags.Scheduled.schedule_erases stack)⟩

/-- The deferred-call family instantiates the complete concrete scheduler, send/clear observers and timer traversal. No callback or successful-completion premise remains. -/
theorem original_deferred_driver_tags (call : Leanux.Proofs.WG.Lifetimes.EnvDeferredCall) (entry : Campaign2.Snapshot) :
    DriverTags.ProductEnsures (DriverTags.inspectProduct (DriverTags.Scheduled.deferred call))
      (fun s => s = entry) (fun out final => final = entry ∧ DriverTags.InspectionFacts entry out) ∧
    DriverTags.ProductAgreesOn (fun _ => True)
      (do let out ← DriverTags.inspectProduct (DriverTags.Scheduled.deferred call); pure out.1)
      (DriverTags.inspectOriginalProduct (call.original)) :=
  ⟨DriverTags.product_inspection_facts _ (fun tags => DriverTags.Scheduled.deferred_preserves tags call) entry,
    DriverTags.product_inspection_erases _ _ (DriverTags.Scheduled.deferred_erases call)⟩

end Leanux.Proofs.WG.Noise
