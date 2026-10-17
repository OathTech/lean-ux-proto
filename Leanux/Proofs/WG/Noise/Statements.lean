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

end Leanux.Proofs.WG.Noise
