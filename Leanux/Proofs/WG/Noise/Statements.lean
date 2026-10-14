import Leanux.Proofs.WG.Noise.ConsumeEdges

/-! H1's checked local endpoints. Whole-run edge ownership and confirmation
uniqueness by allocation lifetime remain separate obligations. -/
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- On normal completion the original rotation implements every C arm:
initiator without next, initiator with next, and responder. -/
theorem original_slot_rotation (pid : PeerId) (newKey : KeypairId)
    (p : Peer) (k : Keypair) :
    Ensures (addNewKeypair pid newKey)
      (fun w => peerAt w pid = some p ∧
        (w.k.wg.bind fun d => d.keypairs[newKey]?) = some k)
      (fun _ w => ∃ p', peerAt w pid = some p' ∧
        slots p' = rotate (slots p) k.iAmTheInitiator newKey) :=
  addNewKeypair_slots pid newKey p k

/-- The original confirmation returns true exactly for the pending next
key, then moves current to previous and next to current and clears next. -/
theorem original_confirmation (pid : PeerId) (received : KeypairId) (p : Peer) :
    Ensures (receivedWithKeypair pid received) (fun w => peerAt w pid = some p)
      (fun ok w => ∃ p', peerAt w pid = some p' ∧
        (ok, slots p') = confirm (slots p) received) :=
  receivedWithKeypair_slots pid received p

/-- Two adjacent normal confirmation calls for the same key cannot both
succeed. This local result does not assert lifetime uniqueness across intervening rotations. -/
theorem original_confirmation_no_repeat (pid : PeerId) (received : KeypairId)
    (p : Peer) (w v z : World) (second : Bool)
    (hp : peerAt w pid = some p)
    (hfirst : (receivedWithKeypair pid received).run w = .ok (true, v))
    (hsecond : (receivedWithKeypair pid received).run v = .ok (second, z)) :
    second = false := by
  obtain ⟨p', hp', hs⟩ := receivedWithKeypair_slots pid received p w true v hp hfirst
  have hn : (slots p').next = none := by
    unfold confirm at hs
    split at hs <;> simp_all [Prod.mk.injEq]
  obtain ⟨p'', _, hs'⟩ := receivedWithKeypair_slots pid received p' v second z hp' hsecond
  simpa [confirm, hn] using congrArg Prod.fst hs'

/-- Normal keypair clearing empties all three slots and preserves every
other field of the resident peer. Puts occur next, previous, current. -/
theorem original_clear_slots (pid : PeerId) (p : Peer) :
    Ensures (keypairsClear pid) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some { p with
        keypairNext := none, keypairPrevious := none, keypairCurrent := none }) :=
  keypairsClear_peer pid p

/-- Original handshake zeroing clears exactly the ephemeral material,
hash, chaining key, remote index and state tag, preserving other peer fields. -/
theorem original_handshake_zero (pid : PeerId) (p : Peer) :
    Ensures (handshakeZero pid) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some { p with
        ephemeralPrivate := List.replicate 32 0, remoteEphemeral := List.replicate 32 0,
        hash := List.replicate 32 0, chainingKey := List.replicate 32 0,
        remoteIndex := 0, handshakeState := 0 }) :=
  handshakeZero_peer pid p

/-- Successful initiation creation sets its owned state tag from any old
state; a normal failure preserves the old tag, not necessarily key material. -/
theorem original_create_initiation_edge (pid : PeerId) (old : Nat) :
    Ensures (createInitiation pid) (fun w => tagAt w.k pid = some old)
      (fun result w => tagAt w.k pid = some
        (if result.isSome then HANDSHAKE_CREATED_INITIATION else old)) :=
  createInitiation_tag pid old

/-- Response creation succeeds only from consumed initiation and sets
created response; every normal failure preserves the old tag. -/
theorem original_create_response_edge (pid : PeerId) (old : Nat) :
    Ensures (createResponse pid) (fun w => tagAt w.k pid = some old)
      (fun result w => tagAt w.k pid = some
        (if result.isSome then HANDSHAKE_CREATED_RESPONSE else old) ∧
        (result.isSome → old = HANDSHAKE_CONSUMED_INITIATION)) :=
  createResponse_tag pid old

/-- Normal expiry preserves the peer's three published key slots and
zeroes its handshake tag. Slot clearing is a different operation. -/
theorem original_expiry_slots (pid : PeerId) (p : Peer) :
    Ensures (expireCurrentPeerKeypairs pid) (fun w => peerAt w pid = some p)
      (fun _ w => ∃ p', peerAt w pid = some p' ∧
        slots p' = slots p ∧ p'.handshakeState = 0) :=
  expireCurrentPeerKeypairs_slots pid p

/-- Normal session completion is possible only from created response or
consumed response and zeroes the handshake. A false return preserves its tag. -/
theorem original_begin_session_edge (pid : PeerId) (old : Nat) :
    Ensures (beginSession pid) (fun w => tagAt w.k pid = some old)
      (fun ok w => tagAt w.k pid = some (if ok then HANDSHAKE_ZEROED else old) ∧
        (ok = true → old = HANDSHAKE_CREATED_RESPONSE ∨ old = HANDSHAKE_CONSUMED_RESPONSE)) :=
  beginSession_tag pid old

/-- A successful initiation consumer returns a resident peer with the
consumed-initiation tag. This endpoint statement does not classify failed prefixes. -/
theorem original_consume_initiation_tag (msg : List UInt8) :
    Ensures (consumeInitiation msg) (fun _ => True)
      (fun result w => ∀ pid, result = some pid →
        tagAt w.k pid = some HANDSHAKE_CONSUMED_INITIATION) :=
  consumeInitiation_tag msg

/-- A successful response consumer returns a resident peer with the
consumed-response tag. Authentication provenance is a separate obligation. -/
theorem original_consume_response_tag (msg : List UInt8) :
    Ensures (consumeResponse msg) (fun _ => True)
      (fun result w => ∀ pid, result = some pid →
        tagAt w.k pid = some HANDSHAKE_CONSUMED_RESPONSE) :=
  consumeResponse_tag msg

end Leanux.Proofs.WG.Noise
