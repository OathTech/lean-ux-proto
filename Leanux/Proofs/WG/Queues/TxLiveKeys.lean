import Leanux.Proofs.WG.Queues.TxLiveTimers

/-! Key/session maintenance changes key allocation and resident contents,
while leaving the actual TX frontier and ring untouched. No owner, key-slot,
reference-credit or totality premise is needed for this narrower property. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

/-- Only the two fields used by Ready are required here; key allocation may
advance its separate counter and key frontier. -/
theorem modify_live (f : Device→Device) (frontier : ∀d,(f d).nextSkb=d.nextSkb)
    (ring : ∀d,(f d).encryptQueue=d.encryptQueue) : Preserves Ready (modifyDev f) := by
  apply hoare_modify
  intro w hi
  constructor
  · intro e device
    cases hd:w.dev with
    | none=>simp [hd] at device
    | some d=>
      have same : e=f d := by simpa only [modifyDev,hd,Option.map_some,Option.some.injEq] using device.symm
      subst e
      simpa only [frontier,ring] using hi.1 d hd
  · intro e device
    cases hd:w.dev with
    | none=>simp [hd] at device
    | some d=>
      have same : e=f d := by simpa only [modifyDev,hd,Option.map_some,Option.some.injEq] using device.symm
      subst e
      simpa only [ring] using hi.2 d hd

macro "live_key_step" : tactic => `(tactic| first
  | (allocation_release_head hiddenClock64; unfold hiddenClock64)
  | (allocation_release_head modifyDev; exact modify_live _ (fun _=>rfl) (fun _=>rfl))
  | (allocation_release_head keypairPut; exact key_put _ _)
  | (allocation_release_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
  | (allocation_release_head generatePublic; exact (generatePublic_sameWGWorld _).wp Ready)
  | (allocation_release_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp Ready)
  | (allocation_release_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp Ready)
  | (allocation_release_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp Ready)
  | (allocation_release_head messageDecrypt; exact (messageDecrypt_sameWGWorld _ _ _).wp Ready)
  | (allocation_release_head kdf; exact (Framing.kdf_sameWGWorld _ _ _ _).wp Ready)
  | (allocation_release_head kdfOut; exact (Framing.kdfOut_sameWGWorld _ _).wp Ready)
  | live_timer_step)

theorem handshake_zero (pid : PeerId) : Preserves Ready (handshakeZero pid) := by
  unfold handshakeZero
  repeat' live_key_step

theorem handshake_clear (pid : PeerId) : Preserves Ready (handshakeClear pid) := by
  unfold handshakeClear
  repeat' first
    | (allocation_release_head handshakeZero; exact handshake_zero _)
    | live_key_step

theorem keys_clear (pid : PeerId) : Preserves Ready (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' live_key_step

theorem expire_keys (pid : PeerId) : Preserves Ready (expireCurrentPeerKeypairs pid) := by
  unfold expireCurrentPeerKeypairs resetLastSentHandshake requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head handshakeClear; exact handshake_clear _)
    | live_key_step

theorem queued_clear (pid : PeerId) : Preserves Ready (queuedExpiredZeroKeyMaterial pid) :=
  preserves_bind (handshake_clear pid) (fun _=>preserves_bind (keys_clear pid) (fun _=>peer_put (some pid)))

theorem key_create (owner : Option PeerId) : Preserves Ready (keypairCreate owner) := by
  unfold keypairCreate
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' live_key_step

theorem key_add (pid : PeerId) (kid : KeypairId) : Preserves Ready (addNewKeypair pid kid) := by
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' live_key_step

theorem derive_keys (kid : KeypairId) (initiator : Bool) (chain : List UInt8) :
    Preserves Ready (deriveKeys kid initiator chain) := by
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' live_key_step

/-- Original session refusal, key creation/rotation and final index guard. -/
theorem begin_session (pid : PeerId) : Preserves Ready (beginSession pid) := by
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head keypairCreate; exact key_create _)
    | (allocation_release_head addNewKeypair; exact key_add _ _)
    | (allocation_release_head deriveKeys; exact derive_keys _ _ _)
    | (allocation_release_head handshakeZero; exact handshake_zero _)
    | live_key_step

theorem create_initiation (pid : PeerId) : Preserves Ready (createInitiation pid) := by
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' live_key_step

theorem create_response (pid : PeerId) : Preserves Ready (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' live_key_step

theorem add_mac (pid : PeerId) (msg : List UInt8) : Preserves Ready (addMacToPacket pid msg) := by
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' live_key_step

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
