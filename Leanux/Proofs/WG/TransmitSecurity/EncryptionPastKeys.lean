import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastKeyFrames

/-! Original session construction and key maintenance retain the historical
encryption carrier, including native refusal and allocation branches. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Keys
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition
set_option maxHeartbeats 600000

theorem handshake_zero (pid : PeerId) : Preserves (Ready past active) (handshakeZero pid) := by
  unfold handshakeZero
  repeat' encryption_past_key_step

theorem handshake_clear (pid : PeerId) : Preserves (Ready past active) (handshakeClear pid) := by
  unfold handshakeClear
  repeat' first
    | (allocation_release_head handshakeZero; exact handshake_zero _)
    | encryption_past_key_step

theorem keys_clear (pid : PeerId) : Preserves (Ready past active) (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' encryption_past_key_step

theorem expire_keys (pid : PeerId) : Preserves (Ready past active) (expireCurrentPeerKeypairs pid) := by
  unfold expireCurrentPeerKeypairs resetLastSentHandshake requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head handshakeClear; exact handshake_clear _)
    | encryption_past_key_step

theorem queued_clear (pid : PeerId) : Preserves (Ready past active) (queuedExpiredZeroKeyMaterial pid) :=
  preserves_bind (handshake_clear pid) (fun _=>preserves_bind (keys_clear pid) (fun _ => ready_frame (LiveFrontier.peer_put (some pid)) (peer_put (some pid))))

theorem key_create (owner : Option PeerId) : Preserves (Ready past active) (keypairCreate owner) := by
  unfold keypairCreate
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' encryption_past_key_step

theorem key_add (pid : PeerId) (kid : KeypairId) : Preserves (Ready past active) (addNewKeypair pid kid) := by
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' encryption_past_key_step

theorem derive_keys (kid : KeypairId) (initiator : Bool) (chain : List UInt8) :
    Preserves (Ready past active) (deriveKeys kid initiator chain) := by
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' encryption_past_key_step

/-- Original session refusal, key creation/rotation and final index guard. -/
theorem begin_session (pid : PeerId) : Preserves (Ready past active) (beginSession pid) := by
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head keypairCreate; exact key_create _)
    | (allocation_release_head addNewKeypair; exact key_add _ _)
    | (allocation_release_head deriveKeys; exact derive_keys _ _ _)
    | (allocation_release_head handshakeZero; exact handshake_zero _)
    | encryption_past_key_step

theorem create_initiation (pid : PeerId) : Preserves (Ready past active) (createInitiation pid) := by
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' encryption_past_key_step

theorem create_response (pid : PeerId) : Preserves (Ready past active) (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' encryption_past_key_step

theorem add_mac (pid : PeerId) (msg : List UInt8) : Preserves (Ready past active) (addMacToPacket pid msg) := by
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' encryption_past_key_step

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Keys
