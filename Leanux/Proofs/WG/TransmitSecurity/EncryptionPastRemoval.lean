import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastRemovalFrames

/-! Full peer removal and device shutdown retain historical encryption exclusion
through their actual queued drains, clears, route teardown and final payments. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Removal
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition Keys Socket Maintenance
set_option maxHeartbeats 600000

theorem remove_allowedips (pid : PeerId) : Preserves (Ready past active) (removeByPeer pid) := by
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head listDel; exact list_delete _)
    | (allocation_release_head AllowedIps.removeNodeBody; exact node_remove _)
    | encryption_past_handshake_step

theorem make_dead (pid : PeerId) : Preserves (Ready past active) (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head removeByPeer; exact remove_allowedips _)
    | encryption_past_handshake_step

theorem remove_peer (peer : Option PeerId) : Preserves (Ready past active) (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head peerMakeDead; exact make_dead _)
    | (allocation_release_head peerRemoveAfterDead; exact remove_after_dead _)
    | encryption_past_handshake_step

theorem remove_all : Preserves (Ready past active) peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head WG.free; exact free_allowedips)
    | (allocation_release_head peerMakeDead; exact make_dead _)
    | (allocation_release_head peerRemoveAfterDead; exact remove_after_dead _)
    | encryption_past_handshake_step

theorem socket_reinit (new4 new6 : Option Nat) : Preserves (Ready past active) (socketReinit new4 new6) := by
  unfold socketReinit sockFree iputReport
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' encryption_past_handshake_step

theorem stop : Preserves (Ready past active) wgStop := by
  unfold wgStop requireNotPending resetLastSentHandshake
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (allocation_release_head purgeStagedPackets; exact ready_frame (LiveFrontier.purge_staged _) (purge_staged _))
    | (allocation_release_head timersStop; exact timers_stop _)
    | (allocation_release_head handshakeClear; exact handshake_clear _)
    | (allocation_release_head keypairsClear; exact keys_clear _)
    | (allocation_release_head socketReinit; exact socket_reinit _ _)
    | encryption_past_handshake_step

theorem down : Preserves (Ready past active) wgDown :=
  preserves_bind (ready_tx_fields _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) (fun _=>stop)

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Removal
