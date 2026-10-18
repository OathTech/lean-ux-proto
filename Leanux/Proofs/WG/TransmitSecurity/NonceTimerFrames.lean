import Leanux.Proofs.WG.TransmitSecurity.NonceHandshakeFrames

/-! Timer operations outside keepalive staging retain the nonce journal. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem timer_delete (pid : PeerId) (timer : PeerTimer) : SameView view (delTimer pid timer) :=
  full (Origins.Retaining.delTimer_material pid timer) (Keypairs.WGFrames.delTimer_sameSnapshot pid timer)

theorem timer_arm (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView view (modPeerTimer site pid timer delay) :=
  full (Origins.Retaining.modPeerTimer_material site pid timer delay)
    (Keypairs.WGTransitions.modPeerTimer_sameSnapshot site pid timer delay)

theorem endpoint_clear (pid : PeerId) : SameView view (clearPeerEndpointSrc pid) :=
  full (Origins.Retaining.clearPeerEndpointSrc_material pid) (Keypairs.WGFrames.clearPeerEndpointSrc_sameSnapshot pid)

theorem purge (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  repeat' nonce_preserves_step h

macro "nonce_timer_step " h:term : tactic => `(tactic| first
  | (rx_retention_head delTimer; exact native_frame $h (timer_delete _ _))
  | (rx_retention_head modPeerTimer; exact native_frame $h (timer_arm _ _ _ _))
  | (rx_retention_head clearPeerEndpointSrc; exact native_frame $h (endpoint_clear _))
  | (rx_retention_head purgeStagedPackets; exact purge _ $h)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact native_frame $h (queuedHandshake _ _))
  | nonce_preserves_step $h)

theorem expired_retransmit (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (expiredRetransmitHandshake pid) := by
  unfold expiredRetransmitHandshake
  simp (config := {zeta := false}) only [branch,branchCmp,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' nonce_timer_step h

theorem expired_new (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (expiredNewHandshake pid) :=
  preserves_bind (native_frame h (endpoint_clear pid)) (fun _ => native_frame h (queuedHandshake pid false))

theorem expired_zero (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' nonce_timer_step h

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
