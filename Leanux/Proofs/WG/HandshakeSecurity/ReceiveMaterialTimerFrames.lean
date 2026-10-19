import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialScheduler
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverDeferredFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimerFrames

/-! Native timer and delayed-send frames preserve RX allocation certificates.
Clearing may delete keys; a surviving referenced core cannot be substituted. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.TimerFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder Origins.Retaining RetirementSecurity
open HandshakeFrames
open ResidentMaterial (core_of_same)
open ResidentMaterial.NativeFrames (lower_owner_geometry)
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (Bounded h) (modPeerTimer site pid timer delay) :=
  bounded_frame
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry) site pid timer delay).factor Prod.snd)
    (core_of_same (pool_of_material (modPeerTimer_material site pid timer delay)))
    (fun _ => lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry) site pid timer delay))

theorem queued (pid : PeerId) (retry : Bool) : Preserves (Bounded h) (sendQueuedHandshakeInitiation pid retry) :=
  bounded_frame (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.sendQueued_geometry) pid retry).factor Prod.snd)
    (core_of_same (queued_core pid retry)) (fun _ => ResidentMaterial.NativeFrames.lower_queued pid retry)

theorem clear_endpoint (pid : PeerId) : Preserves (Bounded h) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  simp only [getAmbient,hiddenJiffies]
  repeat' receive_handshake_leaf

theorem purge (pid : PeerId) : Preserves (Bounded h) (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  repeat' receive_bounded_native_step

macro "receive_timer_frame" : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head purgeStagedPackets; exact purge _)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _)
  | (rx_retention_head modPeerTimer; exact modify_timer _ _ _ _)
  | (rx_retention_head delTimer; exact del _ _)
  | (rx_retention_head peerGet; unfold peerGet requireNotPending refcountInc; simp only [invariant,unsupported,branch,branchCmp]; repeat' receive_handshake_leaf)
  | receive_handshake_frame)

theorem retransmit (pid : PeerId) : Preserves (Bounded h) (expiredRetransmitHandshake pid) := by
  unfold expiredRetransmitHandshake
  simp (config := {zeta := false}) only [branch,branchCmp,Functor.discard,map_const,
    Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' receive_timer_frame

theorem new_handshake (pid : PeerId) : Preserves (Bounded h) (expiredNewHandshake pid) :=
  preserves_bind (clear_endpoint pid) (fun _ => queued pid false)

theorem expired_zero (pid : PeerId) : Preserves (Bounded h) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' receive_timer_frame

theorem create_initiation (pid : PeerId) : Preserves (Bounded h) (createInitiation pid) := by
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' receive_handshake_leaf

theorem initiated (pid : PeerId) : Preserves (Bounded h) (timersHandshakeInitiated pid) :=
  bounded_frame ((PublicationGeometry.timersHandshakeInitiated_geometry pid).factor Prod.snd)
    (core_of_same (pool_of_material (timersHandshakeInitiated_material pid)))
    (fun _ => lower_owner_geometry (PublicationGeometry.timersHandshakeInitiated_geometry pid))

theorem send_initiation (pid : PeerId) : Preserves (Bounded h) (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createInitiation; exact create_initiation _)
    | (rx_retention_head timersHandshakeInitiated; exact initiated _)
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Bounded _))
    | receive_handshake_frame

theorem send_worker (pid : PeerId) : Preserves (Bounded h) (handshakeSendWorker pid) :=
  preserves_bind (send_initiation pid) (fun _ => bounded_peer_put (some pid))

theorem handshake_clear (pid : PeerId) : Preserves (Bounded h) (handshakeClear pid) := by
  unfold handshakeClear handshakeZero
  repeat' receive_handshake_leaf

theorem keys_clear (pid : PeerId) : Preserves (Bounded h) (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' receive_handshake_leaf

theorem clear_worker (pid : PeerId) : Preserves (Bounded h) (queuedExpiredZeroKeyMaterial pid) :=
  preserves_bind (handshake_clear pid) (fun _ =>
    preserves_bind (keys_clear pid) (fun _ => bounded_peer_put (some pid)))

theorem flushed_send (pid : PeerId) : Preserves (Bounded h) (runFlushedSendWork pid) := by
  unfold runFlushedSendWork
  simp only [hidden,invariant]
  repeat' first
    | (rx_retention_head handshakeSendWorker; exact send_worker _)
    | receive_handshake_frame

theorem flushed_clear (pid : PeerId) : Preserves (Bounded h) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact clear_worker _)
    | receive_handshake_frame

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.TimerFrames
