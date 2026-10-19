import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialScheduler
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverDeferredFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimerFrames

/-! Native delayed-work frames for TX allocation material. Clearing may
delete keys; it cannot substitute a new core for a surviving packet reference. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder Origins.Retaining RetirementSecurity
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (Inv h) (modPeerTimer site pid timer delay) :=
  frame (PacketOrigins.snapshot_wire (modPeerTimer_cryptWire site pid timer delay))
    (core_of_same (pool_of_material (modPeerTimer_material site pid timer delay)))
    (fun _ => lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry) site pid timer delay))

theorem queued (pid : PeerId) (retry : Bool) : Preserves (Inv h) (sendQueuedHandshakeInitiation pid retry) :=
  frame (PacketOrigins.snapshot_wire (sendQueued_cryptWire pid retry))
    (core_of_same (queued_core pid retry)) (fun _ => lower_queued pid retry)

theorem clear_endpoint (pid : PeerId) : Preserves (Inv h) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  simp only [getAmbient,hiddenJiffies]
  repeat' resident_handshake_leaf

theorem purge (pid : PeerId) : Preserves (Inv h) (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  repeat' resident_staging_step

macro "resident_timer_frame" : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head purgeStagedPackets; exact purge _)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _)
  | (rx_retention_head modPeerTimer; exact modify_timer _ _ _ _)
  | (rx_retention_head delTimer; exact del _ _)
  | resident_handshake_frame)

theorem retransmit (pid : PeerId) : Preserves (Inv h) (expiredRetransmitHandshake pid) := by
  unfold expiredRetransmitHandshake
  simp (config := {zeta := false}) only [branch,branchCmp,Functor.discard,map_const,
    Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' resident_timer_frame

theorem new_handshake (pid : PeerId) : Preserves (Inv h) (expiredNewHandshake pid) :=
  preserves_bind (clear_endpoint pid) (fun _ => queued pid false)

theorem expired_zero (pid : PeerId) : Preserves (Inv h) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' resident_timer_frame

theorem create_initiation (pid : PeerId) : Preserves (Inv h) (createInitiation pid) := by
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' resident_handshake_leaf

theorem initiated (pid : PeerId) : Preserves (Inv h) (timersHandshakeInitiated pid) :=
  frame (PacketOrigins.snapshot_wire (OccurrenceHandshake.initiated_wire pid))
    (core_of_same (pool_of_material (timersHandshakeInitiated_material pid)))
    (fun _ => lower_owner_geometry (PublicationGeometry.timersHandshakeInitiated_geometry pid))

theorem send_initiation (pid : PeerId) : Preserves (Inv h) (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createInitiation; exact create_initiation _)
    | (rx_retention_head timersHandshakeInitiated; exact initiated _)
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Inv _))
    | resident_handshake_frame

theorem send_worker (pid : PeerId) : Preserves (Inv h) (handshakeSendWorker pid) :=
  preserves_bind (send_initiation pid) (fun _ => peer_put (some pid))

theorem handshake_clear (pid : PeerId) : Preserves (Inv h) (handshakeClear pid) := by
  unfold handshakeClear handshakeZero
  repeat' resident_handshake_leaf

theorem keys_clear (pid : PeerId) : Preserves (Inv h) (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' resident_handshake_leaf

theorem clear_worker (pid : PeerId) : Preserves (Inv h) (queuedExpiredZeroKeyMaterial pid) :=
  preserves_bind (handshake_clear pid) (fun _ =>
    preserves_bind (keys_clear pid) (fun _ => peer_put (some pid)))

theorem flushed_send (pid : PeerId) : Preserves (Inv h) (runFlushedSendWork pid) := by
  unfold runFlushedSendWork
  simp only [hidden,invariant]
  repeat' first
    | (rx_retention_head handshakeSendWorker; exact send_worker _)
    | resident_handshake_frame

theorem flushed_clear (pid : PeerId) : Preserves (Inv h) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact clear_worker _)
    | resident_handshake_frame

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

theorem bounds_clear_worker (pid : PeerId) : Preserves Bounds (queuedExpiredZeroKeyMaterial pid) :=
  bounds_join (ConfiguredRemoval.queuedClear pid)
    (preserves_bind (CurrentSlots.handshakeClear_preserves pid) (fun _ =>
      preserves_bind (CurrentSlots.keypairsClear_preserves pid) (fun _ => CurrentSlots.peerPut_preserves (some pid))))

theorem bounds_flushed_clear (pid : PeerId) : Preserves Bounds (runFlushedClearWork pid) := by
  apply bounds_join (ConfiguredRemoval.flushedClear pid)
  unfold runFlushedClearWork
  simp only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial
       exact preserves_bind (CurrentSlots.handshakeClear_preserves pid) (fun _ =>
         preserves_bind (CurrentSlots.keypairsClear_preserves pid) (fun _ => CurrentSlots.peerPut_preserves (some pid))))
    | slot_traffic_step

theorem send_one_preserves {P : WGWorld → Prop} (read : Preserves P getDev)
    (flushed : ∀ pid, Preserves P (runFlushedSendWork pid)) :
    Preserves (fun w : World => P w.wg) Env.runOneSendWorker := by
  unfold Env.runOneSendWorker
  apply preserves_bind (PublicationPoll.native_product _ _ read)
  intro d
  cases d.sendWorkQueue.head? with
  | none => exact productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi)
  | some head =>
    dsimp only
    apply preserves_bind (productAmbient_spec (AmbientM.peekUnit .sendWorker) _ (fun _ _ hi => hi))
    intro unit
    cases unit <;> dsimp only
    all_goals apply preserves_bind
    · exact preserves_pure _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushed pid)
    · exact productAmbient_spec (AmbientM.resolveUnit _ _ _) _ (fun _ _ hi => hi)
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushed pid)

theorem clear_one_preserves {P : WGWorld → Prop} (read : Preserves P getDev)
    (flushed : ∀ pid, Preserves P (runFlushedClearWork pid)) :
    Preserves (fun w : World => P w.wg) Env.runOneClearWorker := by
  unfold Env.runOneClearWorker
  apply preserves_bind (PublicationPoll.native_product _ _ read)
  intro d
  cases d.clearWorkQueue.head? with
  | none => exact productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi)
  | some head =>
    dsimp only
    apply preserves_bind (productAmbient_spec (AmbientM.peekUnit .clearPeerWorker) _ (fun _ _ hi => hi))
    intro unit
    cases unit <;> dsimp only
    all_goals apply preserves_bind
    · exact preserves_pure _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushed pid)
    · exact productAmbient_spec (AmbientM.resolveUnit _ _ _) _ (fun _ _ hi => hi)
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushed pid)

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
