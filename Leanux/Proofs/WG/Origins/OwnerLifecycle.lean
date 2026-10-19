import Leanux.Proofs.WG.Origins.OwnerControls

/-! Receiving-owner bounds through native flushed work and removal-time timer stops.
Normal errno returns retain their effects; every recorded guard and Stop is
the original source operation. -/
namespace Leanux.Proofs.WG.OwnerLifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Queues.RxCredits OwnerBounds OwnerControls

private theorem edit_preserves (f : WGWorld → WGWorld) (same : ∀ w, (f w).dev = w.dev) :
    Preserves Carrier (modify f : WG.M Unit) := by
  apply hoare_modify
  intro w hi
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
    hi (same w)

macro "owner_lifecycle_step" : tactic => `(tactic| first
  | (allocation_release_lift_from Net.M; exact OwnerControls.store _ (liftRouting_sameWGStore _))
  | (allocation_release_head liftRouting; exact OwnerControls.store _ (liftRouting_sameWGStore _))
  | (allocation_release_head getRouting
     exact OwnerControls.store _ (liftRouting_sameWGStore
       ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))))
  | (allocation_release_head modify; exact edit_preserves _ (fun _ => rfl))
  | owner_control_step)

macro "owner_crypto" : tactic => `(tactic| first
  | (allocation_release_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp Carrier)
  | (allocation_release_head generatePublic; exact (generatePublic_sameWGWorld _).wp Carrier)
  | (allocation_release_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp Carrier)
  | (allocation_release_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp Carrier)
  | (allocation_release_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp Carrier)
  | owner_lifecycle_step)

private theorem createInitiation_preserves (pid : PeerId) : Preserves Carrier (createInitiation pid) := by
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' owner_crypto

private theorem addMacToPacket_preserves (pid : PeerId) (msg : List UInt8) :
    Preserves Carrier (addMacToPacket pid msg) := by
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' owner_crypto

private theorem dstCacheGet_preserves (pid : PeerId) (gen : Nat) :
    Preserves Carrier (dstCacheGet pid gen) := by
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' owner_lifecycle_step

private theorem dstCacheSet_preserves (pid : PeerId) (src gen dev : Nat) :
    Preserves Carrier (dstCacheSet pid src gen dev) := by
  unfold dstCacheSet
  repeat' owner_lifecycle_step

theorem delTimer_preserves (pid : PeerId) (timer : PeerTimer) :
    Preserves Carrier (delTimer pid timer) := by
  unfold delTimer
  repeat' owner_lifecycle_step

private theorem armTimer_preserves (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64) : Preserves Carrier (armTimer pid timer delay jc) :=
  OwnerCompletion.preserves_of_frames _
    (Origins.Retaining.of_view (Origins.Retaining.armTimer_material pid timer delay jc))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.arm_geometry) pid timer delay jc)
    (control_keyEffects (allowed := NoPromotion) (armTimer_control pid timer delay jc))

theorem modPeerTimer_preserves (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) : Preserves Carrier (modPeerTimer site pid timer delay) :=
  OwnerCompletion.preserves_of_frames _
    (Origins.Retaining.of_view (Origins.Retaining.modPeerTimer_material site pid timer delay))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry) site pid timer delay)
    (control_keyEffects (allowed := NoPromotion) (modPeerTimer_control site pid timer delay))

private theorem traversal_preserves (pid : PeerId) : Preserves Carrier (timersTraversal pid) :=
  OwnerCompletion.preserves_of_frames _
    (Origins.Retaining.of_view (Origins.Retaining.timersTraversal_material pid))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.traversal_geometry) pid)
    (control_keyEffects (allowed := NoPromotion) (timersTraversal_control pid))

private theorem sent_preserves (pid : PeerId) : Preserves Carrier (timersAnyAuthenticatedPacketSent pid) := by
  unfold timersAnyAuthenticatedPacketSent
  repeat' first
    | (allocation_release_head delTimer; exact delTimer_preserves _ _)
    | owner_lifecycle_step

private theorem initiated_preserves (pid : PeerId) : Preserves Carrier (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp Carrier)
    | (allocation_release_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp Carrier)
    | (allocation_release_head armTimer; exact armTimer_preserves _ _ _ _)
    | owner_lifecycle_step

private theorem dstCacheReset_preserves (pid : PeerId) : Preserves Carrier (dstCacheReset pid) := by
  unfold dstCacheReset
  simp (config := {zeta := false}) only [hiddenJiffies,getAmbient]
  repeat' owner_lifecycle_step

theorem tunnelXmit_preserves (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    Preserves Carrier ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact OwnerControls.store _ (loopbackSend_kernel _ _))
    | (rx_retention_head socketPort
       exact OwnerControls.store _ (socketPort_sameStore _))
    | owner_lifecycle_step

private theorem send4ClearSrc_preserves cache : Preserves Carrier (send4ClearSrcSource cache) := by
  unfold send4ClearSrcSource
  repeat' first
    | owner_lifecycle_step

private theorem send4Finish_preserves e bytes ds exactRx route : Preserves Carrier (send4FinishSource e bytes ds exactRx route) := by
  unfold send4FinishSource
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact tunnelXmit_preserves _ _ _ _ _)
    | owner_lifecycle_step

private theorem send4RouteDone_preserves e cache bytes ds exactRx gen fallback rt :
    Preserves Carrier (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  unfold send4RouteDoneSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact dstCacheSet_preserves _ _ _ _)
    | (rx_retention_head send4FinishSource; exact send4Finish_preserves _ _ _ _ _)
    | owner_lifecycle_step

private theorem send4Retry_preserves e cache bytes ds exactRx gen fallback srcIf rt :
    Preserves Carrier (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  unfold send4RetrySource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact send4ClearSrc_preserves _)
    | (rx_retention_head dstCacheReset; exact dstCacheReset_preserves _)
    | (rx_retention_head send4RouteDoneSource; exact send4RouteDone_preserves _ _ _ _ _ _ _ _)
    | owner_lifecycle_step

private theorem send4Miss_preserves e cache bytes ds exactRx gen fallback saddr srcIf :
    Preserves Carrier (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  unfold send4MissSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact send4ClearSrc_preserves _)
    | (rx_retention_head dstCacheReset; exact dstCacheReset_preserves _)
    | (rx_retention_head send4RetrySource; exact send4Retry_preserves _ _ _ _ _ _ _ _ _)
    | owner_lifecycle_step

private theorem send4AfterCache_preserves e cache bytes ds exactRx gen saddr srcIf route :
    Preserves Carrier (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  unfold send4AfterCacheSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact send4Miss_preserves _ _ _ _ _ _ _ _ _)
    | (rx_retention_head send4FinishSource; exact send4Finish_preserves _ _ _ _ _)
    | owner_lifecycle_step

theorem send4_preserves e cache bytes ds exactRx : Preserves Carrier (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  unfold send4Source
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact dstCacheGet_preserves _ _)
    | (rx_retention_head send4AfterCacheSource; exact send4AfterCache_preserves _ _ _ _ _ _ _ _ _)
    | owner_lifecycle_step

theorem send6_preserves (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Preserves Carrier (send6 e cache bytes ds exactRx) := by
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact dstCacheGet_preserves _ _)
    | (rx_retention_head dstCacheReset; exact dstCacheReset_preserves _)
    | (rx_retention_head dstCacheSet; exact dstCacheSet_preserves _ _ _ _)
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact tunnelXmit_preserves _ _ _ _ _)
    | owner_lifecycle_step

theorem sendBufferToPeer_preserves (pid : PeerId) (bytes : List UInt8) : Preserves Carrier (sendBufferToPeer pid bytes) := by
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head send4; exact send4_preserves _ _ _ _ _)
    | (rx_retention_head send6; exact send6_preserves _ _ _ _ _)
    | owner_lifecycle_step

theorem sendHandshakeInitiation_preserves (pid : PeerId) : Preserves Carrier (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (allocation_release_head createInitiation; exact createInitiation_preserves _)
    | (allocation_release_head addMacToPacket; exact addMacToPacket_preserves _ _)
    | (allocation_release_head timersTraversal; exact traversal_preserves _)
    | (allocation_release_head timersAnyAuthenticatedPacketSent; exact sent_preserves _)
    | (allocation_release_head timersHandshakeInitiated; exact initiated_preserves _)
    | (allocation_release_head sendBufferToPeer; exact sendBufferToPeer_preserves _ _)
    | owner_crypto

theorem handshakeSendWorker_preserves (pid : PeerId) : Preserves Carrier (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact preserves_bind (sendHandshakeInitiation_preserves pid)
    (fun _ => OwnerConsume.peerPut_preserves (some pid))

theorem runFlushedSendWork_preserves (pid : PeerId) : Preserves Carrier (runFlushedSendWork pid) := by
  unfold runFlushedSendWork
  simp (config := {zeta := false}) only [hidden,invariant]
  repeat' first
    | (allocation_release_head handshakeSendWorker; exact handshakeSendWorker_preserves _)
    | owner_lifecycle_step

theorem runFlushedClearWork_preserves (pid : PeerId) : Preserves Carrier (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (allocation_release_head queuedExpiredZeroKeyMaterial; exact queuedExpiredZeroKeyMaterial_preserves _)
    | owner_lifecycle_step

theorem drainHandshakeSendWq_preserves (upTo : Option PeerId) :
    Preserves Carrier (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (allocation_release_head runFlushedSendWork; exact runFlushedSendWork_preserves _)
    | (allocation_release_head runFlushedClearWork; exact runFlushedClearWork_preserves _)
    | owner_lifecycle_step

theorem timersStop_preserves (pid : PeerId) : Preserves Carrier (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (allocation_release_head delTimer; exact delTimer_preserves _ _)
    | (allocation_release_head drainHandshakeSendWq; exact drainHandshakeSendWq_preserves _)
    | owner_lifecycle_step

end Leanux.Proofs.WG.OwnerLifecycle
