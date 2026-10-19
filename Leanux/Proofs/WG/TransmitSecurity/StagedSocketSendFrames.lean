import Leanux.Proofs.WG.TransmitSecurity.StagedSocketFrames

/-! Both native socket paths preserve staged queues through cache updates,
routing failures and actual datagram append. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Exact
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

macro "staged_send_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getRouting; unfold getRouting; exact (store (liftRouting_sameWGStore _)) $initial)
  | (rx_retention_head liftRouting; exact (store (liftRouting_sameWGStore _)) $initial)
  | (allocation_release_lift_from Net.M; exact (store (liftRouting_sameWGStore _)) $initial)
  | (rx_retention_head modifyDev; apply modify_preserves; intro d; rfl)
  | staged_socket_step $initial)

theorem tunnelXmit_staged (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView stagedAt ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact (store (Queues.loopbackSend_kernel _ _)).wp (fun s => s = initial))
    | (rx_retention_head socketPort
       exact (store (socketPort_sameStore _)).wp (fun s => s = initial))
    | staged_send_step initial

theorem send4ClearSrc_staged cache : SameView stagedAt (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  change Preserves (fun w => stagedAt w = initial) _
  repeat' first
    | staged_send_step initial

theorem send4Finish_staged e bytes ds exactRx route : SameView stagedAt (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  change Preserves (fun w => stagedAt w = initial) _
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact (tunnelXmit_staged _ _ _ _ _).wp (fun t => t = initial))
    | staged_send_step initial

theorem send4RouteDone_staged e cache bytes ds exactRx gen fallback rt :
    SameView stagedAt (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  change Preserves (fun w => stagedAt w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact (cache_set _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_staged _ _ _ _ _).wp (fun t => t = initial))
    | staged_send_step initial

theorem send4Retry_staged e cache bytes ds exactRx gen fallback srcIf rt :
    SameView stagedAt (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  change Preserves (fun w => stagedAt w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_staged _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (cache_reset _).wp (fun t => t = initial))
    | (rx_retention_head send4RouteDoneSource; exact (send4RouteDone_staged _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | staged_send_step initial

theorem send4Miss_staged e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView stagedAt (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  change Preserves (fun w => stagedAt w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_staged _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (cache_reset _).wp (fun t => t = initial))
    | (rx_retention_head send4RetrySource; exact (send4Retry_staged _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | staged_send_step initial

theorem send4AfterCache_staged e cache bytes ds exactRx gen saddr srcIf route :
    SameView stagedAt (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  change Preserves (fun w => stagedAt w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact (send4Miss_staged _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_staged _ _ _ _ _).wp (fun t => t = initial))
    | staged_send_step initial

theorem send4_staged e cache bytes ds exactRx : SameView stagedAt (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  change Preserves (fun w => stagedAt w = initial) _
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (cache_get _ _).wp (fun t => t = initial))
    | (rx_retention_head send4AfterCacheSource; exact (send4AfterCache_staged _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | staged_send_step initial

theorem send6_staged (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView stagedAt (send6 e cache bytes ds exactRx) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (cache_get _ _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheReset; exact (cache_reset _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheSet; exact (cache_set _ _ _ _).wp (fun s => s = initial))
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact (tunnelXmit_staged _ _ _ _ _).wp (fun s => s = initial))
    | staged_send_step initial

theorem sendSkbToPeer_staged (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView stagedAt (sendSkbToPeer pid bytes ds) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4; exact (send4_staged _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_staged _ _ _ _ _).wp (fun s => s = initial))
    | staged_send_step initial

theorem send_buffer (pid : PeerId) (bytes : List UInt8) : SameView stagedAt (sendBufferToPeer pid bytes) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head send4; exact (send4_staged _ _ _ _ _).wp (· = initial))
    | (rx_retention_head send6; exact (send6_staged _ _ _ _ _).wp (· = initial))
    | staged_send_step initial

end Leanux.Proofs.WG.TransmitSecurity.Staged.Exact
