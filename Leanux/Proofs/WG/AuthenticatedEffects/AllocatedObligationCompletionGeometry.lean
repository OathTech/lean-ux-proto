import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceStagingFrames
import Leanux.Proofs.WG.Lifetimes.SocketSend4

/-! Actual IPv4 and IPv6 send paths preserve all packet allocation frontiers
and packet records, including their error returns and routing-cache writes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionGeometry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity.StagingOccurrences (geometry)

private theorem geometry_store {action : WG.M α} (same : SameWGStore action) :
    SameView geometry action :=
  same.of_factor (fun s : WGStoreView => geometry {dev := s.dev}) geometry (fun _ => rfl)

macro "completion_socket_geometry_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getAmbient; unfold getAmbient; exact hoare_liftAmbient _ _)
  | (rx_retention_head invariant; unfold invariant; exact hoare_liftAmbient _ _)
  | (rx_retention_head hiddenJiffies; unfold hiddenJiffies; exact hoare_liftAmbient _ _)
  | (rx_retention_head getRouting; unfold getRouting; exact (geometry_store (liftRouting_sameWGStore _)) $initial)
  | (rx_retention_head liftRouting; exact (geometry_store (liftRouting_sameWGStore _)) $initial)
  | (allocation_release_lift_from Net.M; exact (geometry_store (liftRouting_sameWGStore _)) $initial)
  | staging_geometry_step $initial)

theorem cache_reset (pid : PeerId) : SameView geometry (dstCacheReset pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold dstCacheReset
  repeat' completion_socket_geometry_step initial

theorem cache_set (pid : PeerId) (src gen dev : Nat) : SameView geometry (dstCacheSet pid src gen dev) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold dstCacheSet
  repeat' completion_socket_geometry_step initial

theorem cache_get (pid : PeerId) (gen : Nat) : SameView geometry (dstCacheGet pid gen) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' completion_socket_geometry_step initial

theorem tunnelXmit_geometry (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView geometry ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact (geometry_store (Queues.loopbackSend_kernel _ _)).wp (fun s => s = initial))
    | (rx_retention_head socketPort
       exact (geometry_store (socketPort_sameStore _)).wp (fun s => s = initial))
    | completion_socket_geometry_step initial

theorem send4ClearSrc_geometry cache : SameView geometry (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  change Preserves (fun w => geometry w = initial) _
  repeat' first
    | completion_socket_geometry_step initial

theorem send4Finish_geometry e bytes ds exactRx route : SameView geometry (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact (tunnelXmit_geometry _ _ _ _ _).wp (fun t => t = initial))
    | completion_socket_geometry_step initial

theorem send4RouteDone_geometry e cache bytes ds exactRx gen fallback rt :
    SameView geometry (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact (cache_set _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_geometry _ _ _ _ _).wp (fun t => t = initial))
    | completion_socket_geometry_step initial

theorem send4Retry_geometry e cache bytes ds exactRx gen fallback srcIf rt :
    SameView geometry (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_geometry _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (cache_reset _).wp (fun t => t = initial))
    | (rx_retention_head send4RouteDoneSource; exact (send4RouteDone_geometry _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | completion_socket_geometry_step initial

theorem send4Miss_geometry e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView geometry (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_geometry _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (cache_reset _).wp (fun t => t = initial))
    | (rx_retention_head send4RetrySource; exact (send4Retry_geometry _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | completion_socket_geometry_step initial

theorem send4AfterCache_geometry e cache bytes ds exactRx gen saddr srcIf route :
    SameView geometry (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact (send4Miss_geometry _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_geometry _ _ _ _ _).wp (fun t => t = initial))
    | completion_socket_geometry_step initial

theorem send4_geometry e cache bytes ds exactRx : SameView geometry (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (cache_get _ _).wp (fun t => t = initial))
    | (rx_retention_head send4AfterCacheSource; exact (send4AfterCache_geometry _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | completion_socket_geometry_step initial

theorem send6_geometry (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView geometry (send6 e cache bytes ds exactRx) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (cache_get _ _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheReset; exact (cache_reset _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheSet; exact (cache_set _ _ _ _).wp (fun s => s = initial))
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact (tunnelXmit_geometry _ _ _ _ _).wp (fun s => s = initial))
    | completion_socket_geometry_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionGeometry
