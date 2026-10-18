import Leanux.Proofs.WG.Queues.TxLiveKeys

/-! The actual socket route/cache source retains the TX live frontier. These
contracts keep normal errno returns and all original socket/route/record Stops;
loopback output is the modeled native send, not an invented RX callback. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

macro "live_socket_step" : tactic => `(tactic| first
  | (allocation_release_lift_from Net.M; exact store_ready _ (liftRouting_sameWGStore _))
  | (allocation_release_head liftRouting; exact store_ready _ (liftRouting_sameWGStore _))
  | (allocation_release_head getRouting
     exact store_ready _ (liftRouting_sameWGStore
       ((fun (s : Net.State)=>s.toRouting) <$> (get : Net.M Net.State))))
  | live_key_step)

private theorem cache_get (pid : PeerId) (gen : Nat) : Preserves Ready (dstCacheGet pid gen) := by
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' live_socket_step

private theorem cache_set (pid : PeerId) (src gen dev : Nat) : Preserves Ready (dstCacheSet pid src gen dev) := by
  unfold dstCacheSet
  repeat' live_socket_step

private theorem cache_reset (pid : PeerId) : Preserves Ready (dstCacheReset pid) := by
  unfold dstCacheReset
  simp (config := {zeta := false}) only [hiddenJiffies,getAmbient]
  repeat' live_socket_step

theorem tunnel (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    Preserves Ready ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact store_ready _ (loopbackSend_kernel _ _))
    | (rx_retention_head socketPort
       exact store_ready _ (socketPort_sameStore _))
    | live_socket_step

private theorem send4_clear cache : Preserves Ready (send4ClearSrcSource cache) := by
  unfold send4ClearSrcSource
  repeat' first
    | live_socket_step

private theorem send4_finish e bytes ds exactRx route : Preserves Ready (send4FinishSource e bytes ds exactRx route) := by
  unfold send4FinishSource
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact tunnel _ _ _ _ _)
    | live_socket_step

private theorem send4_route e cache bytes ds exactRx gen fallback rt :
    Preserves Ready (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  unfold send4RouteDoneSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact cache_set _ _ _ _)
    | (rx_retention_head send4FinishSource; exact send4_finish _ _ _ _ _)
    | live_socket_step

private theorem send4_retry e cache bytes ds exactRx gen fallback srcIf rt :
    Preserves Ready (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  unfold send4RetrySource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact send4_clear _)
    | (rx_retention_head dstCacheReset; exact cache_reset _)
    | (rx_retention_head send4RouteDoneSource; exact send4_route _ _ _ _ _ _ _ _)
    | live_socket_step

private theorem send4_miss e cache bytes ds exactRx gen fallback saddr srcIf :
    Preserves Ready (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  unfold send4MissSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact send4_clear _)
    | (rx_retention_head dstCacheReset; exact cache_reset _)
    | (rx_retention_head send4RetrySource; exact send4_retry _ _ _ _ _ _ _ _ _)
    | live_socket_step

private theorem send4_after e cache bytes ds exactRx gen saddr srcIf route :
    Preserves Ready (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  unfold send4AfterCacheSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact send4_miss _ _ _ _ _ _ _ _ _)
    | (rx_retention_head send4FinishSource; exact send4_finish _ _ _ _ _)
    | live_socket_step

theorem socket4 e cache bytes ds exactRx : Preserves Ready (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  unfold send4Source
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact cache_get _ _)
    | (rx_retention_head send4AfterCacheSource; exact send4_after _ _ _ _ _ _ _ _ _)
    | live_socket_step

theorem socket6 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    Preserves Ready (send6 e cache bytes ds exactRx) := by
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact cache_get _ _)
    | (rx_retention_head dstCacheReset; exact cache_reset _)
    | (rx_retention_head dstCacheSet; exact cache_set _ _ _ _)
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact tunnel _ _ _ _ _)
    | live_socket_step

theorem send_buffer (pid : PeerId) (bytes : List UInt8) : Preserves Ready (sendBufferToPeer pid bytes) := by
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head send4; exact socket4 _ _ _ _ _)
    | (rx_retention_head send6; exact socket6 _ _ _ _ _)
    | live_socket_step

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
