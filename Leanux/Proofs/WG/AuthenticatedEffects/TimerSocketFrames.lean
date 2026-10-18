import Leanux.Proofs.WG.AuthenticatedEffects.TimerHandshakeFrames
import Leanux.Proofs.WG.Queues.HolderWorkFrames
import Leanux.Proofs.WG.Cookies.Frames

/-! Actual socket and handshake receive callbacks preserve timer provenance.
The source factors for routing and cache fallback are the existing native cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

macro "timer_socket_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (allocation_release_lift_from Net.M; exact retained_store (liftRouting_sameWGStore _) $initial)
  | (rx_retention_head liftRouting; exact retained_store (liftRouting_sameWGStore _) $initial)
  | (rx_retention_head getRouting; exact retained_store (liftRouting_sameWGStore
      ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))) $initial)
  | timer_handshake_step $initial)

theorem dstCacheReset_retained (pid : PeerId) (initial) :
    Preserves (Retained initial) (dstCacheReset pid) := by
  unfold dstCacheReset
  simp only [getAmbient,hiddenJiffies]
  repeat' timer_socket_step initial

private theorem dstCacheGet_frame (pid : PeerId) (gen : Nat) : ∀ initial, Preserves (Retained initial) (dstCacheGet pid gen) := by
  intro initial
  change Preserves (Retained initial) _
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' timer_socket_step initial

private theorem dstCacheSet_frame (pid : PeerId) (src gen dev : Nat) : ∀ initial, Preserves (Retained initial) (dstCacheSet pid src gen dev) := by
  intro initial
  change Preserves (Retained initial) _
  unfold dstCacheSet
  repeat' timer_socket_step initial

private theorem tunnelXmit_frame (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    ∀ initial, Preserves (Retained initial) ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  change Preserves (Retained initial) _
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact retained_store (Queues.loopbackSend_kernel _ _) initial)
    | (rx_retention_head socketPort
       exact retained_store (socketPort_sameStore _) initial)
    | timer_socket_step initial

private theorem send4ClearSrc_frame cache : ∀ initial, Preserves (Retained initial) (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  change Preserves (Retained initial) _
  repeat' first
    | timer_socket_step initial

private theorem send4Finish_frame e bytes ds exactRx route : ∀ initial, Preserves (Retained initial) (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  change Preserves (Retained initial) _
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact tunnelXmit_frame _ _ _ _ _ initial)
    | timer_socket_step initial

private theorem send4RouteDone_frame e cache bytes ds exactRx gen fallback rt :
    ∀ initial, Preserves (Retained initial) (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  change Preserves (Retained initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact dstCacheSet_frame _ _ _ _ initial)
    | (rx_retention_head send4FinishSource; exact send4Finish_frame _ _ _ _ _ initial)
    | timer_socket_step initial

private theorem send4Retry_frame e cache bytes ds exactRx gen fallback srcIf rt :
    ∀ initial, Preserves (Retained initial) (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  change Preserves (Retained initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact send4ClearSrc_frame _ initial)
    | (rx_retention_head dstCacheReset; exact dstCacheReset_retained _ initial)
    | (rx_retention_head send4RouteDoneSource; exact send4RouteDone_frame _ _ _ _ _ _ _ _ initial)
    | timer_socket_step initial

private theorem send4Miss_frame e cache bytes ds exactRx gen fallback saddr srcIf :
    ∀ initial, Preserves (Retained initial) (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  change Preserves (Retained initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact send4ClearSrc_frame _ initial)
    | (rx_retention_head dstCacheReset; exact dstCacheReset_retained _ initial)
    | (rx_retention_head send4RetrySource; exact send4Retry_frame _ _ _ _ _ _ _ _ _ initial)
    | timer_socket_step initial

private theorem send4AfterCache_frame e cache bytes ds exactRx gen saddr srcIf route :
    ∀ initial, Preserves (Retained initial) (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  change Preserves (Retained initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact send4Miss_frame _ _ _ _ _ _ _ _ _ initial)
    | (rx_retention_head send4FinishSource; exact send4Finish_frame _ _ _ _ _ initial)
    | timer_socket_step initial

private theorem send4_frame e cache bytes ds exactRx : ∀ initial, Preserves (Retained initial) (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  change Preserves (Retained initial) _
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact dstCacheGet_frame _ _ initial)
    | (rx_retention_head send4AfterCacheSource; exact send4AfterCache_frame _ _ _ _ _ _ _ _ _ initial)
    | timer_socket_step initial

private theorem send6_frame (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ∀ initial, Preserves (Retained initial) (send6 e cache bytes ds exactRx) := by
  intro initial
  change Preserves (Retained initial) _
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact dstCacheGet_frame _ _ initial)
    | (rx_retention_head dstCacheReset; exact dstCacheReset_retained _ initial)
    | (rx_retention_head dstCacheSet; exact dstCacheSet_frame _ _ _ _ initial)
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact tunnelXmit_frame _ _ _ _ _ initial)
    | timer_socket_step initial

theorem sendBufferToPeer_retained (pid : PeerId) (bytes : List UInt8) : ∀ initial, Preserves (Retained initial) (sendBufferToPeer pid bytes) := by
  intro initial
  change Preserves (Retained initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head send4; exact send4_frame _ _ _ _ _ initial)
    | (rx_retention_head send6; exact send6_frame _ _ _ _ _ initial)
    | timer_socket_step initial


theorem cookieConsume_retained (msg : Key) (initial) :
    Preserves (Retained initial) (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp only [branch,hiddenClock64,invariant]
  repeat' timer_handshake_step initial

theorem cookie_retained {action : WG.M α} (frame : SameCookie action) (initial) :
    Preserves (Retained initial) action := by
  apply retained_exact
  apply frame.of_factor (fun s : WGOwnedView => fun pid t =>
    (s.dev.bind fun d => d.peers[pid]?).map (fun p => (p.internalId,p.timer t,p.wheel t))) view
  intro w
  funext pid t
  simp only [view,cookieView,cookieDevice,wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def]

theorem noise_retained {action : WG.M α} (frame : Cookies.NoNoiseChange action) (initial) :
    Preserves (Retained initial) action := by
  apply retained_exact
  apply frame.of_factor (fun s => fun pid t =>
    (s.1.bind fun d => d.peers[pid]?).map (fun p => (p.internalId,p.timer t,p.wheel t))) view
  intro w
  funext pid t
  simp only [view,Cookies.noiseView,Cookies.viewOfStore,Cookies.scrub,wgStoreView,
    Option.bind_map,Function.comp_def]

theorem cookieSend_retained (msg : Key) (src : SkbSource) (initial) :
    Preserves (Retained initial) (sendHandshakeCookie msg src) :=
  noise_retained (Cookies.sendHandshakeCookie_frame msg src) initial

theorem endpoint_retained (pid : PeerId) (src : SkbSource) (initial) :
    Preserves (Retained initial) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb setPeerEndpoint endpointFromSkb endpointEq
  simp only [WG.andM,branch,invariant,unsupported,requireNotPending]
  repeat' first
    | (rx_retention_head dstCacheReset; exact dstCacheReset_retained _ initial)
    | timer_socket_step initial

theorem guard_retained (pid : PeerId) (initial) :
    Preserves (Retained initial) (modPeerTimerGuard pid) := by
  unfold modPeerTimerGuard
  simp only [WG.andM,branch]
  repeat' timer_handshake_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
