import Leanux.Proofs.WG.Queues.TxLiveTransmit

/-! Actual timer arming and callbacks preserve the logical TX live frontier
and physical encryption-ring refinement. Native keepalive may append fresh
items; it is composed by its proved Ready contract rather than a ring frame. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem place (pid : PeerId) (timer : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
    Preserves Ready (placeOnWheel pid timer expires clk unit) := by
  unfold placeOnWheel
  repeat' first | maintenance_store_leaf | live_send_step

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64) :
    Preserves Ready (armTimer pid timer delay clock) := by
  unfold armTimer
  repeat' first
    | (allocation_release_head placeOnWheel; exact place _ _ _ _ _)
    | maintenance_store_leaf
    | live_send_step

theorem del (pid : PeerId) (timer : PeerTimer) : Preserves Ready (delTimer pid timer) := by
  unfold delTimer
  repeat' first | maintenance_store_leaf | live_send_step

theorem mod_guard (pid : PeerId) : Preserves Ready (modPeerTimerGuard pid) := by
  unfold modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first | maintenance_store_leaf | live_send_step

theorem mod_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves Ready (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  repeat' first
    | (allocation_release_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp Ready)
    | (allocation_release_head modPeerTimerGuard; exact mod_guard _)
    | (allocation_release_head armTimer; exact arm _ _ _ _)
    | maintenance_store_leaf
    | live_send_step

macro "live_timer_step" : tactic => `(tactic| first
  | (allocation_release_head delTimer; exact del _ _)
  | (allocation_release_head armTimer; exact arm _ _ _ _)
  | (allocation_release_head modPeerTimer; exact mod_timer _ _ _ _)
  | (allocation_release_head modPeerTimerGuard; exact mod_guard _)
  | (allocation_release_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp Ready)
  | (allocation_release_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp Ready)
  | (allocation_release_head sendKeepalive; exact keepalive _)
  | (allocation_release_head sendQueuedHandshakeInitiation; exact queued _ _)
  | (allocation_release_head peekQueuedUnit; exact hoare_liftAmbient (AmbientM.peekQueuedUnit _ _) Ready)
  | (allocation_release_head recordQueued; exact hoare_liftAmbient (AmbientM.recordQueued _ _) Ready)
  | (allocation_release_head peerGet; exact peer_get _)
  | (allocation_release_head peerPut; exact peer_put _)
  | maintenance_store_leaf
  | live_send_step)

theorem data_sent (pid : PeerId) : Preserves Ready (timersDataSent pid) := by
  unfold timersDataSent
  simp (config := {zeta := false}) only [branch]
  repeat' live_timer_step

theorem data_received (pid : PeerId) : Preserves Ready (timersDataReceived pid) := by
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' live_timer_step

theorem authenticated_sent (pid : PeerId) : Preserves Ready (timersAnyAuthenticatedPacketSent pid) := del _ _

theorem authenticated_received (pid : PeerId) : Preserves Ready (timersAnyAuthenticatedPacketReceived pid) := del _ _

theorem handshake_complete (pid : PeerId) (site : HiddenSite) :
    Preserves Ready (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  repeat' live_timer_step

theorem session_derived (pid : PeerId) : Preserves Ready (timersSessionDerived pid) := by
  unfold timersSessionDerived
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' live_timer_step

theorem traversal (pid : PeerId) : Preserves Ready (timersTraversal pid) := by
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' live_timer_step

theorem initiated (pid : PeerId) : Preserves Ready (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated
  repeat' live_timer_step

theorem clear_endpoint (pid : PeerId) : Preserves Ready (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  repeat' first | maintenance_store_leaf | live_send_step

theorem purge_staged (pid : PeerId) : Preserves Ready (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  repeat' first | maintenance_store_leaf | live_send_step

/-- Each actual callback retains all queue/coalescing and timer records. The
result is normal-only; no state is invented on a failed guard or missing record. -/
theorem timer_callback (pid : PeerId) (timer : PeerTimer) :
    Preserves Ready (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake =>
    change Preserves Ready (expiredRetransmitHandshake pid)
    unfold expiredRetransmitHandshake
    simp (config := {zeta := false}) only [branch,branchCmp,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' first
      | (allocation_release_head clearPeerEndpointSrc; exact clear_endpoint _)
      | (allocation_release_head purgeStagedPackets; exact purge_staged _)
      | live_timer_step
  | sendKeepalive =>
    change Preserves Ready (expiredSendKeepalive pid)
    unfold expiredSendKeepalive
    simp (config := {zeta := false}) only [branch,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' first
      | (allocation_release_head clearPeerEndpointSrc; exact clear_endpoint _)
      | (allocation_release_head purgeStagedPackets; exact purge_staged _)
      | live_timer_step
  | newHandshake =>
    change Preserves Ready (expiredNewHandshake pid)
    unfold expiredNewHandshake
    repeat' first
      | (allocation_release_head clearPeerEndpointSrc; exact clear_endpoint _)
      | (allocation_release_head purgeStagedPackets; exact purge_staged _)
      | live_timer_step
  | zeroKeyMaterial =>
    change Preserves Ready (expiredZeroKeyMaterial pid)
    unfold expiredZeroKeyMaterial
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (allocation_release_head clearPeerEndpointSrc; exact clear_endpoint _)
      | (allocation_release_head purgeStagedPackets; exact purge_staged _)
      | live_timer_step
  | persistentKeepalive =>
    change Preserves Ready (expiredSendPersistentKeepalive pid)
    unfold expiredSendPersistentKeepalive
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (allocation_release_head clearPeerEndpointSrc; exact clear_endpoint _)
      | (allocation_release_head purgeStagedPackets; exact purge_staged _)
      | live_timer_step

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
