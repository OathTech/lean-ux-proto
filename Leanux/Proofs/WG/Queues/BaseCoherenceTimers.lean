import Leanux.Proofs.WG.Queues.BaseCoherenceCompletion
import Leanux.Proofs.WG.Queues.SlotTimers

/-! All five real timer callbacks retain the base list and public-key rows.
Queue append/coalescing, final peer payment and timer records remain actual. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem clearEndpoint_view (pid : PeerId) : SameView view (clearPeerEndpointSrc pid) := by
  have cache : SameView view (dstCacheReset pid) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.combined_frame)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.dstCacheReset_frame) pid)
      (ConfiguredIdentity.cacheReset pid)
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | (rx_retention_head dstCacheReset; exact cache.wp (fun s => s=initial))
    | base_rx_step initial

theorem purgeStaged_view (pid : PeerId) : SameView view (purgeStagedPackets pid) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold purgeStagedPackets
  repeat' base_rx_step initial

macro "base_timer_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc; exact (clearEndpoint_view _).wp (fun s => s=$initial))
  | (rx_retention_head purgeStagedPackets; exact (purgeStaged_view _).wp (fun s => s=$initial))
  | (rx_retention_head WG.sendKeepalive; exact (keepalive_view _).wp (fun s => s=$initial))
  | (rx_retention_head sendQueuedHandshakeInitiation; exact (sendQueued_view _ _).wp (fun s => s=$initial))
  | (rx_retention_head delTimer; exact (delTimer_view _ _).wp (fun s => s=$initial))
  | (rx_retention_head modPeerTimer; exact (modTimer_view _ _ _ _).wp (fun s => s=$initial))
  | (rx_retention_head Functor.discard
     apply discard_view_spec view (fun s => s=$initial)
     change Preserves (fun w => view w=$initial) _
     exact (modTimer_view _ _ _ _).wp (fun s => s=$initial))
  | base_rx_step $initial)

/-- The exact timer dispatcher is covered for every constructor. This is a
normal-source field frame, not a claim that the callback is total. -/
theorem timerCallback_view (pid : PeerId) (timer : PeerTimer) :
    SameView view (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake =>
    intro initial
    change Preserves (fun w => view w=initial) (expiredRetransmitHandshake pid)
    unfold expiredRetransmitHandshake
    simp (config := {zeta := false}) only [branch,branchCmp]
    repeat' base_timer_step initial
  | sendKeepalive =>
    intro initial
    change Preserves (fun w => view w=initial) (expiredSendKeepalive pid)
    unfold expiredSendKeepalive
    simp (config := {zeta := false}) only [branch]
    repeat' base_timer_step initial
  | newHandshake =>
    intro initial
    change Preserves (fun w => view w=initial) (expiredNewHandshake pid)
    unfold expiredNewHandshake
    repeat' base_timer_step initial
  | zeroKeyMaterial =>
    intro initial
    change Preserves (fun w => view w=initial) (expiredZeroKeyMaterial pid)
    unfold expiredZeroKeyMaterial
    simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
    repeat' base_timer_step initial
  | persistentKeepalive =>
    intro initial
    change Preserves (fun w => view w=initial) (expiredSendPersistentKeepalive pid)
    unfold expiredSendPersistentKeepalive
    simp (config := {zeta := false}) only [branch]
    repeat' base_timer_step initial

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
