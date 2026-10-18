import Leanux.Proofs.WG.Noise.PendingTimerFrames

set_option autoImplicit false

namespace Leanux.Proofs.WG.Noise.PendingTimers
open Leanux Leanux.WG Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open PendingReception PendingSession

/-- Variant of CurrentSlots.Timer.callback for the pending-confirmation
invariant. Only normal endpoints have a state claim. -/
theorem callback_pending_variant (pid : PeerId) (timer : PeerTimer) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (timerCallback pid timer) := by
  have modify_eq (f : Peer → Peer) : modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have retry_source : expiredRetransmitHandshake pid = (do
      let attempts := (← getPeer pid).timerHandshakeAttempts
      if ← branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES then
        delTimer pid .sendKeepalive
        purgeStagedPackets pid
        if ← branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial) then
          discard <| modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
      else
        modifyPeer pid (fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1})
        clearPeerEndpointSrc pid
        sendQueuedHandshakeInitiation pid true) := by
    simp only [expiredRetransmitHandshake,modify_eq,bind_assoc]
  have keepalive_source : expiredSendKeepalive pid = (do
      sendKeepalive pid
      if ← branch .keepaliveNeedAnother (← getPeer pid).timerNeedAnotherKeepalive then
        modifyPeer pid (fun p => {p with timerNeedAnotherKeepalive := false})
        discard <| modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS) := by
    simp only [expiredSendKeepalive,modify_eq,bind_assoc]
  cases timer <;> simp only [timerCallback]
  all_goals first
    | rw [retry_source]
    | rw [keepalive_source]
    | unfold expiredNewHandshake
    | unfold expiredZeroKeyMaterial
    | unfold expiredSendPersistentKeepalive
  all_goals try simp (config := {zeta := false}) only
    [branch,branchCmp,peekQueuedUnit,recordQueued,discard,map_const,Function.comp_def,map_eq_pure_bind]
  all_goals repeat' first
    | (rx_retention_head modifyPeer
       apply native_update _ _ ?_ ?_ ?_ seen
       all_goals intro p; rfl)
    | (rx_retention_head clearPeerEndpointSrc; exact configuration_clear_endpoint _ seen)
    | (rx_retention_head purgeStagedPackets; exact purge_native _ seen)
    | (rx_retention_head delTimer; exact del_native _ _ seen)
    | (rx_retention_head modPeerTimer; exact mod_native _ _ _ _ seen)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued_native _ _ seen)
    | (rx_retention_head sendKeepalive; exact keepalive _ seen)
    | (rx_retention_head peerGet; exact peerGet_native _ seen)
    | (rx_retention_head peerPut; exact pay _ seen)
    | pending_native_step seen

/-- Variant of CurrentSlots.Timer.dispatch for the pending-confirmation
invariant, on the unchanged recorded dispatch unit. Selection guards, detachment,
section boundaries and the timerPassStep writes remain the actual calls. -/
theorem dispatch_pending_variant (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen)
      (timerDispatchUnit worker pid timer entry prior) := by
  unfold timerDispatchUnit
  simp (config := {zeta := false}) only [peekUnit]
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact timer_section _ _ seen (native_product _ (callback_pending_variant _ _) seen))
    | (allocation_release_lift_from WG.M
       exact native_product _ (del_native _ _) seen)
    | pending_timer_product_step seen

/-- Variant of CurrentSlots.Timer.placeholder for the existing literal
placeholder pass. The wheel is read again each iteration; no saved-device
invariant, new loop bound or work-progress conclusion is supplied. -/
theorem placeholder_pending_variant (j : UInt64) (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) (RxHistory.placeholderTimerPassSource j) := by
  unfold RxHistory.placeholderTimerPassSource
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact timer_section _ _ seen (native_product _ (callback_pending_variant _ _) seen))
    | (allocation_release_lift_from WG.M
       first
       | exact PendingScheduler.product_store _ (liftWG_sameProductStore getDev getDev_sameWGStore) seen
       | exact native_product _ (del_native _ _) seen)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => NativeInv w.wg seen)
       intro _ _
       change Preserves (fun w : World => NativeInv w.wg seen) _)
    | pending_timer_product_step seen

end Leanux.Proofs.WG.Noise.PendingTimers
