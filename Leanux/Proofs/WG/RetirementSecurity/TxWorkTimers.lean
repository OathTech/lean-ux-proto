import Leanux.Proofs.WG.RetirementSecurity.TxActorNativeScheduler

/-! Native timer callbacks retain pending TX service. Keepalive callbacks
enter actual staging, whereas plaintext purge does not discharge allocated
TX cells. Peer acquisition and release retain their original source branches. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem serving_maintenance (call : MaintenanceCall) : Preserves (Serving locals crypt tx) call.original := by
  apply serving_join
  · cases call with
    | cache pid=>
      exact passive ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.dstCacheReset_cryptWire) pid)
        (ownership_queues ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.dstCacheReset_ownership) pid)) ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxWorkSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.TxWork.dstCacheReset_work) pid)
    | endpoint pid e=>
      exact passive (endpoint_cryptWire pid e)
        (ownership_queues (endpoint_ownership pid e)) (endpoint_work pid e)
    | arm pid timer delay clock=>
      exact passive (armTimer_cryptWire pid timer delay clock)
        (ownership_queues (armTimer_ownership pid timer delay clock)) (armTimer_work pid timer delay clock)
    | deleteTimer pid timer=>
      exact passive (delTimer_cryptWire pid timer)
        (ownership_queues (delTimer_ownership pid timer)) (delTimer_work pid timer)
    | guard pid=>
      exact passive (modPeerTimerGuard_cryptWire pid)
        (ownership_queues (modPeerTimerGuard_ownership pid)) (modPeerTimerGuard_work pid)
    | modifyTimer site pid timer delay=>
      exact passive (modPeerTimer_cryptWire site pid timer delay)
        (ownership_queues (modPeerTimer_ownership site pid timer delay)) (modPeerTimer_work site pid timer delay)
    | handshakeComplete pid site=>
      exact passive (handshakeComplete_cryptWire pid site)
        (ownership_queues (handshakeComplete_ownership pid site)) (handshake_complete_work pid site)
    | authenticatedReceived pid=>
      exact passive (delTimer_cryptWire pid .newHandshake)
        (ownership_queues (delTimer_ownership pid .newHandshake)) (delTimer_work pid .newHandshake)
    | dataReceived pid=>
      exact passive (dataReceived_cryptWire pid)
        (ownership_queues (dataReceived_ownership pid)) (data_received_work pid)
    | traversal pid=>
      exact passive (timersTraversal_cryptWire pid)
        (ownership_queues (timersTraversal_ownership pid)) (timersTraversal_work pid)
    | queuedHandshake pid retry=>
      exact passive (sendQueued_cryptWire pid retry)
        (ownership_queues (sendQueued_ownership pid retry)) (sendQueued_work pid retry)
    | keyFresh pid=>
      exact passive (freshRx_cryptWire pid)
        (ownership_queues (freshRx_ownership pid)) (fresh_rx_work pid)
  · exact TxCovered.Native.maintenance call

theorem serving_clear_endpoint (pid : PeerId) : Preserves (Serving locals crypt tx) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | (rx_retention_head dstCacheReset; exact serving_maintenance (.cache _))
    | serving_metadata_step

theorem serving_purge (pid : PeerId) : Preserves (Serving locals crypt tx) (purgeStagedPackets pid) := by
  apply serving_join
  · apply passive
    · intro initial; change Preserves (fun w=>txCryptWire w=initial) _
      unfold purgeStagedPackets
      repeat' crypt_wire_step initial
    · intro initial; change Preserves (fun w=>handoffTxView w=initial) _
      unfold purgeStagedPackets
      repeat' crypt_queue_step initial
    · intro initial; change Preserves (fun w=>queued w=initial) _
      unfold purgeStagedPackets
      repeat' tx_work_step initial
  · exact TxCovered.join (OccurrenceTimers.purge pid) (TxCoverageNative.purge pid)

theorem serving_peer_get (pid : PeerId) : Preserves (Serving locals crypt tx) (peerGet pid) :=
  serving_join (passive (peerGet_cryptWire pid) (ownership_queues (peerGet_ownership pid)) (peer_get pid))
    (TxCovered.Native.peer_get pid)

macro "serving_timer_step" : tactic => `(tactic| first
  | (rx_retention_head delTimer; exact serving_maintenance (.deleteTimer _ _))
  | (rx_retention_head modPeerTimer; exact serving_maintenance (.modifyTimer _ _ _ _))
  | (rx_retention_head sendKeepalive; exact serving_keepalive _)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact serving_maintenance (.queuedHandshake _ _))
  | (rx_retention_head clearPeerEndpointSrc; exact serving_clear_endpoint _)
  | (rx_retention_head purgeStagedPackets; exact serving_purge _)
  | (rx_retention_head peerGet; exact serving_peer_get _)
  | (rx_retention_head peerPut; exact serving_peer_put _)
  | serving_metadata_step)

theorem serving_callback (pid : PeerId) (timer : PeerTimer) :
    Preserves (Serving locals crypt tx) (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake =>
    change Preserves (Serving locals crypt tx) (expiredRetransmitHandshake pid)
    unfold expiredRetransmitHandshake
    simp (config := {zeta := false}) only [branch,branchCmp,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' serving_timer_step
  | sendKeepalive =>
    change Preserves (Serving locals crypt tx) (expiredSendKeepalive pid)
    unfold expiredSendKeepalive
    simp (config := {zeta := false}) only [branch,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' serving_timer_step
  | newHandshake =>
    change Preserves (Serving locals crypt tx) (expiredNewHandshake pid)
    unfold expiredNewHandshake
    repeat' serving_timer_step
  | zeroKeyMaterial =>
    change Preserves (Serving locals crypt tx) (expiredZeroKeyMaterial pid)
    unfold expiredZeroKeyMaterial
    simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
    repeat' serving_timer_step
  | persistentKeepalive =>
    change Preserves (Serving locals crypt tx) (expiredSendPersistentKeepalive pid)
    unfold expiredSendPersistentKeepalive
    simp (config := {zeta := false}) only [branch]
    repeat' serving_timer_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
