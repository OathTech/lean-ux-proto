import Leanux.Proofs.WG.RetirementSecurity.OccurrenceScheduler

/-! Actual timer callbacks and queued zero-material retirement preserve
physical TX ownership. Unpublication and final deallocation remain governed
by the separate key-reference ledger, not a no-retirement assumption. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimers
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits OccurrenceStack OccurrenceHandshake

theorem maintenance (call : MaintenanceCall) : Preserves (Ready locals active) call.original := by
  apply RxPollOccurrences.join call.erases call.allocation
  cases call with
  | cache pid =>
    exact occurrence_passive
      ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.dstCacheReset_cryptWire) pid)
      (ownership_queues ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.dstCacheReset_ownership) pid))
  | endpoint pid e =>
    exact occurrence_passive (endpoint_cryptWire pid e) (ownership_queues (endpoint_ownership pid e))
  | arm pid timer delay clock =>
    exact occurrence_passive (armTimer_cryptWire pid timer delay clock)
      (ownership_queues (armTimer_ownership pid timer delay clock))
  | deleteTimer pid timer =>
    exact occurrence_passive (delTimer_cryptWire pid timer) (ownership_queues (delTimer_ownership pid timer))
  | guard pid =>
    exact occurrence_passive (modPeerTimerGuard_cryptWire pid) (ownership_queues (modPeerTimerGuard_ownership pid))
  | modifyTimer site pid timer delay =>
    exact occurrence_passive (modPeerTimer_cryptWire site pid timer delay)
      (ownership_queues (modPeerTimer_ownership site pid timer delay))
  | handshakeComplete pid site =>
    exact occurrence_passive (handshakeComplete_cryptWire pid site) (ownership_queues (handshakeComplete_ownership pid site))
  | authenticatedReceived pid =>
    exact occurrence_passive (delTimer_cryptWire pid .newHandshake) (ownership_queues (delTimer_ownership pid .newHandshake))
  | dataReceived pid =>
    exact occurrence_passive (dataReceived_cryptWire pid) (ownership_queues (dataReceived_ownership pid))
  | traversal pid =>
    exact occurrence_passive (timersTraversal_cryptWire pid) (ownership_queues (timersTraversal_ownership pid))
  | queuedHandshake pid retry =>
    exact occurrence_passive (sendQueued_cryptWire pid retry) (ownership_queues (sendQueued_ownership pid retry))
  | keyFresh pid =>
    exact occurrence_passive (freshRx_cryptWire pid) (ownership_queues (freshRx_ownership pid))

theorem clear_endpoint (pid : PeerId) : Preserves (Ready locals active) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | (rx_retention_head dstCacheReset; exact maintenance (.cache _))
    | occurrence_ready_step

theorem purge (pid : PeerId) : Preserves (Ready locals active) (purgeStagedPackets pid) := by
  apply RxPollOccurrences.join (purgeStagedPacketsPrefix_erases pid)
    (purgeStagedPacketsPrefix_preserves_ambient allocationAmbient allocationTx pid)
  apply occurrence_passive
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    unfold purgeStagedPackets
    repeat' crypt_wire_step initial
  · intro initial
    change Preserves (fun w => handoffTxView w = initial) _
    unfold purgeStagedPackets
    repeat' crypt_queue_step initial

theorem peer_get (pid : PeerId) : Preserves (Ready locals active) (peerGet pid) :=
  RxPollOccurrences.join (peerGetMixed_erases pid) (allocationAmbient.peerGet pid)
    (ReceiveOccurrences.peer_get pid)

macro "occurrence_timer_step" : tactic => `(tactic| first
  | (rx_retention_head delTimer; exact maintenance (.deleteTimer _ _))
  | (rx_retention_head modPeerTimer; exact maintenance (.modifyTimer _ _ _ _))
  | (rx_retention_head sendKeepalive; exact keepalive _)
  | (rx_retention_head sendQueuedHandshakeInitiation; exact maintenance (.queuedHandshake _ _))
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head purgeStagedPackets; exact purge _)
  | (rx_retention_head peerGet; exact peer_get _)
  | (rx_retention_head peerPut; exact RxPollOccurrences.peer_put _)
  | occurrence_ready_step)

theorem callback (pid : PeerId) (timer : PeerTimer) :
    Preserves (Ready locals active) (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake =>
    change Preserves (Ready locals active) (expiredRetransmitHandshake pid)
    unfold expiredRetransmitHandshake
    simp (config := {zeta := false}) only [branch,branchCmp,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' occurrence_timer_step
  | sendKeepalive =>
    change Preserves (Ready locals active) (expiredSendKeepalive pid)
    unfold expiredSendKeepalive
    simp (config := {zeta := false}) only [branch,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' occurrence_timer_step
  | newHandshake =>
    change Preserves (Ready locals active) (expiredNewHandshake pid)
    unfold expiredNewHandshake
    repeat' occurrence_timer_step
  | zeroKeyMaterial =>
    change Preserves (Ready locals active) (expiredZeroKeyMaterial pid)
    unfold expiredZeroKeyMaterial
    simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
    repeat' occurrence_timer_step
  | persistentKeepalive =>
    change Preserves (Ready locals active) (expiredSendPersistentKeepalive pid)
    unfold expiredSendPersistentKeepalive
    simp (config := {zeta := false}) only [branch]
    repeat' occurrence_timer_step

theorem queued_zero (pid : PeerId) :
    Preserves (Ready locals active) (queuedExpiredZeroKeyMaterial pid) := by
  apply RxPollOccurrences.join (KeyMaintenanceCall.erases (.queuedClear pid))
    (KeyMaintenanceCall.allocation (.queuedClear pid))
  change Preserves (TxOccurrences locals active) (queuedExpiredZeroKeyMaterial pid)
  unfold queuedExpiredZeroKeyMaterial
  apply preserves_bind (occurrence_passive (OccurrenceKeys.handshake_clear_wire pid)
    (OccurrenceKeys.handshake_clear_queues pid))
  intro _
  apply preserves_bind (occurrence_passive (OccurrenceKeys.clear_wire pid) (OccurrenceKeys.clear_queues pid))
  intro _
  exact ReceiveOccurrences.peer_put (some pid)

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimers
