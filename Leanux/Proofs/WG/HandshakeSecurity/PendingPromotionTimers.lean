import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionScheduler
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialTimerFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity
open Responder.DriverCuts (hooks)

/-- Single-call pending frames from C2 pin
`7ff94e48c2a3323ef29e6fb62f82a4a64d43f218`. The source callback and all its
history transport are proved below, not supplied by this package. -/
structure H1TimerFrames : Prop where
  /-- `Noise.PendingTickets.delTimer_frame`. -/
  delete : ∀ pid timer, SameView view (delTimer pid timer)
  /-- `Noise.PendingTickets.modPeerTimer_frame`. -/
  modify : ∀ site pid timer delay, SameView view (modPeerTimer site pid timer delay)
  /-- `Noise.PendingTickets.purgeStagedPackets_frame`. -/
  purge : ∀ pid, SameView view (purgeStagedPackets pid)
  /-- `Noise.PendingTickets.clearPeerEndpointSrc_frame`. -/
  endpoint : ∀ pid, SameView view (clearPeerEndpointSrc pid)

theorem Carrier.delete_timer (frames : H1TimerFrames) (pid : PeerId) (timer : PeerTimer)
    (confirmed : List Nat) : Preserves (Carrier confirmed) (delTimer pid timer) :=
  Carrier.from_frame (Responder.DriverCuts.carrier_delete_timer pid timer) (frames.delete pid timer) confirmed

theorem Carrier.modify_timer (frames : H1TimerFrames) (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (modPeerTimer site pid timer delay) :=
  Carrier.from_frame (Responder.DriverCuts.carrier_modify_timer site pid timer delay)
    (frames.modify site pid timer delay) confirmed

private def editPeer (pid : PeerId) (f : Peer → Peer) : WG.M Unit := do
  let p ← getPeer pid
  setPeer pid (f p)

theorem Carrier.timer (quiet : H1PendingQuietFrames) (transmit : H1TransmitFrames)
    (frames : H1TimerFrames) (pid : PeerId) (timer : PeerTimer) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (timerCallback pid timer) := by
  have modify_eq (f : Peer → Peer) : editPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have retry_source : expiredRetransmitHandshake pid = (do
      let attempts := (← getPeer pid).timerHandshakeAttempts
      if ← branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES then
        delTimer pid .sendKeepalive
        purgeStagedPackets pid
        if ← branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial) then
          discard <| modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
      else
        editPeer pid (fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1})
        clearPeerEndpointSrc pid
        sendQueuedHandshakeInitiation pid true) := by
    simp only [expiredRetransmitHandshake,modify_eq,bind_assoc]
  have keepalive_source : expiredSendKeepalive pid = (do
      sendKeepalive pid
      if ← branch .keepaliveNeedAnother (← getPeer pid).timerNeedAnotherKeepalive then
        editPeer pid (fun p => {p with timerNeedAnotherKeepalive := false})
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
    | (rx_retention_head editPeer
       apply Carrier.modify_peer confirmed
       all_goals intro p; rfl)
    | (rx_retention_head clearPeerEndpointSrc
       exact Carrier.from_frame (Responder.DriverCuts.carrier_clear_endpoint _) (frames.endpoint _) confirmed)
    | (rx_retention_head purgeStagedPackets
       exact Carrier.from_frame (Responder.DriverCuts.carrier_purge _) (frames.purge _) confirmed)
    | (rx_retention_head delTimer; exact Carrier.delete_timer frames _ _ confirmed)
    | (rx_retention_head modPeerTimer; exact Carrier.modify_timer frames _ _ _ _ confirmed)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact Carrier.queued transmit _ _ confirmed)
    | (rx_retention_head sendKeepalive
       exact Carrier.bounds confirmed
         (ResidentMaterial.bounds_join (ConfiguredTraffic.keepalive _)
           ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive_slots) _))
         (PendingPromotion.preserves (quiet.keepalive _) confirmed))
    | (rx_retention_head peerGet; exact Carrier.peer_get confirmed _)
    | (rx_retention_head getDev; exact Carrier.store confirmed getDev_sameWGStore)
    | pending_carrier_poll_step (), confirmed

theorem timer_quiet (pid : PeerId) (timer : PeerTimer) : LabelsQuiet (Driver.timerObserved hooks pid timer) :=
  fun initial => Driver.timer_history (quiet_hooks initial).actors.toActorCoreHistorySafe pid timer

theorem timer_erases (pid : PeerId) (timer : PeerTimer) :
    ErasesStatePrefix (Driver.timerObserved hooks pid timer) (timerCallback pid timer) := by
  apply native_via_nonce (Driver.timer_projects native_projection pid timer)
    (Driver.timer_projects NativeDriver.nonce_projection pid timer)
  rw [Driver.nonce_timerObserved_eq]
  exact Nonce.timerObserved_erases pid timer

theorem timer (quiet : H1PendingQuietFrames) (transmit : H1TransmitFrames)
    (frames : H1TimerFrames) (pid : PeerId) (t : PeerTimer) : Observed (Driver.timerObserved hooks pid t) :=
  quiet_native (timer_quiet pid t) (timer_erases pid t) (Carrier.timer quiet transmit frames pid t)

/-- C2 `Noise.PendingTickets.runFlushedSendWork_retained` and
`runFlushedClearWork_retained` at the same pin as `H1TimerFrames`. Both facts
are native pending-projection retention, not history invariants. -/
structure H1FlushedFrames : Prop where
  send : ∀ pid, ProjectedAction view Retained (runFlushedSendWork pid)
  clear : ∀ pid, ProjectedAction view Retained (runFlushedClearWork pid)

theorem Carrier.flushed_send (frames : H1FlushedFrames) (pid : PeerId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (runFlushedSendWork pid) :=
  Carrier.from_retained (Responder.DriverCuts.carrier_flushed_send pid) (frames.send pid) confirmed

theorem Carrier.flushed_clear (frames : H1FlushedFrames) (pid : PeerId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (runFlushedClearWork pid) :=
  Carrier.bounds confirmed (ResidentMaterial.bounds_flushed_clear pid)
    (PendingPromotion.preserves (frames.clear pid) confirmed)

theorem wg_read : ProductPreserves (liftPrefix getWG) :=
  product_store _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    ProductPreserves (liftPrefix (modifyWG f)) :=
  product_store _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : ProductPreserves (liftPrefix getEnv) := by
  apply product_lift
  intro confirmed
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases run
  exact hi

theorem send_one (frames : H1FlushedFrames) : ProductPreserves (liftPrefix Env.runOneSendWorker) :=
  product_lift _ (fun confirmed => ResidentMaterial.send_one_preserves
    (Carrier.store confirmed getDev_sameWGStore) (fun pid => Carrier.flushed_send frames pid confirmed))

theorem clear_one (frames : H1FlushedFrames) : ProductPreserves (liftPrefix Env.runOneClearWorker) :=
  product_lift _ (fun confirmed => ResidentMaterial.clear_one_preserves
    (Carrier.store confirmed getDev_sameWGStore) (fun pid => Carrier.flushed_clear frames pid confirmed))

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
