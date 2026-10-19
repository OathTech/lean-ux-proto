import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerNativeFrames

/-! Every native timer callback transports one exact holder account. Staging
and queued work absorb their actual deltas; metadata leaves preserve the
same existing account. Only normal native endpoints are claimed here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.TimerCallbacks
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits DurableHolders TimerFrames

private theorem staged_boundary (pid : PeerId) :
    Preserves (ExactBoundary cs loans) (sendStagedPackets pid) := ExactBoundary.staged pid

private theorem queued_boundary (pid : PeerId) (retry : Bool) :
    Preserves (ExactBoundary cs loans) (sendQueuedHandshakeInitiation pid retry) :=
  ExactBoundary.queued pid retry

private theorem ambient_state (action : AmbientM α) (a b : Ambient)
    (run : (((monadLift action : WG.M α)).run w).run a=.ok ((x,v),b)) : v=w :=
  (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient action (· = w)) w a x v b rfl run

/-- The keepalive allocates/stages only in its actual empty branch, then
uses the concrete staged-send delta. No queue readiness premise is needed. -/
theorem keepalive_boundary (pid : PeerId) : Preserves (ExactBoundary cs loans) (sendKeepalive pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  unfold sendKeepalive at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,getter,run⟩ := run
  obtain ⟨same,time,d,hd,hp⟩ := getPeer_normal pid w read p a ar getter
  subst read
  subst ar
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨empty,guarded,ag,guard,run⟩ := run
  have same := ambient_state (AmbientM.branch .keepaliveStagedEmpty p.staged.isEmpty) a ag guard
  subst guarded
  cases empty with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at run
    exact (hoare_iff_run_ambient _ _ _).mp (staged_boundary pid) w ag x v b hi run
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨allocated,read,aa,alloc,failed,guarded,af,guard,run⟩ := run
    have same := ambient_state (AmbientM.hiddenAlloc .keepaliveSkb) ag aa alloc
    subst read
    have same := ambient_state (AmbientM.branch .keepaliveNoMem (!allocated)) aa af guard
    subst guarded
    cases failed with
    | true =>
      simp only [ite_true] at run
      cases run
      exact hi
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨dev,read,ad,getter,u,staged,as_,write,run⟩ := run
      obtain ⟨same,time,_⟩ := DecryptCarrier.getDev_current af ad getter
      subst read
      subst ad
      have kept := source_modify hi hd hp
        (fun p => {p with staged := p.staged ++ [{mtu := dev.mtu}]})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ _ h => h) (fun _ => rfl) af as_ write
      exact (hoare_iff_run_ambient _ _ _).mp (staged_boundary pid) staged as_ x v b kept run

theorem modTimer_boundary (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (ExactBoundary cs loans) (modPeerTimer site pid timer delay) :=
  TimerFrames.exists_account fun _ => TimerFrames.control
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.modPeerTimer_view) site pid timer delay)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.mod_preserves) site pid timer delay)

theorem delTimer_boundary (pid : PeerId) (timer : PeerTimer) :
    Preserves (ExactBoundary cs loans) (delTimer pid timer) :=
  TimerFrames.exists_account fun _ => TimerFrames.control
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.delTimer_view) pid timer)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.del_preserves) pid timer)

private theorem endpoint_boundary {cs : Ledger} {loans : Reservations}
    (pid : PeerId) :
    Preserves (ExactBoundary cs loans) (clearPeerEndpointSrc pid) := by
  have cacheWrite (ts : UInt64) : Preserves (ExactBoundary cs loans)
      (do let p ← getPeer pid; setPeer pid {p with dstCache := {p.dstCache with resetTs := ts}}) :=
    modify_boundary pid (fun p => {p with dstCache := {p.dstCache with resetTs := ts}})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ hk => hk) (fun _ => rfl)
  have cache : Preserves (ExactBoundary cs loans) (dstCacheReset pid) := by
    unfold dstCacheReset
    simp only [getAmbient,hiddenJiffies]
    repeat' first
      | (env_bind_head getPeer; exact cacheWrite _)
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))
      | rx_retention_step
  have now : Preserves (ExactBoundary cs loans) (dstCacheResetNow pid) := by
    unfold dstCacheResetNow
    apply preserves_bind cache
    intro _
    exact modify_boundary pid (fun p => {p with dstCache := {p.dstCache with slot := none}})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ _ hk => hk) (fun _ => rfl)
  unfold clearPeerEndpointSrc
  rw [← bind_assoc]
  apply preserves_bind (modify_boundary pid
    (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0,srcIf := 0}})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ hk => hk) (fun _ => rfl))
  intro _
  exact now

/-- Purging staged bytes pays no durable batch: the staged list is uncharged.
The actual saved-peer setter and dropped-byte accounting remain in order. -/
theorem purge_boundary (pid : PeerId) : Preserves (ExactBoundary cs loans) (purgeStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  unfold purgeStagedPackets at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,getter,run⟩ := run
  obtain ⟨same,time,d,hd,hp⟩ := getPeer_normal pid w read p a ar getter
  subst read
  subst ar
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨u,stats,as_,write,run⟩ := run
  cases write
  have fields : HolderEncrypt.fields
      {w with dev := w.dev.map fun d => {d with txDropped := d.txDropped+p.staged.length}} = HolderEncrypt.fields w := by
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    simp [hd,rxView]
  have kept := ExactBoundary.fields hi fields
  exact source_modify (d := {d with txDropped := d.txDropped+p.staged.length}) kept
    (by simp [hd]) hp (fun p => {p with staged := []})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => h) (fun _ => rfl) a b run

/-- The retransmit callback follows its actual give-up, re-arm and queued
handshake paths; the latter retains the source-acquired work reservation. -/
theorem retransmit_boundary (pid : PeerId) :
    Preserves (ExactBoundary cs loans) (expiredRetransmitHandshake pid) := by
  have attempts := modify_boundary (cs := cs) (loans := loans) pid
    (fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts+1})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => h) (fun _ => rfl)
  unfold expiredRetransmitHandshake
  apply preserves_bind (read_boundary pid)
  intro p
  apply preserves_bind (hoare_liftAmbient (AmbientM.branchCmp .retransmitGiveUp
    (p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES) p.timerHandshakeAttempts MAX_TIMER_HANDSHAKES) (ExactBoundary cs loans))
  intro giveUp
  cases giveUp with
  | false =>
    simpa only [Bool.false_eq_true,ite_false,bind_assoc] using
      preserves_bind attempts (fun _ => preserves_bind (endpoint_boundary pid)
        (fun _ => queued_boundary pid true))
  | true =>
    apply preserves_bind (delTimer_boundary pid .sendKeepalive)
    intro _
    apply preserves_bind (purge_boundary pid)
    intro _
    apply preserves_bind (read_boundary pid)
    intro p
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .retransmitZeroKeyNotPending
      (!p.timerPending .zeroKeyMaterial)) (ExactBoundary cs loans))
    intro pending
    cases pending with
    | false => exact preserves_pure _
    | true =>
      apply discard_view_spec id (ExactBoundary cs loans)
      exact modTimer_boundary .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS

/-- The keepalive callback includes its real optional timer re-arm. -/
theorem keepaliveTimer_boundary (pid : PeerId) :
    Preserves (ExactBoundary cs loans) (expiredSendKeepalive pid) := by
  have clear := modify_boundary (cs := cs) (loans := loans) pid
    (fun p => {p with timerNeedAnotherKeepalive := false})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => h) (fun _ => rfl)
  unfold expiredSendKeepalive
  apply preserves_bind (keepalive_boundary pid)
  intro _
  apply preserves_bind (read_boundary pid)
  intro p
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .keepaliveNeedAnother p.timerNeedAnotherKeepalive)
    (ExactBoundary cs loans))
  intro another
  cases another with
  | false => exact preserves_pure _
  | true =>
    rw [←bind_assoc]
    apply preserves_bind clear
    intro _
    apply discard_view_spec id (ExactBoundary cs loans)
    exact modTimer_boundary .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS

theorem persistent_boundary (pid : PeerId) :
    Preserves (ExactBoundary cs loans) (expiredSendPersistentKeepalive pid) := by
  unfold expiredSendPersistentKeepalive
  apply preserves_bind (read_boundary pid)
  intro p
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .persistentKeepaliveInterval
    (p.persistentKeepaliveInterval != 0)) (ExactBoundary cs loans))
  intro enabled
  cases enabled
  · exact preserves_pure _
  · exact keepalive_boundary pid

theorem zero_boundary (pid : PeerId) :
    Preserves (ExactBoundary cs loans) (expiredZeroKeyMaterial pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  obtain ⟨h,account⟩ := hi
  obtain ⟨added,_,post⟩ := account.expired_zero pid a b run
  exact ⟨HolderTimers.addClear h added,post⟩

theorem newHandshake_boundary (pid : PeerId) :
    Preserves (ExactBoundary cs loans) (expiredNewHandshake pid) := by
  unfold expiredNewHandshake
  exact preserves_bind (endpoint_boundary pid) (fun _ => queued_boundary pid false)

/-- All five actual callbacks preserve a complete aligned funded account.
New work/batches remain charged; control writes retain existing obligations.
This contract is normal-return preservation, not timer-dispatch totality. -/
theorem callback_boundary (pid : PeerId) (timer : PeerTimer) :
    Preserves (ExactBoundary cs loans) (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact retransmit_boundary pid
  | sendKeepalive => exact keepaliveTimer_boundary pid
  | newHandshake => exact newHandshake_boundary pid
  | zeroKeyMaterial => exact zero_boundary pid
  | persistentKeepalive => exact persistent_boundary pid

/-- The product lift runs the same WG/Ambient callback with the complete
account; unrelated product components need no additional premise. -/
theorem callback_product (pid : PeerId) (timer : PeerTimer) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (liftWG (timerCallback pid timer)) :=
by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact (hoare_iff_run_ambient _ _ _).mp (callback_boundary pid timer)
    w.wg w.ambient x v.wg v.ambient hi
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) _ w v x run)

/-- The original lifetime observer has exactly the same normal endpoint,
with arbitrary incoming history and the callback's actual Ambient cuts. -/
theorem callback_observed (pid : PeerId) (timer : PeerTimer)
    (hi : ExactBoundary cs loans w) (history : List LifetimeEvent) (a b : Ambient)
    (run : (runStatePrefix (timerCallbackPrefix pid timer) w a history).1 = .ok ((result,v),b)) :
    ExactBoundary cs loans v :=
  (hoare_iff_run_ambient _ _ _).mp (callback_boundary pid timer) w a result v b hi
    ((timerCallbackPrefix_erases pid timer w a history).symm.trans run)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.TimerCallbacks
