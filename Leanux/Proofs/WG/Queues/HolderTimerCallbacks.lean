import Leanux.Proofs.WG.Queues.HolderTimers
import Leanux.Proofs.WG.Queues.HolderEncryptFrames
import Leanux.Proofs.WG.Lifetimes.TimerCallbacks

/-! The remaining concrete timer callbacks retain complete attributed holders.
Actual staged sends absorb their own delta; control writes retain the account. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderTimers
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

/-- Actual staged send retains every acquired TX/send holder. -/
theorem staged_funded (pid : PeerId) {h : DurableHolders}
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ (h.absorb delta).Funded cs loans v ∧ StableRx cs v := by
  have transfer := staged_send_handoff pid (hi.carriers.keys.2 pid) a b run
  have keys := staged_send_keys pid hi.carriers.keys a b run
  have passive := (hoare_iff_run_ambient _ _ _).mp
    (PassiveHolders.staged_preserves pid (passiveView w)) w a () v b rfl run
  obtain ⟨delta,step,funded⟩ := hi.transfer transfer keys passive
  refine ⟨delta,step,funded,?_⟩
  apply stable.retains
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (RxRing.sendStagedPackets_cell pid) w a () v b run
  · exact step.rx
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (sendStagedPackets_rxQueues pid) w a () v b run
  · exact (hoare_iff_run_ambient _ _ _).mp
      (NapiFrames.staged_preserves pid (NapiFrames.napiView w)) w a () v b (NapiFrames.refl w) run

theorem staged_boundary (pid : PeerId) : Preserves (Boundary cs loans) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  obtain ⟨h,funded,stable⟩ := hi
  obtain ⟨delta,_,post,stable⟩ := staged_funded pid funded stable a b run
  exact ⟨h.absorb delta,post,stable⟩

theorem queued_boundary (pid : PeerId) (retry : Bool) :
    Preserves (Boundary cs loans) (sendQueuedHandshakeInitiation pid retry) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  obtain ⟨h,funded,stable⟩ := hi
  obtain ⟨delta,_,post,stable⟩ := sendQueued_funded pid retry funded stable a b run
  exact ⟨h.absorb delta,post,stable⟩

private theorem read_boundary (pid : PeerId) : Preserves (Boundary cs loans) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  exact (getPeer_normal pid w v p a b run).1 ▸ hi

private theorem modify_boundary (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Preserves (Boundary cs loans) (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨h,funded,stable⟩ := hi
  have keep : Preserves (fun w => h.Funded cs loans w ∧ StableRx cs w)
      (do let p ← getPeer pid; setPeer pid (f p)) := (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.modify_peer)
    pid f stamp count rx napi current tx
  exact ⟨h,(hoare_iff_run_ambient _ _ _).mp keep w a x v b ⟨funded,stable⟩ run⟩

private theorem source_modify (hi : Boundary cs loans w) (hd : w.dev=some d)
    (hp : d.peers[pid]?=some p) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all) (a b : Ambient)
    (run : ((setPeer pid (f p)).run w).run a=.ok ((x,v),b)) : Boundary cs loans v := by
  apply (hoare_iff_run_ambient _ _ _).mp
    (modify_boundary pid f stamp count rx napi current tx) w a x v b hi
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨p,w,a,by simp [getPeer,getDev,hd,hp],run⟩

private theorem ambient_state (action : AmbientM α) (a b : Ambient)
    (run : (((monadLift action : WG.M α)).run w).run a=.ok ((x,v),b)) : v=w :=
  (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient action (· = w)) w a x v b rfl run

/-- The keepalive allocates/stages only in its actual empty branch, then
uses the concrete staged-send delta. No queue readiness premise is needed. -/
theorem keepalive_boundary (pid : PeerId) : Preserves (Boundary cs loans) (sendKeepalive pid) := by
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

private theorem frame_boundary (action : WG.M α)
    (frame : ∀ initial, Preserves (Frame initial) action)
    (keeps : ∀ cs loans, Preserves (ClearWork.Inv cs loans) action) :
    Preserves (Boundary cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨h,funded,stable⟩ := hi
  have rule : Preserves (fun w => h.Funded cs loans w ∧ StableRx cs w) action :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.fixed_rule)
      action frame keeps
  exact ⟨h,(hoare_iff_run_ambient _ _ _).mp rule w a x v b ⟨funded,stable⟩ run⟩

private theorem control_keeps {action : WG.M α}
    (same : SameView (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view) action) :
    Preserves (ClearWork.Inv cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  have eq := (ProjectedAction.iff_run_ambient _ _ _).mp same w a x v b run
  refine ⟨hi.1.view ?_,hi.2.view ?_⟩
  · exact ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) v).trans
      ((congrArg (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrierOf) eq).trans
        ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) w).symm)
  · exact ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.stable_factor) v).trans
      ((congrArg (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.stableOf) eq).trans
        ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.stable_factor) w).symm)

theorem modTimer_boundary (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (Boundary cs loans) (modPeerTimer site pid timer delay) :=
  frame_boundary _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.mod_preserves) site pid timer delay)
    (fun _ _ => control_keeps
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.modPeerTimer_view) site pid timer delay))

theorem delTimer_boundary (pid : PeerId) (timer : PeerTimer) :
    Preserves (Boundary cs loans) (delTimer pid timer) :=
  frame_boundary _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.del_preserves) pid timer)
    (fun _ _ => control_keeps
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.delTimer_view) pid timer))

private theorem endpoint_boundary (pid : PeerId) :
    Preserves (Boundary cs loans) (clearPeerEndpointSrc pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨h,funded,stable⟩ := hi
  exact ⟨h,(hoare_iff_run_ambient _ _ _).mp (clearEndpoint_preserves pid) w a x v b ⟨funded,stable⟩ run⟩

/-- Purging staged bytes pays no durable batch: the staged list is uncharged.
The actual saved-peer setter and dropped-byte accounting remain in order. -/
theorem purge_boundary (pid : PeerId) : Preserves (Boundary cs loans) (purgeStagedPackets pid) := by
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
  have kept := HolderEncrypt.boundary_fields hi fields
  exact source_modify (d := {d with txDropped := d.txDropped+p.staged.length}) kept
    (by simp [hd]) hp (fun p => {p with staged := []})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => h) (fun _ => rfl) a b run

/-- The retransmit callback follows its actual give-up, re-arm and queued
handshake paths; the latter retains the source-acquired work reservation. -/
theorem retransmit_boundary (pid : PeerId) :
    Preserves (Boundary cs loans) (expiredRetransmitHandshake pid) := by
  have attempts := modify_boundary (cs := cs) (loans := loans) pid
    (fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts+1})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => h) (fun _ => rfl)
  unfold expiredRetransmitHandshake
  apply preserves_bind (read_boundary pid)
  intro p
  apply preserves_bind (hoare_liftAmbient (AmbientM.branchCmp .retransmitGiveUp
    (p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES) p.timerHandshakeAttempts MAX_TIMER_HANDSHAKES) (Boundary cs loans))
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
      (!p.timerPending .zeroKeyMaterial)) (Boundary cs loans))
    intro pending
    cases pending with
    | false => exact preserves_pure _
    | true =>
      apply discard_view_spec id (Boundary cs loans)
      exact modTimer_boundary .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS

/-- The keepalive callback includes its real optional timer re-arm. -/
theorem keepaliveTimer_boundary (pid : PeerId) :
    Preserves (Boundary cs loans) (expiredSendKeepalive pid) := by
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
    (Boundary cs loans))
  intro another
  cases another with
  | false => exact preserves_pure _
  | true =>
    rw [←bind_assoc]
    apply preserves_bind clear
    intro _
    apply discard_view_spec id (Boundary cs loans)
    exact modTimer_boundary .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS

theorem persistent_boundary (pid : PeerId) :
    Preserves (Boundary cs loans) (expiredSendPersistentKeepalive pid) := by
  unfold expiredSendPersistentKeepalive
  apply preserves_bind (read_boundary pid)
  intro p
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .persistentKeepaliveInterval
    (p.persistentKeepaliveInterval != 0)) (Boundary cs loans))
  intro enabled
  cases enabled
  · exact preserves_pure _
  · exact keepalive_boundary pid

theorem zero_boundary (pid : PeerId) :
    Preserves (Boundary cs loans) (expiredZeroKeyMaterial pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  obtain ⟨h,funded,stable⟩ := hi
  obtain ⟨added,_,post,stable⟩ := expiredZero_funded pid funded stable a b run
  exact ⟨addClear h added,post,stable⟩

theorem newHandshake_boundary (pid : PeerId) :
    Preserves (Boundary cs loans) (expiredNewHandshake pid) := by
  unfold expiredNewHandshake
  exact preserves_bind (endpoint_boundary pid) (fun _ => queued_boundary pid false)

/-- All five actual callbacks preserve a complete aligned funded account.
New work/batches remain charged; control writes retain existing obligations.
This contract is normal-return preservation, not timer-dispatch totality. -/
theorem callback_boundary (pid : PeerId) (timer : PeerTimer) :
    Preserves (Boundary cs loans) (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact retransmit_boundary pid
  | sendKeepalive => exact keepaliveTimer_boundary pid
  | newHandshake => exact newHandshake_boundary pid
  | zeroKeyMaterial => exact zero_boundary pid
  | persistentKeepalive => exact persistent_boundary pid

/-- The product lift runs the same WG/Ambient callback with the complete
account; unrelated product components need no additional premise. -/
theorem callback_product (pid : PeerId) (timer : PeerTimer) :
    Preserves (fun w : World => Boundary cs loans w.wg) (liftWG (timerCallback pid timer)) :=
  HolderEncrypt.lift_boundary (callback_boundary pid timer)

/-- The original lifetime observer has exactly the same normal endpoint,
with arbitrary incoming history and the callback's actual Ambient cuts. -/
theorem callback_observed (pid : PeerId) (timer : PeerTimer)
    (hi : Boundary cs loans w) (history : List LifetimeEvent) (a b : Ambient)
    (run : (runStatePrefix (timerCallbackPrefix pid timer) w a history).1 = .ok ((result,v),b)) :
    Boundary cs loans v :=
  (hoare_iff_run_ambient _ _ _).mp (callback_boundary pid timer) w a result v b hi
    ((timerCallbackPrefix_erases pid timer w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.HolderTimers
