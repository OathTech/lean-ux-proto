import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Keypairs.Frames.EnvWorkers
import Leanux.Proofs.WG.Keypairs.SnapshotRules

/-! Ordinary framing of nonreceive environment work, timers, lifecycle calls
and the fixture's packet construction. -/
namespace Leanux.Proofs.WG.Keypairs.EnvFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open Leanux.Proofs.Framing
open WGFrames WGTransitions WGMore WGConfig WGDevice
open Observers SchedulerObservers

set_option maxHeartbeats 400000
set_option pp.structureInstances false


private theorem productStoreSnapshot {a : Leanux.M α} (h : SameProductStore a) :
    SameView (fun w : World => snapshot w.wg) a :=
  h.of_factor
    (fun s : ProductStore43 => snapshotOfWGStoreView s.2.2.2)
    (fun w => snapshot w.wg) (fun _ => rfl)

private theorem nativeSnapshot {a : WG.M α} (h : SameSnapshot a) :
    SameView (fun w : World => snapshot w.wg) (MonadLift.monadLift a : Leanux.M α) :=
  sameView_liftWG (fun w => snapshot w.wg) snapshot a h (fun _ _ _ h => h)

private theorem productGetSnapshot : SameView (fun w : World => snapshot w.wg) (getWG : Leanux.M WGWorld) :=
  productStoreSnapshot (by intro initial; exact productGetWG_spec (fun s => s = initial))

theorem requireNoCryptWork_sameSnapshot  : SameView (fun w : World => snapshot w.wg) Env.requireNoCryptWork :=
  productStoreSnapshot (Framing.requireNoCryptWork_sameKernel)

theorem requireNoCryptWork_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.requireNoCryptWork
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (requireNoCryptWork_sameSnapshot ).wp P

theorem requireDrained_sameSnapshot (what : String) (queues : List Bool) :
    SameView (fun w : World => snapshot w.wg) (Env.requireDrained what queues) := by
  apply SameView.of_wp
  intro initial
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => snapshot w.wg = initial) (fun _ _ h => h)
  unfold Hoare at ha
  have hd := (nativeSnapshot getDev_sameSnapshot).wp (fun s => s = initial)
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.requireDrained, hd, ha, unsupported, invariant]

theorem requireDrained_spec (P : Snapshot → Prop) (what : String) (queues : List Bool) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.requireDrained what queues
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (requireDrained_sameSnapshot what queues).wp P

theorem runOneSendWorker_sameSnapshot  : SameView (fun w : World => snapshot w.wg) Env.runOneSendWorker := by
  apply SameView.of_wp
  intro initial
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => snapshot w.wg = initial) (fun _ _ h => h)
  unfold Hoare at ha
  have hd := (nativeSnapshot getDev_sameSnapshot).wp (fun s => s = initial)
  have hg := fun pid => (nativeSnapshot (getPeer_sameSnapshot pid)).wp (fun s => s = initial)
  have hs := fun pid p => (nativeSnapshot (setPeer_sameSnapshot pid p)).wp (fun s => s = initial)
  have hm (pid : PeerId) : SameView (fun w : World => snapshot w.wg)
      (MonadLift.monadLift (modifyDev fun d => { d with sendWorkQueue := d.sendWorkQueue.erase pid }) : Leanux.M Unit) := by
    apply nativeSnapshot
    intro k
    exact modifyDev_snapshot_spec (fun s => s = k) _ (fun _ => rfl)
  have hmSpec := fun pid => (hm pid).wp (fun s => s = initial)
  have hw := fun pid => (runWorker_sameSnapshot .sendWorker _
    (nativeSnapshot (handshakeSendWorker_sameSnapshot pid))).wp (fun s => s = initial)
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.runOneSendWorker, hd, hg, hs, hmSpec, hw,
    peekUnit, resolveUnit, ha, invariant]

theorem runOneSendWorker_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.runOneSendWorker
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (runOneSendWorker_sameSnapshot ).wp P

theorem timerCallback_ordinary (pid : PeerId) (timer : PeerTimer) : OrdinaryAction (WG.timerCallback pid timer) := by
  frame_ordinary [WG.timerCallback] using [expiredRetransmitHandshake_spec, expiredNewHandshake_spec, expiredZeroKeyMaterial_spec] ordinary [expiredSendKeepalive_spec, expiredSendPersistentKeepalive_spec]

theorem timerCallback_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) (timer : PeerTimer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (WG.timerCallback pid timer)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timerCallback_ordinary pid timer).wp P hp

theorem runTimerSection_ordinary (worker : Worker) (body : Leanux.M Unit)
    (hb : ProductOrdinaryAction body) : ProductOrdinaryAction (Env.runTimerSection worker body) := by
  unfold Env.runTimerSection
  repeat' env_worker_step

theorem runTimerSection_spec (P : Snapshot → Prop) (hp : Stable P)
    (worker : Worker) (body : Leanux.M Unit) (hb : ProductOrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.runTimerSection worker body
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (runTimerSection_ordinary worker body hb).wp P hp

theorem runOneClearWorker_ordinary  : ProductOrdinaryAction Env.runOneClearWorker := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => P (snapshot w.wg)) (fun _ _ h => h)
  have hd := (nativeSnapshot getDev_sameSnapshot).wp P
  have hm (pid : PeerId) : SameView (fun w : World => snapshot w.wg)
      (MonadLift.monadLift (modifyDev fun d => { d with clearWorkQueue := d.clearWorkQueue.erase pid }) : Leanux.M Unit) := by
    apply nativeSnapshot
    intro initial
    exact modifyDev_snapshot_spec (fun s => s = initial) _ (fun _ => rfl)
  have hmSpec := fun pid => (hm pid).wp P
  have hw (pid : PeerId) :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        Env.runWorker .clearPeerWorker (MonadLift.monadLift (queuedExpiredZeroKeyMaterial pid) : Leanux.M Unit)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    Lifetimes.ProjectedAction.wp (runWorker_ordinary .clearPeerWorker _
      (OrdinaryAction.liftWG (queuedExpiredZeroKeyMaterial_ordinary pid))) P hp
  unfold Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.runOneClearWorker, hd, hmSpec, hw,
    peekUnit, resolveUnit, ha, invariant]

theorem runOneClearWorker_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.runOneClearWorker
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (runOneClearWorker_ordinary ).wp P hp

theorem timerWorker_sameSnapshot (timer : PeerTimer) : SameView (fun w : World => snapshot w.wg) (Env.timerWorker timer) :=
  productStoreSnapshot (Framing.timerWorker_sameKernel timer)

theorem timerWorker_spec (P : Snapshot → Prop) (timer : PeerTimer) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Env.timerWorker timer)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (timerWorker_sameSnapshot timer).wp P

theorem advance_sameSnapshot (ticks : Nat) : SameView (fun w : World => snapshot w.wg) (Env.advance ticks) :=
  productStoreSnapshot (Framing.advance_sameKernel ticks)

theorem advance_spec (P : Snapshot → Prop) (ticks : Nat) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Env.advance ticks)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (advance_sameSnapshot ticks).wp P

theorem requireIdleDevice_sameSnapshot  : SameView (fun w : World => snapshot w.wg) Env.requireIdleDevice := by
  apply SameView.of_wp
  intro initial
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => snapshot w.wg = initial) (fun _ _ h => h)
  unfold Hoare at ha
  have hd := (nativeSnapshot getDev_sameSnapshot).wp (fun s => s = initial)
  have hn := requireNoCryptWork_spec (fun s => s = initial)
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.requireIdleDevice, hn, hd, ha, unsupported]

theorem requireIdleDevice_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.requireIdleDevice
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (requireIdleDevice_sameSnapshot ).wp P

theorem wgUp_ordinary  : ProductOrdinaryAction Env.wgUp := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => P (snapshot w.wg)) (fun _ _ h => h)
  have hg := productGetSnapshot.wp P
  have hr := fun α (a : Net.M α) => productRouting_spec a
    (fun s => P (snapshotOfWGStoreView s.2.2.2))
  unfold Hoare at ha hr
  have hu :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄ (MonadLift.monadLift WG.wgUp : Leanux.M Int)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    Lifetimes.ProjectedAction.wp (OrdinaryAction.liftWG WGDevice.wgUp_ordinary) P hp
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.wgUp, hg, hu, hr, ha, skipCut, modifyEnv]

theorem wgUp_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.wgUp
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (wgUp_ordinary ).wp P hp

theorem setMtu_sameSnapshot (mtu : Nat) : SameView (fun w : World => snapshot w.wg) (Env.setMtu mtu) := by
  apply (Framing.setMtu_sameEnvScalar mtu).of_factor
    (fun s : ProductStore43 => snapshotOfWGStoreView s.2.2.2)
    (fun w => snapshot w.wg)
  intro w
  simp [envScalarView, envScalarStore, productStoreView, snapshotOfWGStoreView,
    wgStoreView, envScalarDevice, snapshot, Option.bind_map, Function.comp_def]

theorem setMtu_spec (P : Snapshot → Prop) (mtu : Nat) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Env.setMtu mtu)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (setMtu_sameSnapshot mtu).wp P

theorem routeIntoWg0_sameSnapshot  : SameView (fun w : World => snapshot w.wg) Env.routeIntoWg0 :=
  productStoreSnapshot (Framing.routeIntoWg0_sameKernel)

theorem routeIntoWg0_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.routeIntoWg0
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (routeIntoWg0_sameSnapshot ).wp P

theorem wgDown_ordinary  : ProductOrdinaryAction Env.wgDown := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => P (snapshot w.wg)) (fun _ _ h => h)
  have hg := productGetSnapshot.wp P
  have hr := fun α (a : Net.M α) => productRouting_spec a
    (fun s => P (snapshotOfWGStoreView s.2.2.2))
  unfold Hoare at ha hr
  have hd :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄ (MonadLift.monadLift WG.wgDown : Leanux.M Unit)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    Lifetimes.ProjectedAction.wp (OrdinaryAction.liftWG WGDevice.wgDown_ordinary) P hp
  have hi := requireIdleDevice_spec P
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.wgDown, hg, hd, hi, hr, ha, skipCut, modifyRouting]

theorem wgDown_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.wgDown
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (wgDown_ordinary ).wp P hp

theorem wgDelete_ordinary  : ProductOrdinaryAction Env.wgDelete := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => P (snapshot w.wg)) (fun _ _ h => h)
  have hg := productGetSnapshot.wp P
  have hr := fun α (a : Net.M α) => productRouting_spec a
    (fun s => P (snapshotOfWGStoreView s.2.2.2))
  unfold Hoare at ha hr
  have hd := (nativeSnapshot getDev_sameSnapshot).wp P
  have hs := (nativeSnapshot mayHaveSlept_sameSnapshot).wp P
  have hdown :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄ (MonadLift.monadLift WG.wgDown : Leanux.M Unit)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    Lifetimes.ProjectedAction.wp (OrdinaryAction.liftWG WGDevice.wgDown_ordinary) P hp
  have hdestruct :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄ (MonadLift.monadLift WG.wgDestruct : Leanux.M Unit)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ :=
    Lifetimes.ProjectedAction.wp (OrdinaryAction.liftWG WGDevice.wgDestruct_ordinary) P hp
  have hi := requireIdleDevice_spec P
  have hl (α β : Type) := list_view_spec (m := Except Stop) (fun w : World => snapshot w.wg)
    (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT,
    Env.wgDelete, WG.wgDelete, Env.inetdevDestroy, getRouting, modifyRouting, hg, hd, hs,
    hdown, hdestruct, hi, hr, ha, hl, skipCut, unsupported]

theorem wgDelete_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.wgDelete
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (wgDelete_ordinary ).wp P hp

theorem wgDeladdr_sameSnapshot (family : Nat) : SameView (fun w : World => snapshot w.wg) (Env.wgDeladdr family) :=
  productStoreSnapshot (Framing.wgDeladdr_sameKernel family)

theorem wgDeladdr_spec (P : Snapshot → Prop) (family : Nat) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Env.wgDeladdr family)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (wgDeladdr_sameSnapshot family).wp P

theorem wgDelroute_sameSnapshot (family : Nat) : SameView (fun w : World => snapshot w.wg) (Env.wgDelroute family false 0 0 0 0 0) :=
  productStoreSnapshot (Framing.wgDelroute_sameKernel family)

theorem wgDelroute_spec (P : Snapshot → Prop) (family : Nat) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Env.wgDelroute family false 0 0 0 0 0)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (wgDelroute_sameSnapshot family).wp P

theorem netnsCleanup_sameSnapshot  : SameView (fun w : World => snapshot w.wg) Env.netnsCleanup := by
  apply SameView.of_wp
  intro initial
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => snapshot w.wg = initial) (fun _ _ h => h)
  unfold Hoare at ha
  have hr := fun α (a : Net.M α) => productRouting_spec a
    (fun s => snapshotOfWGStoreView s.2.2.2 = initial)
  have hn := (nativeSnapshot netnsPreExit_sameSnapshot).wp (fun s => s = initial)
  unfold Hoare at hr
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.netnsCleanup, Env.runWorker,
    getRouting, modifyEnv, hn, hr, ha, peekUnit, resolveUnit, hidden, peekHiddenSite, skipCut, invariant, unsupported]

theorem netnsCleanup_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.netnsCleanup
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (netnsCleanup_sameSnapshot ).wp P

theorem xmitPacket_sameSnapshot (family addr : Nat) (payload : List UInt8) (mtu tos : Nat) : SameView (fun w : World => snapshot w.wg) (Env.xmitPacket family addr payload mtu tos) :=
  productStoreSnapshot (Framing.xmitPacket_sameKernel family addr payload mtu tos)

theorem xmitPacket_spec (P : Snapshot → Prop) (family addr : Nat) (payload : List UInt8) (mtu tos : Nat) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Env.xmitPacket family addr payload mtu tos)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (xmitPacket_sameSnapshot family addr payload mtu tos).wp P

theorem xmitPackets_sameSnapshot (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) : SameView (fun w : World => snapshot w.wg) (Env.xmitPackets family addr payload opts) :=
  productStoreSnapshot (Framing.xmitPackets_sameKernel family addr payload opts)

theorem xmitPackets_spec (P : Snapshot → Prop) (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Env.xmitPackets family addr payload opts)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (xmitPackets_sameSnapshot family addr payload opts).wp P

theorem xmitMulticastLoop_sameSnapshot (family addr : Nat) : SameView (fun w : World => snapshot w.wg) (Env.xmitMulticastLoop family addr) := by
  apply SameView.of_wp
  intro initial
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => snapshot w.wg = initial) (fun _ _ h => h)
  unfold Hoare at ha
  have hl := (nativeSnapshot (loopbackSend_sameSnapshot [] true)).wp (fun s => s = initial)
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.xmitMulticastLoop, hl, ha, unsupported]

theorem xmitMulticastLoop_spec (P : Snapshot → Prop) (family addr : Nat) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Env.xmitMulticastLoop family addr)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (xmitMulticastLoop_sameSnapshot family addr).wp P

end Leanux.Proofs.WG.Keypairs.EnvFrames
