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
    SameView (fun w : World => snapshot w.wg) (Env.requireDrained what queues) :=
  productStoreSnapshot (Framing.requireDrained_sameKernel what queues)

theorem requireDrained_spec (P : Snapshot → Prop) (what : String) (queues : List Bool) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.requireDrained what queues
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (requireDrained_sameSnapshot what queues).wp P

theorem runOneSendWorker_sameSnapshot  : SameView (fun w : World => snapshot w.wg) Env.runOneSendWorker := by
  have ambient {α : Type} (a : AmbientM α) :
      SameView (fun w : World => snapshot w.wg) (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a
      (fun w => snapshot w.wg = initial) (fun _ _ h => h)
  have device : SameView (fun w : World => snapshot w.wg) (monadLift getDev : Leanux.M Device) := nativeSnapshot getDev_sameSnapshot
  have peer (pid : PeerId) : SameView (fun w : World => snapshot w.wg) (monadLift (getPeer pid) : Leanux.M Peer) := nativeSnapshot (getPeer_sameSnapshot pid)
  have writePeer (pid : PeerId) (p : Peer) : SameView (fun w : World => snapshot w.wg) (monadLift (setPeer pid p) : Leanux.M Unit) := nativeSnapshot (setPeer_sameSnapshot pid p)
  have edit (pid : PeerId) : SameView (fun w : World => snapshot w.wg)
      (monadLift (modifyDev fun d => { d with sendWorkQueue := d.sendWorkQueue.erase pid }) : Leanux.M Unit) := by
    apply nativeSnapshot
    exact fun initial => modifyDev_snapshot_spec (fun s => s = initial) _ (fun _ => rfl)
  have worker (pid : PeerId) : SameView (fun w : World => snapshot w.wg)
      (Env.runWorker .sendWorker (liftM (handshakeSendWorker pid))) :=
    runWorker_sameSnapshot .sendWorker _ (nativeSnapshot (handshakeSendWorker_sameSnapshot pid))
  env_operation_source [Env.runOneSendWorker, peekUnit, resolveUnit, invariant]
    using [device, peer, writePeer, edit, worker, ambient]

theorem runOneSendWorker_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.runOneSendWorker
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (runOneSendWorker_sameSnapshot ).wp P

theorem timerCallback_ordinary (pid : PeerId) (timer : PeerTimer) : OrdinaryAction (WG.timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact SameView.ordinary (expiredRetransmitHandshake_sameSnapshot pid)
  | sendKeepalive => exact expiredSendKeepalive_ordinary pid
  | newHandshake => exact SameView.ordinary (expiredNewHandshake_sameSnapshot pid)
  | zeroKeyMaterial => exact SameView.ordinary (expiredZeroKeyMaterial_sameSnapshot pid)
  | persistentKeepalive => exact expiredSendPersistentKeepalive_ordinary pid

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
  have ambient {α : Type} (a : AmbientM α) :
      ProductOrdinaryAction (monadLift a : Leanux.M α) :=
    SameView.ordinary (fun initial => productAmbient_spec a
      (fun w => snapshot w.wg = initial) (fun _ _ h => h))
  have device : ProductOrdinaryAction (monadLift getDev : Leanux.M Device) :=
    SameView.ordinary (nativeSnapshot getDev_sameSnapshot)
  have edit (pid : PeerId) : ProductOrdinaryAction
      (monadLift (modifyDev fun d => { d with clearWorkQueue := d.clearWorkQueue.erase pid }) : Leanux.M Unit) := by
    apply SameView.ordinary
    apply nativeSnapshot
    exact fun initial => modifyDev_snapshot_spec (fun s => s = initial) _ (fun _ => rfl)
  have worker (pid : PeerId) : ProductOrdinaryAction
      (Env.runWorker .clearPeerWorker (liftM (queuedExpiredZeroKeyMaterial pid))) :=
    runWorker_ordinary .clearPeerWorker _
      (OrdinaryAction.liftWG (queuedExpiredZeroKeyMaterial_ordinary pid))
  unfold ProductOrdinaryAction
  unfold Env.runOneClearWorker
  repeat' first
    | (unfold ProductOrdinaryAction)
    | env_operation_fact device
    | env_operation_fact edit
    | env_operation_fact worker
    | env_operation_fact ambient
    | (ordinary_head Leanux.invariant; exact ambient _)
    | (ordinary_head Leanux.unsupported; exact ambient _)
    | (ordinary_head Leanux.peekUnit; exact ambient _)
    | (ordinary_head Leanux.resolveUnit; exact ambient _)
    | (ordinary_head liftM; unfold liftM)
    | env_product_join_let
    | env_product_join_use
    | keypairs_intro_forall
    | (ordinary_head Pure.pure; exact SameView.ordinary (SameView.pure _ _))
    | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
    | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
    | (ordinary_head ForIn.forIn; apply ordinary_forIn)
    | (ordinary_head Functor.discard; apply ordinary_discard)
    | ordinary_head_reduce
    | ordinary_head_match

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
  have ambient {α : Type} (a : AmbientM α) :
      SameView (fun w : World => snapshot w.wg) (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a
      (fun w => snapshot w.wg = initial) (fun _ _ h => h)
  have device : SameView (fun w : World => snapshot w.wg) (monadLift getDev : Leanux.M Device) := nativeSnapshot getDev_sameSnapshot
  env_operation_source [Env.requireIdleDevice, unsupported]
    using [requireNoCryptWork_sameSnapshot, device, ambient]

theorem requireIdleDevice_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.requireIdleDevice
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (requireIdleDevice_sameSnapshot ).wp P

theorem wgUp_ordinary  : ProductOrdinaryAction Env.wgUp := by
  have ambient {α : Type} (a : AmbientM α) :
      ProductOrdinaryAction (monadLift a : Leanux.M α) :=
    SameView.ordinary (fun initial => productAmbient_spec a
      (fun w => snapshot w.wg = initial) (fun _ _ h => h))
  have routing {α : Type} (a : Net.M α) : ProductOrdinaryAction
      (monadLift a : Leanux.M α) :=
    SameView.ordinary (productStoreSnapshot
      (liftWG_sameProductStore _ (liftRouting_sameWGStore a)))
  have edit (f : EnvWorld → EnvWorld) : ProductOrdinaryAction (modifyEnv f) := by
    apply (Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    exact .refl _
  have read := SameView.ordinary productGetSnapshot
  have up : ProductOrdinaryAction (monadLift WG.wgUp : Leanux.M Int) := OrdinaryAction.liftWG WGDevice.wgUp_ordinary
  unfold ProductOrdinaryAction
  unfold Env.wgUp
  repeat' first
    | (unfold ProductOrdinaryAction)
    | env_operation_fact up
    | env_operation_fact read
    | env_operation_fact routing
    | env_operation_fact edit
    | (ordinary_head Leanux.skipCut; unfold Leanux.skipCut)
    | env_operation_fact ambient
    | (ordinary_head Leanux.invariant; exact ambient _)
    | (ordinary_head Leanux.unsupported; exact ambient _)
    | (ordinary_head Leanux.peekUnit; exact ambient _)
    | (ordinary_head Leanux.resolveUnit; exact ambient _)
    | (ordinary_head liftM; unfold liftM)
    | env_product_join_let
    | env_product_join_use
    | keypairs_intro_forall
    | (ordinary_head Pure.pure; exact SameView.ordinary (SameView.pure _ _))
    | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
    | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
    | (ordinary_head ForIn.forIn; apply ordinary_forIn)
    | (ordinary_head Functor.discard; apply ordinary_discard)
    | ordinary_head_reduce
    | ordinary_head_match

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
  have ambient {α : Type} (a : AmbientM α) :
      ProductOrdinaryAction (monadLift a : Leanux.M α) :=
    SameView.ordinary (fun initial => productAmbient_spec a
      (fun w => snapshot w.wg = initial) (fun _ _ h => h))
  have routing {α : Type} (a : Net.M α) : ProductOrdinaryAction
      (monadLift a : Leanux.M α) :=
    SameView.ordinary (productStoreSnapshot
      (liftWG_sameProductStore _ (liftRouting_sameWGStore a)))
  have read := SameView.ordinary productGetSnapshot
  have down : ProductOrdinaryAction (monadLift WG.wgDown : Leanux.M Unit) := OrdinaryAction.liftWG WGDevice.wgDown_ordinary
  have idle := SameView.ordinary requireIdleDevice_sameSnapshot
  unfold ProductOrdinaryAction
  unfold Env.wgDown modifyRouting
  repeat' first
    | (unfold ProductOrdinaryAction)
    | env_operation_fact down
    | env_operation_fact read
    | env_operation_fact idle
    | env_operation_fact routing
    | (ordinary_head Leanux.skipCut; unfold Leanux.skipCut)
    | env_operation_fact ambient
    | (ordinary_head Leanux.invariant; exact ambient _)
    | (ordinary_head Leanux.unsupported; exact ambient _)
    | (ordinary_head Leanux.peekUnit; exact ambient _)
    | (ordinary_head Leanux.resolveUnit; exact ambient _)
    | (ordinary_head liftM; unfold liftM)
    | env_product_join_let
    | env_product_join_use
    | keypairs_intro_forall
    | (ordinary_head Pure.pure; exact SameView.ordinary (SameView.pure _ _))
    | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
    | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
    | (ordinary_head ForIn.forIn; apply ordinary_forIn)
    | (ordinary_head Functor.discard; apply ordinary_discard)
    | ordinary_head_reduce
    | ordinary_head_match

theorem wgDown_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ Env.wgDown
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (wgDown_ordinary ).wp P hp

theorem wgDelete_ordinary  : ProductOrdinaryAction Env.wgDelete := by
  have ambient {α : Type} (a : AmbientM α) :
      ProductOrdinaryAction (monadLift a : Leanux.M α) :=
    SameView.ordinary (fun initial => productAmbient_spec a
      (fun w => snapshot w.wg = initial) (fun _ _ h => h))
  have routing {α : Type} (a : Net.M α) : ProductOrdinaryAction
      (monadLift a : Leanux.M α) :=
    SameView.ordinary (productStoreSnapshot
      (liftWG_sameProductStore _ (liftRouting_sameWGStore a)))
  have read := SameView.ordinary productGetSnapshot
  have device : ProductOrdinaryAction (monadLift getDev : Leanux.M Device) := SameView.ordinary (nativeSnapshot getDev_sameSnapshot)
  have slept : ProductOrdinaryAction (monadLift mayHaveSlept : Leanux.M Unit) := SameView.ordinary (nativeSnapshot mayHaveSlept_sameSnapshot)
  have down : ProductOrdinaryAction (monadLift WG.wgDown : Leanux.M Unit) := OrdinaryAction.liftWG WGDevice.wgDown_ordinary
  have destruct : ProductOrdinaryAction (monadLift WG.wgDestruct : Leanux.M Unit) := OrdinaryAction.liftWG WGDevice.wgDestruct_ordinary
  have idle := SameView.ordinary requireIdleDevice_sameSnapshot
  have destroy : ProductOrdinaryAction Env.inetdevDestroy := by
    unfold ProductOrdinaryAction
    unfold Env.inetdevDestroy getRouting modifyRouting
    repeat' first
      | (unfold ProductOrdinaryAction)
      | env_operation_fact routing
      | (ordinary_head ForIn.forIn; apply ordinary_forIn)
      | env_operation_fact ambient
      | (ordinary_head Leanux.invariant; exact ambient _)
      | (ordinary_head Leanux.unsupported; exact ambient _)
      | (ordinary_head Leanux.peekUnit; exact ambient _)
      | (ordinary_head Leanux.resolveUnit; exact ambient _)
      | (ordinary_head liftM; unfold liftM)
      | env_product_join_let
      | env_product_join_use
      | keypairs_intro_forall
      | (ordinary_head Pure.pure; exact SameView.ordinary (SameView.pure _ _))
      | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
      | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
      | (ordinary_head ForIn.forIn; apply ordinary_forIn)
      | (ordinary_head Functor.discard; apply ordinary_discard)
      | ordinary_head_reduce
      | ordinary_head_match
  unfold ProductOrdinaryAction
  unfold Env.wgDelete WG.wgDelete modifyRouting
  repeat' first
    | (unfold ProductOrdinaryAction)
    | env_operation_fact destroy
    | env_operation_fact down
    | env_operation_fact destruct
    | env_operation_fact slept
    | env_operation_fact device
    | env_operation_fact read
    | env_operation_fact idle
    | env_operation_fact routing
    | (ordinary_head Leanux.skipCut; unfold Leanux.skipCut)
    | env_operation_fact ambient
    | (ordinary_head Leanux.invariant; exact ambient _)
    | (ordinary_head Leanux.unsupported; exact ambient _)
    | (ordinary_head Leanux.peekUnit; exact ambient _)
    | (ordinary_head Leanux.resolveUnit; exact ambient _)
    | (ordinary_head liftM; unfold liftM)
    | env_product_join_let
    | env_product_join_use
    | keypairs_intro_forall
    | (ordinary_head Pure.pure; exact SameView.ordinary (SameView.pure _ _))
    | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
    | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
    | (ordinary_head ForIn.forIn; apply ordinary_forIn)
    | (ordinary_head Functor.discard; apply ordinary_discard)
    | ordinary_head_reduce
    | ordinary_head_match

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
  have ambient {α : Type} (a : AmbientM α) :
      SameView (fun w : World => snapshot w.wg) (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a
      (fun w => snapshot w.wg = initial) (fun _ _ h => h)
  have routing {α : Type} (a : Net.M α) : SameView (fun w : World => snapshot w.wg)
      (monadLift a : Leanux.M α) :=
    productStoreSnapshot (liftWG_sameProductStore _ (liftRouting_sameWGStore a))
  have netns : SameView (fun w : World => snapshot w.wg) (monadLift netnsPreExit : Leanux.M Unit) := nativeSnapshot netnsPreExit_sameSnapshot
  have edit (f : EnvWorld → EnvWorld) : SameView (fun w : World => snapshot w.wg) (modifyEnv f) := by
    apply (Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    rfl
  env_operation_source [Env.netnsCleanup, getRouting, peekUnit, resolveUnit, skipCut, unsupported]
    using [runWorker_sameSnapshot, netns, routing, edit, ambient]

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
  have ambient {α : Type} (a : AmbientM α) :
      SameView (fun w : World => snapshot w.wg) (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a
      (fun w => snapshot w.wg = initial) (fun _ _ h => h)
  have loopback : SameView (fun w : World => snapshot w.wg) (monadLift (loopbackSend [] true) : Leanux.M Unit) := nativeSnapshot (loopbackSend_sameSnapshot [] true)
  env_operation_source [Env.xmitMulticastLoop, unsupported] using [loopback, ambient]

theorem xmitMulticastLoop_spec (P : Snapshot → Prop) (family addr : Nat) :
    ⦃fun w => ⌜P (snapshot w.wg)⌝⦄ (Env.xmitMulticastLoop family addr)
    ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := (xmitMulticastLoop_sameSnapshot family addr).wp P

end Leanux.Proofs.WG.Keypairs.EnvFrames
