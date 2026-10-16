import Leanux.Proofs.WG.AllowedIps.RoutingEnvTimersFrames
import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Environment.BatchSource

/-! Original environment ingress, exact flood and batch submission retain
routing at normal endpoints. Concrete nested scheduling closes the full receive
worker. Saved device scalars and lists need no current-device equality premise;
all actual getters, record failures and finite exhaustion remain unchanged. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem wgKernel_routing (a : Leanux.M α) (ha : SameView (fun w : World => wgStoreView w.wg) a) :
    SameView (fun w : World => routingView w.wg) a :=
  ha.of_factor (fun k : WGStoreView => k.dev.map routingState) (fun w : World => routingView w.wg) (fun _ => rfl)

private theorem product_store_routing (a : Leanux.M α) (ha : SameProductStore a) :
    SameView (fun w : World => routingView w.wg) a :=
  ha.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)

private theorem workerLoop_routing (worker : Worker) (pid : Option Nat)
    (step : Leanux.M Bool) (afterItem : Leanux.M Unit) (bound : Nat) (drained : String)
    (hs : ProductRetainsRoutingCall step) (ha : ProductRetainsRoutingCall afterItem) :
    ProductRetainsRoutingCall (workerLoop worker pid step afterItem bound drained) := by
  have hafter : ProductRetainsRoutingCall (do afterItem; pure false) := by
    apply ProjectedAction.of_wp
    intro s
    have h := RetainsRoutingCall.wp ha s
    mvcgen [h]
    subst s
    exact RetainsRouting.refl _
  apply ProjectedAction.of_wp
  intro s
  have hi := RetainsRoutingCall.wp (workerIter_routing worker pid step _ hs hafter) s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, workerLoop, hi, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals intros
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem handshakeReceiveWorker_routing :
    ProductRetainsRoutingCall (handshakeReceiveWorker (Env.nestedResched .receiveWorker)) :=
  workerLoop_routing _ _ _ _ _ _ receiveStep_routing.liftWG (nestedResched_routing .receiveWorker)

theorem xmitMulticastLoop_routing (family addr : Nat) :
    SameView (fun w : World => routingView w.wg) (Env.xmitMulticastLoop family addr) := by
  apply SameView.of_wp
  intro s
  have hl : Hoare (MonadLift.monadLift (loopbackSend [] true) : Leanux.M Unit)
      (fun w => routingView w.wg = s) (fun _ w => routingView w.wg = s) :=
    (sameView_liftWG (fun w : World => routingView w.wg) routingView _
      (routing_kernel _ (Queues.loopbackSend_kernel [] true)) (fun _ _ _ h => h)).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => routingView w.wg = s) (fun _ w => routingView w.wg = s) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at hl ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, Env.xmitMulticastLoop, hl, unsupported]

theorem inject_routing (family port : Nat) (msg : List UInt8) (tos : Nat)
    (ll : Bool) (dest : Nat) : ProductRetainsRoutingCall (Env.inject family port msg tos ll dest) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have editWG := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have routing {α : Type} (a : Net.M α) :=
    productRouting_spec a (fun store => P (store.2.2.2.dev.map routingState))
  have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    (sameView_liftWG (fun w : World => routingView w.wg) routingView a ha
      (fun _ _ _ h => h)).wp P
  unfold Hoare at ambient dev readWG editWG routing native
  have hn := fun pid => native _ (requireNotPending_routing pid "receiving while a handshake is queued")
  have hs := (product_store_routing _ (senderSource_sameKernel family dest tos ll)).wp P
  have hw (src : SkbSource) : Hoare
      (Env.runWorker .netRx (MonadLift.monadLift (wgReceive msg src)))
      (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    RetainsRoutingCall.wp (runWorker_routing .netRx _ (wgReceive_routing msg src).liftWG) s
  unfold Hoare at hw
  have hc := RetainsRoutingCall.wp runCryptWorkers_routing s
  have hd := fun queues => (requireDrained_routing "the datagram queued" queues).wp P
  have hl (α β : Type) := list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, editWG, routing, hidden, Env.fixtureSend, skipCut, getAmbient, modifyAmbient, Env.peekNextSite, peekUnit, resolveUnit, recordBudget, budgetExhausted, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    Env.inject, getRouting, getEnv, hn, hs, hw, hc, hd,  invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals intros
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem afterBatch_routing : ProductRetainsRoutingCall Env.afterBatch := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have editWG := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have routing {α : Type} (a : Net.M α) :=
    productRouting_spec a (fun store => P (store.2.2.2.dev.map routingState))
  have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    (sameView_liftWG (fun w : World => routingView w.wg) routingView a ha
      (fun _ _ _ h => h)).wp P
  unfold Hoare at ambient dev readWG editWG routing native
  have hc := RetainsRoutingCall.wp runCryptWorkers_routing s
  have hs := RetainsRoutingCall.wp runSendWorkers_routing s
  have hw := RetainsRoutingCall.wp runOneSendWorker_routing s
  have hsc := RetainsRoutingCall.wp (schedule_routing none) s
  have hd := fun qs => (requireDrained_routing "the batch queued" qs).wp P
  have he := deliverSent_routing.wp P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, editWG, routing, hidden, Env.fixtureSend, skipCut, getAmbient, modifyAmbient, Env.peekNextSite, peekUnit, resolveUnit, recordBudget, budgetExhausted, Env.afterBatch, hc, hs, hw, hsc, hd, he,  invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals intros
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem flood_routing (count port family : Nat) (messages : List (List UInt8)) :
    ProductRetainsRoutingCall (Env.flood count port family messages) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have editWG := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have routing {α : Type} (a : Net.M α) :=
    productRouting_spec a (fun store => P (store.2.2.2.dev.map routingState))
  have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    (sameView_liftWG (fun w : World => routingView w.wg) routingView a ha
      (fun _ _ _ h => h)).wp P
  unfold Hoare at ambient dev readWG editWG routing native
  have hn := fun pid => native _ (requireNotPending_routing pid "a flood while a handshake is queued")
  have hs := (product_store_routing _ (senderSource_sameKernel family 0 0 false)).wp P
  have hw (msg src) : ProductRetainsRoutingCall (Env.runWorker .netRx (do MonadLift.monadLift (wgReceive msg src); Env.pollScheduledInline)) := by
    apply runWorker_routing
    apply ProjectedAction.of_wp
    intro t
    have hr : Hoare (MonadLift.monadLift (wgReceive msg src) : Leanux.M Unit)
        (fun w => RetainsRouting t (routingView w.wg))
        (fun _ w => RetainsRouting t (routingView w.wg)) :=
      RetainsRoutingCall.wp (wgReceive_routing msg src).liftWG t
    unfold Hoare at hr
    have hp := RetainsRoutingCall.wp pollScheduledInline_routing t
    mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, editWG, routing, hidden, Env.fixtureSend, skipCut, getAmbient, modifyAmbient, Env.peekNextSite, peekUnit, resolveUnit, recordBudget, budgetExhausted, hr, hp]
    subst t
    exact RetainsRouting.refl _
  have hwp := fun msg src => RetainsRoutingCall.wp (hw msg src) s
  have ha := RetainsRoutingCall.wp afterBatch_routing s
  have hd := fun queues => (requireDrained_routing "the flood queued" queues).wp P
  have hl (α β : Type) := list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, editWG, routing, hidden, Env.fixtureSend, skipCut, getAmbient, modifyAmbient, Env.peekNextSite, peekUnit, resolveUnit, recordBudget, budgetExhausted, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    Env.flood, hn, hs, hwp, ha, hd,  invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals intros
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem batchItem_routing (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductRetainsRoutingCall (Environment.batchItemSource d cqes item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have editWG := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have routing {α : Type} (a : Net.M α) :=
    productRouting_spec a (fun store => P (store.2.2.2.dev.map routingState))
  have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    (sameView_liftWG (fun w : World => routingView w.wg) routingView a ha
      (fun _ _ _ h => h)).wp P
  unfold Hoare at ambient dev readWG editWG routing native
  have hs := fun family => (product_store_routing _ (senderSource_sameKernel family 0 0 false)).wp P
  have hw (msg src) : ProductRetainsRoutingCall (Env.runWorker .netRx (do MonadLift.monadLift (wgReceive msg src); Env.pollScheduledInline)) := by
    apply runWorker_routing
    apply ProjectedAction.of_wp
    intro t
    have hr : Hoare (MonadLift.monadLift (wgReceive msg src) : Leanux.M Unit)
        (fun w => RetainsRouting t (routingView w.wg))
        (fun _ w => RetainsRouting t (routingView w.wg)) :=
      RetainsRoutingCall.wp (wgReceive_routing msg src).liftWG t
    unfold Hoare at hr
    have hp := RetainsRoutingCall.wp pollScheduledInline_routing t
    mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, editWG, routing, hidden, Env.fixtureSend, skipCut, getAmbient, modifyAmbient, Env.peekNextSite, peekUnit, resolveUnit, recordBudget, budgetExhausted, hr, hp]
    subst t
    exact RetainsRouting.refl _
  have hwp := fun msg src => RetainsRoutingCall.wp (hw msg src) s
  have hx := fun family addr payload opts => (product_store_routing _ (xmitPackets_sameKernel family addr payload opts)).wp P
  have hm := fun family addr => (xmitMulticastLoop_routing family addr).wp P
  have ht (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
      Hoare (MonadLift.monadLift (wgXmit family addr pkts mtu) : Leanux.M Int)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    RetainsRoutingCall.wp (wgXmit_routing family addr pkts mtu).liftWG s
  unfold Hoare at ht
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, editWG, routing, hidden, Env.fixtureSend, skipCut, getAmbient, modifyAmbient, Env.peekNextSite, peekUnit, resolveUnit, recordBudget, budgetExhausted, Environment.batchItemSource, hs, hwp, hx, hm, ht, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals intros
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem batch_routing (items : List Env.BatchItem) : ProductRetainsRoutingCall (Env.batch items) := by
  rw [← Environment.batchSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have editWG := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have routing {α : Type} (a : Net.M α) :=
    productRouting_spec a (fun store => P (store.2.2.2.dev.map routingState))
  have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    (sameView_liftWG (fun w : World => routingView w.wg) routingView a ha
      (fun _ _ _ h => h)).wp P
  unfold Hoare at ambient dev readWG editWG routing native
  have hn := fun pid => native _ (requireNotPending_routing pid "a batch while a handshake is queued")
  have hi := fun d cqes item => RetainsRoutingCall.wp (batchItem_routing d cqes item) s
  have ha := RetainsRoutingCall.wp afterBatch_routing s
  have hl (α β : Type) := list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, editWG, routing, hidden, Env.fixtureSend, skipCut, getAmbient, modifyAmbient, Env.peekNextSite, peekUnit, resolveUnit, recordBudget, budgetExhausted, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    Environment.batchSource, hn, hi, ha,  unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals intros
  all_goals first | exact RetainsRouting.refl _ | assumption

end Leanux.Proofs.WG.AllowedIps
