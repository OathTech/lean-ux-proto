import Leanux.Proofs.WG.AllowedIps.RoutingSchedulerFrames
import Leanux.Proofs.WG.AllowedIps.RoutingNapiFrames
import Leanux.Proofs.Framing.EnvLeaves
import Leanux.Proofs.WG.Keypairs.Frames.Env

/-! Deferred environment workers retain routing at every normal endpoint.
The captured work queues do not imply residency: original getters establish
fresh setter facts or Stop, and worker cleanup may delete resident peers. The
legacy environment import shares generated matcher declarations under Lean 4.35. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-- Preserve the complete native pre/post relation through the actual adapter. -/
private theorem native_lift_spec (a : WG.M α) {P : WGWorld → Prop}
    {Q : α → WGWorld → Prop} (ha : Hoare a P Q) :
    Hoare (MonadLift.monadLift a : Leanux.M α)
      (fun w => P w.wg) (fun x w => Q x w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hp hr
  change (liftWG a).run w = .ok (x, v) at hr
  rw [liftWG_run] at hr
  cases he : (a.run w.wg).run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y, g⟩, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact (hoare_iff_run_ambient _ _ _).mp ha _ _ _ _ _ hp he

theorem deliverSent_routing : SameView (fun w : World => routingView w.wg) Env.deliverSent :=
  deliverSent_sameKernel.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w => routingView w.wg) (fun _ => rfl)

theorem requireNoCryptWork_routing : SameView (fun w : World => routingView w.wg) Env.requireNoCryptWork :=
  requireNoCryptWork_sameKernel.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w => routingView w.wg) (fun _ => rfl)

theorem requireDrained_routing (what : String) (queues : List Bool) :
    SameView (fun w : World => routingView w.wg) (Env.requireDrained what queues) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => routingView w.wg = s) (fun _ w => routingView w.wg = s) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => store.2.2.2.dev.map routingState = s)
  have readWG := productGetWG_spec (fun store => store.2.2.2.dev.map routingState = s)
  have modifyWGSpec := productModifyWG_spec (fun store => store.2.2.2.dev.map routingState = s)
  unfold Hoare at ambient dev readWG modifyWGSpec
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, modifyWGSpec, hidden, getAmbient, peekUnit, resolveUnit, recordBudget, budgetExhausted, Env.requireDrained, dev, invariant, unsupported]

theorem runCryptWorkers_routing : ProductRetainsRoutingCall Env.runCryptWorkers := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  have hs := RetainsRoutingCall.wp (schedule_routing none) s
  have hd := deliverSent_routing.wp (RetainsRouting s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, modifyWGSpec, hidden, getAmbient, peekUnit, resolveUnit, recordBudget, budgetExhausted, Env.runCryptWorkers, hs, hd]
  subst s
  exact RetainsRouting.refl _

theorem runOneSendWorker_routing : ProductRetainsRoutingCall Env.runOneSendWorker := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) (initial : ProductStore43) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => productStoreView w = initial) (fun _ w => productStoreView w = initial) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev (initial : ProductStore43) := productGetDev_spec (fun store => store = initial)
  have readWG := productGetWG_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  let P := RetainsRouting s
  have hm := fun pid => native_lift_spec _ ((modifyDev_routing (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) (fun _ => rfl)).wp P)
  have hg := fun pid => native_lift_spec _ (routing_getPeer P pid)
  have hs := fun pid p => native_lift_spec _ (routing_setPeer P pid p)
  have hw (pid : PeerId) : Hoare
      (Env.runWorker .sendWorker (MonadLift.monadLift (handshakeSendWorker pid)))
      (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    RetainsRoutingCall.wp (runWorker_routing .sendWorker _ (handshakeSendWorker_routing pid).liftWG) s
  unfold Hoare at hw
  unfold Hoare at hm
  unfold Hoare at hg hs
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, modifyWGSpec, hidden, getAmbient, peekUnit, resolveUnit, recordBudget, budgetExhausted, Env.runOneSendWorker, hm, hg, hs, hw, dev, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try subst s
  all_goals intros
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem runOneClearWorker_routing : ProductRetainsRoutingCall Env.runOneClearWorker := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  let P := RetainsRouting s
  have hm := fun pid => native_lift_spec _ ((modifyDev_routing (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) (fun _ => rfl)).wp P)
  have hw (pid : PeerId) : Hoare
      (Env.runWorker .clearPeerWorker (MonadLift.monadLift (queuedExpiredZeroKeyMaterial pid)))
      (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    RetainsRoutingCall.wp (runWorker_routing .clearPeerWorker _ (queuedExpiredZeroKeyMaterial_routing pid).liftWG) s
  unfold Hoare at hw
  unfold Hoare at hm
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, modifyWGSpec, hidden, getAmbient, peekUnit, resolveUnit, recordBudget, budgetExhausted, Env.runOneClearWorker, hm, hw, dev, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem runSendWorkers_routing : ProductRetainsRoutingCall Env.runSendWorkers := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  let P := RetainsRouting s
  have hn := requireNoCryptWork_routing.wp P
  have hd := deliverSent_routing.wp P
  have hw := RetainsRoutingCall.wp runOneSendWorker_routing s
  have hs := RetainsRoutingCall.wp (schedule_routing none) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, modifyWGSpec, hidden, getAmbient, peekUnit, resolveUnit, recordBudget, budgetExhausted, Env.runSendWorkers, hn, hd, hw, hs, dev, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem afterXmit_routing : ProductRetainsRoutingCall Env.afterXmit := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  have hc := RetainsRoutingCall.wp runCryptWorkers_routing s
  have hs := RetainsRoutingCall.wp runSendWorkers_routing s
  have hd := fun what queues => (requireDrained_routing what queues).wp (RetainsRouting s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, readWG, modifyWGSpec, hidden, getAmbient, peekUnit, resolveUnit, recordBudget, budgetExhausted, Env.afterXmit, hc, hs, hd, dev, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

end Leanux.Proofs.WG.AllowedIps
