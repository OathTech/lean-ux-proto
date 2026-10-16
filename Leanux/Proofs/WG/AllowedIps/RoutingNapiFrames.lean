import Leanux.Proofs.WG.AllowedIps.RoutingRxFrames
import Leanux.Proofs.Framing.Batch
import Leanux.Proofs.WG.Lifetimes.BatchNapi

/-! Concrete NET_RX and crypt-worker callbacks. The original captured pending
list, ambiguity choice, records and unsupported cases remain intact. These
normal-endpoint frames permit deletion and require no resident-list premise. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem runWorker_routing (worker : Worker) (body : Leanux.M Unit)
    (hb : ProductRetainsRoutingCall body) : ProductRetainsRoutingCall (Env.runWorker worker body) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg))
        (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have dev : Hoare (MonadLift.monadLift getDev : Leanux.M Device)
      (fun w => RetainsRouting s (routingView w.wg))
      (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productGetDev_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  unfold Hoare at dev
  have hbody := RetainsRoutingCall.wp hb s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, hidden, getAmbient, modifyAmbient, peekHiddenSite, invariant, unsupported, Env.runWorker, hbody]
  all_goals try dsimp +zetaDelta only at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

private theorem pendingPolls_routing (pending : List PeerId) :
    ProductRetainsRoutingCall (do
      for pid in pending do
        discard <| rxPoll pid NAPI_POLL_WEIGHT (fun xs => xs.forM Env.deliverInner)) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg))
        (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have dev : Hoare (MonadLift.monadLift getDev : Leanux.M Device)
      (fun w => RetainsRouting s (routingView w.wg))
      (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productGetDev_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  unfold Hoare at dev
  have hp := fun pid => RetainsRoutingCall.wp (actualRxPoll_routing pid NAPI_POLL_WEIGHT) s
  have hl (α β : Type) := list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) (α := α) (β := β) (RetainsRouting s)
  have hd (α : Type) := discard_view_spec (m := Except Stop) (fun w : World => routingView w.wg) (α := α) (RetainsRouting s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, hidden, getAmbient, modifyAmbient, peekHiddenSite, invariant, unsupported, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hd, hp]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem napiSoftirq_routing : ProductRetainsRoutingCall Env.napiSoftirq := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg))
        (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have dev : Hoare (MonadLift.monadLift getDev : Leanux.M Device)
      (fun w => RetainsRouting s (routingView w.wg))
      (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productGetDev_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  unfold Hoare at dev
  have hw := fun pending => RetainsRoutingCall.wp (runWorker_routing .netRx _ (pendingPolls_routing pending)) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, hidden, getAmbient, peekHiddenSite, Env.napiSoftirq, hw, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

/-- The second actual direct poll site runs without opening a new section. -/
theorem pollScheduledInline_routing : ProductRetainsRoutingCall Env.pollScheduledInline := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg))
        (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have dev : Hoare (MonadLift.monadLift getDev : Leanux.M Device)
      (fun w => RetainsRouting s (routingView w.wg))
      (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productGetDev_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  unfold Hoare at dev
  have hp := fun pid => RetainsRoutingCall.wp (actualRxPoll_routing pid NAPI_POLL_WEIGHT) s
  have hl (α β : Type) := list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) (α := α) (β := β) (RetainsRouting s)
  have hd (α : Type) := discard_view_spec (m := Except Stop) (fun w : World => routingView w.wg) (α := α) (RetainsRouting s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, hidden, getAmbient, modifyAmbient, peekHiddenSite, invariant, unsupported, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hd,
    Env.pollScheduledInline, hp, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem napiIrqExit_routing : ProductRetainsRoutingCall Env.napiIrqExit := by
  rw [← napiIrqExitSource_eq]
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg))
        (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have dev : Hoare (MonadLift.monadLift getDev : Leanux.M Device)
      (fun w => RetainsRouting s (routingView w.wg))
      (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productGetDev_spec (fun store => RetainsRouting s (store.2.2.2.dev.map routingState))
  unfold Hoare at dev
  have hn := RetainsRoutingCall.wp napiSoftirq_routing s
  have choice : Hoare chooseNapiHere
      (fun w => RetainsRouting s (routingView w.wg))
      (fun _ w => RetainsRouting s (routingView w.wg)) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  unfold Hoare at choice
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, dev, choice, getAmbient, peekHiddenSite, napiIrqExitSource, hn, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem actualEncryptStep_routing : ProductRetainsRoutingCall (encryptStep Env.checksumHelp Env.napiSoftirq) :=
  encryptStep_routing _ _ actualChecksum_routing napiSoftirq_routing

theorem actualEncryptIter_routing :
    ProductRetainsRoutingCall (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
  encryptIter_routing _ _ _ actualChecksum_routing napiSoftirq_routing
    (ProjectedRetainsRoutingCall.of_same
      ((Framing.condResched_sameKernel .encryptWorker).of_factor
        (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
        (fun w : World => routingView w.wg) (fun _ => rfl)))

theorem actualDecryptStep_routing : ProductRetainsRoutingCall (decryptStep Env.napiSoftirq Env.napiIrqExit) :=
  decryptStep_routing _ _ napiSoftirq_routing napiIrqExit_routing

theorem actualDecryptIter_routing :
    ProductRetainsRoutingCall (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
  decryptIter_routing _ _ _ napiSoftirq_routing napiIrqExit_routing
    (ProjectedRetainsRoutingCall.of_same
      ((Framing.condResched_sameKernel .decryptWorker).of_factor
        (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
        (fun w : World => routingView w.wg) (fun _ => rfl)))

theorem actualTxIter_routing (pid : PeerId) : ProductRetainsRoutingCall (txIter pid (Env.condResched .txWorker)) :=
  txIter_routing _ _ (ProjectedRetainsRoutingCall.of_same
      ((Framing.condResched_sameKernel .txWorker).of_factor
        (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
        (fun w : World => routingView w.wg) (fun _ => rfl)))

end Leanux.Proofs.WG.AllowedIps
