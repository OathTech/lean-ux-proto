import Leanux.Proofs.WG.AllowedIps.RoutingHandshakeReceiveFrames
import Leanux.Proofs.WG.Queues.SourceScheduler
import Leanux.Proofs.WG.AllowedIps.RoutingNapiFrames

/-! Concrete scheduler routing frames, including original copied consistency
trials. The source-shaped scheduler contracts are instantiated with a fixed
input routing view, then exact erasure recovers all-input normal endpoints.
No successful trial, residency or progress premise is required. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem cryptAhead_routing (pid : PeerId) : ProductRetainsRoutingCall (Env.cryptAhead pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView a ha
      (fun _ _ _ h => h)).wp P
  have hg := native _ (getPeer_routing pid)
  have skb {α : Type} (a : SkbM α) :
      Hoare (MonadLift.monadLift (liftSkb a) : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) := by
    apply native
    apply SameView.of_wp
    intro initial
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have ha := native _ (modifyDev_routing
    (fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}) (fun _ => rfl))
  have he := native _ (modifyDev_routing
    (fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}) (fun _ => rfl))
  have hi := RetainsRoutingCall.wp actualEncryptIter_routing s
  unfold Hoare at hg skb ambient ha he
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.cryptAhead, getTxSkb,
    getAmbient, modifyAmbient, peekHiddenSite, invariant, hg, skb, ambient, ha, he, hi]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem activationIter_routing (a : Activation) : ProductRetainsRoutingCall (Env.Activation.iter a) := by
  apply ProjectedAction.of_wp
  intro s
  have he := RetainsRoutingCall.wp actualEncryptIter_routing s
  have hd := RetainsRoutingCall.wp actualDecryptIter_routing s
  have hr :
      ⦃fun w => ⌜RetainsRouting s (routingView w.wg)⌝⦄
      workerIter .receiveWorker none (MonadLift.monadLift receiveStep : Leanux.M Bool)
        (Env.condResched .receiveWorker)
      ⦃⇓? _ w => ⌜RetainsRouting s (routingView w.wg)⌝⦄ :=
    RetainsRoutingCall.wp actualReceiveIter_routing s
  have ht := fun pid => RetainsRoutingCall.wp (actualTxIter_routing pid) s
  have hc := fun pid => RetainsRoutingCall.wp (cryptAhead_routing pid) s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg))
        (fun _ w => RetainsRouting s (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.Activation.iter, he, hd, hr, ht, hc, invariant, ambient]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

private def Holds (s : Option RoutingState) (_ : List Unit) (w : World) : Prop :=
  RetainsRouting s (routingView w.wg)

private theorem holds_kernel (s : Option RoutingState) :
    ∀ h w v, productStoreView v = productStoreView w → Holds s h w → Holds s h v := by
  intro h w v hk hi
  have hd := congrArg (fun store : ProductStore43 => store.2.2.2.dev.map routingState) hk
  change routingView v.wg = routingView w.wg at hd
  simpa only [Holds, hd] using hi

private theorem lift_holds (s : Option RoutingState) (a : Leanux.M α) (ha : ProductRetainsRoutingCall a) :
    PrefixPreserves (Holds s) (fun _ => True) (liftPrefix a) :=
  (PrefixEnsures.lift a (fun _ _ _ => True.intro)
    (fun _ w x v hi hr => hi.trans ((ProjectedAction.iff_run _ _ _).mp ha w x v hr))).preserves

private theorem retains_of_erases (a : Leanux.M α) (g : PrefixM Unit α)
    (he : ErasesPrefix g a)
    (hp : ∀ s, PrefixPreserves (Holds s) (fun _ => True) g) : ProductRetainsRoutingCall a := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  obtain ⟨_, _, _, ho⟩ := hp (routingView w.wg) w [] (RetainsRouting.refl _)
  simpa only [he w [], hr, Holds] using ho

private def iteration (a : Activation) : PrefixM Unit IterResult := liftPrefix (Env.Activation.iter a)
private def napi : PrefixM Unit Unit := liftPrefix Env.napiSoftirq
private theorem iteration_preserves (s : Option RoutingState) (a : Activation) :
    PrefixPreserves (Holds s) (fun _ => True) (iteration a) :=
  lift_holds s _ (activationIter_routing a)
private theorem queueErase_preserves (s : Option RoutingState) (pid : PeerId) :
    PrefixPreserves (Holds s) (fun _ => True)
      (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))) :=
  lift_holds s _ (RetainsRoutingCall.liftWG
    (ProjectedRetainsRoutingCall.of_same (modifyDev_routing _ (fun _ => rfl))))

theorem activationRun_routing (a : Activation) : ProductRetainsRoutingCall (Env.Activation.run a) := by
  apply retains_of_erases _ (Queues.SourceScheduler.run iteration a)
  · exact Queues.SourceScheduler.run_erases iteration (fun _ => erasesPrefix_lift _) a
  · intro s
    exact Queues.SourceScheduler.run_preserves (fun _ _ _ => True.intro)
      (holds_kernel s) iteration (iteration_preserves s) a

theorem dispatch_routing (worker : Worker) : ProductRetainsRoutingCall (Env.dispatch worker) := by
  apply retains_of_erases _ (Queues.SourceScheduler.dispatch iteration worker)
  · exact Queues.SourceScheduler.dispatch_erases iteration (fun _ => erasesPrefix_lift _) worker
  · intro s
    exact Queues.SourceScheduler.dispatch_preserves (fun _ _ _ => True.intro)
      (holds_kernel s) (queueErase_preserves s) iteration (iteration_preserves s) worker

theorem schedule_routing (stack : Option Worker := none) : ProductRetainsRoutingCall (Env.schedule stack) := by
  apply retains_of_erases _ (Queues.SourceScheduler.schedule iteration napi stack)
  · exact Queues.SourceScheduler.schedule_erases iteration napi
      (fun _ => erasesPrefix_lift _) (erasesPrefix_lift _) stack
  · intro s
    exact Queues.SourceScheduler.schedule_preserves (fun _ _ _ => True.intro)
      (holds_kernel s) (queueErase_preserves s) iteration napi (iteration_preserves s)
      (lift_holds s _ napiSoftirq_routing) stack

theorem nestedResched_routing (self : Worker) : ProductRetainsRoutingCall (Env.nestedResched self) := by
  apply ProjectedAction.of_wp
  intro s
  have hc := ((condResched_sameKernel self).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)).wp (RetainsRouting s)
  have hs := RetainsRoutingCall.wp (schedule_routing (some self)) s
  mvcgen [Env.nestedResched, hc, hs]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
