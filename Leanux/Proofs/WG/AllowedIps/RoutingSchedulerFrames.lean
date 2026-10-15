import Leanux.Proofs.WG.AllowedIps.RoutingHandshakeReceiveFrames
import Leanux.Proofs.WG.Queues.SourceScheduler

/-! Concrete scheduler routing frames, including original copied consistency
trials. The source-shaped scheduler contracts are instantiated with a fixed
input routing view, then exact erasure recovers all-input normal endpoints.
No successful trial, residency or progress premise is required. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem cryptAhead_routing (pid : PeerId) : RetainsRoutingCall (Env.cryptAhead pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := (getPeer_routing pid).wp P
  have ht := fun id => (getTxSkb_routing id).wp P
  have hh := (routing_kernel _ peekHiddenSite_sameKernel).wp P
  have ha := (modifyDev_routing (fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}) (fun _ => rfl)).wp P
  have he := (modifyDev_routing (fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}) (fun _ => rfl)).wp P
  have hi := actualEncryptIter_routing.wp s
  mvcgen [Env.cryptAhead, hg, ht, hh, ha, he, hi, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem activationIter_routing (a : Activation) : RetainsRoutingCall (Env.Activation.iter a) := by
  apply ProjectedAction.of_wp
  intro s
  have he := actualEncryptIter_routing.wp s
  have hd := actualDecryptIter_routing.wp s
  have hr := actualReceiveIter_routing.wp s
  have ht := fun pid => (actualTxIter_routing pid).wp s
  have hc := fun pid => (cryptAhead_routing pid).wp s
  mvcgen [Env.Activation.iter, he, hd, hr, ht, hc, invariant]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

private def Holds (s : Option RoutingState) (_ : List Unit) (w : World) : Prop :=
  RetainsRouting s (routingView w)

private theorem holds_kernel (s : Option RoutingState) :
    ∀ h w v, v.k = w.k → Holds s h w → Holds s h v := by
  intro h w v hk hi
  simpa only [Holds, routingView, hk] using hi

private theorem lift_holds (s : Option RoutingState) (a : M α) (ha : RetainsRoutingCall a) :
    PrefixPreserves (Holds s) (fun _ => True) (liftPrefix a) :=
  (PrefixEnsures.lift a (fun _ _ _ => True.intro)
    (fun _ w x v hi hr => hi.trans (ha w x v hr))).preserves

private theorem retains_of_erases (a : M α) (g : PrefixM Unit α)
    (he : ErasesPrefix g a)
    (hp : ∀ s, PrefixPreserves (Holds s) (fun _ => True) g) : RetainsRoutingCall a := by
  intro w x v hr
  obtain ⟨_, _, _, ho⟩ := hp (routingView w) w [] (RetainsRouting.refl _)
  simpa only [he w [], hr, Holds] using ho

private def iteration (a : Activation) : PrefixM Unit IterResult := liftPrefix (Env.Activation.iter a)
private def napi : PrefixM Unit Unit := liftPrefix Env.napiSoftirq
private theorem iteration_preserves (s : Option RoutingState) (a : Activation) :
    PrefixPreserves (Holds s) (fun _ => True) (iteration a) :=
  lift_holds s _ (activationIter_routing a)
private theorem queueErase_preserves (s : Option RoutingState) (pid : PeerId) :
    PrefixPreserves (Holds s) (fun _ => True)
      (liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid})) :=
  lift_holds s _ (.of_same (modifyDev_routing _ (fun _ => rfl)))

theorem activationRun_routing (a : Activation) : RetainsRoutingCall (Env.Activation.run a) := by
  apply retains_of_erases _ (Queues.SourceScheduler.run iteration a)
  · exact Queues.SourceScheduler.run_erases iteration (fun _ => erasesPrefix_lift _) a
  · intro s
    exact Queues.SourceScheduler.run_preserves (fun _ _ _ => True.intro)
      (holds_kernel s) iteration (iteration_preserves s) a

theorem dispatch_routing (worker : Worker) : RetainsRoutingCall (Env.dispatch worker) := by
  apply retains_of_erases _ (Queues.SourceScheduler.dispatch iteration worker)
  · exact Queues.SourceScheduler.dispatch_erases iteration (fun _ => erasesPrefix_lift _) worker
  · intro s
    exact Queues.SourceScheduler.dispatch_preserves (fun _ _ _ => True.intro)
      (holds_kernel s) (queueErase_preserves s) iteration (iteration_preserves s) worker

theorem schedule_routing (stack : Option Worker := none) : RetainsRoutingCall (Env.schedule stack) := by
  apply retains_of_erases _ (Queues.SourceScheduler.schedule iteration napi stack)
  · exact Queues.SourceScheduler.schedule_erases iteration napi
      (fun _ => erasesPrefix_lift _) (erasesPrefix_lift _) stack
  · intro s
    exact Queues.SourceScheduler.schedule_preserves (fun _ _ _ => True.intro)
      (holds_kernel s) (queueErase_preserves s) iteration napi (iteration_preserves s)
      (lift_holds s _ napiSoftirq_routing) stack

theorem nestedResched_routing (self : Worker) : RetainsRoutingCall (Env.nestedResched self) := by
  apply ProjectedAction.of_wp
  intro s
  have hc := (routing_kernel _ (condResched_sameKernel self)).wp (RetainsRouting s)
  have hs := (schedule_routing (some self)).wp s
  mvcgen [Env.nestedResched, hc, hs]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
