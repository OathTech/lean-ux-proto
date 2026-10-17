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
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have lifted {α : Type} (a : WG.M α) (ha : SameView routingView a) :
      Preserves P (monadLift a : Leanux.M α) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView a ha (fun _ _ _ h => h)).wp Q
  have peer : Preserves P (monadLift (getPeer pid) : Leanux.M Peer) := lifted _ (getPeer_routing pid)
  have packets {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
    intro initial
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  have skb (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    lifted _ (packets _)
  have append : Preserves P (monadLift (modifyDev fun d =>
      {d with txWorkQueue := d.txWorkQueue ++ [pid]}) : Leanux.M Unit) :=
    lifted _ (modifyDev_routing _ (fun _ => rfl))
  have erase : Preserves P (monadLift (modifyDev fun d =>
      {d with txWorkQueue := d.txWorkQueue.erase pid}) : Leanux.M Unit) :=
    lifted _ (modifyDev_routing _ (fun _ => rfl))
  have iteration : Preserves P (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
    RetainsRoutingCall.wp actualEncryptIter_routing s
  have stopped {α : Type} (e : Stop) : Preserves P (throw e : Leanux.M α) := hoare_throw e
  have main : Preserves P (Env.cryptAhead pid) := by
    routing_tx_source [Env.cryptAhead, getAmbient, modifyAmbient, peekHiddenSite] using
      [peer, skb, append, erase, iteration, ambient, stopped]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem activationIter_routing (a : Activation) : ProductRetainsRoutingCall (Env.Activation.iter a) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have encrypt : Preserves P (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
    RetainsRoutingCall.wp actualEncryptIter_routing s
  have decrypt : Preserves P (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
    RetainsRoutingCall.wp actualDecryptIter_routing s
  have receive : Preserves P (workerIter .receiveWorker none (monadLift receiveStep : Leanux.M Bool)
      (Env.condResched .receiveWorker)) := RetainsRoutingCall.wp actualReceiveIter_routing s
  have transmit (pid : PeerId) : Preserves P (txIter pid (Env.condResched .txWorker)) :=
    RetainsRoutingCall.wp (actualTxIter_routing pid) s
  have ahead (pid : PeerId) : Preserves P (Env.cryptAhead pid) := RetainsRoutingCall.wp (cryptAhead_routing pid) s
  have main : Preserves P (Env.Activation.iter a) := by
    routing_tx_source [Env.Activation.iter] using [encrypt, decrypt, receive, transmit, ahead, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

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
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have cond : Preserves P (Env.condResched self) :=
    ((condResched_sameKernel self).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl)).wp Q
  have schedule : Preserves P (Env.schedule (some self)) := RetainsRoutingCall.wp (schedule_routing (some self)) s
  have main : Preserves P (Env.nestedResched self) := by
    routing_tx_source [Env.nestedResched] using [cond, schedule]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.AllowedIps
