import Leanux.Proofs.WG.AllowedIps.RoutingEnvWorkersFrames
import Leanux.Proofs.WG.Environment.TimerSource
import Leanux.Proofs.WG.AllowedIps.RoutingMaintenanceFrames

/-! The current timer-wheel loops and their idle/advance callers retain routing
on normal return. Native callbacks execute through the actual product adapter;
record order, wheel detachment and pass-step guards remain the source's.
The former raw-expiry selectors are no longer mirror operations. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem runTimerSection_routing (worker : Worker) (body : Leanux.M Unit)
    (hb : ProductRetainsRoutingCall body) :
    ProductRetainsRoutingCall (Env.runTimerSection worker body) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  have hw := RetainsRoutingCall.wp (runWorker_routing worker body hb) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.runTimerSection, hw, ambient, dev, readWG, modifyWGSpec, getAmbient, modifyAmbient, Env.peekNextSite, peekSiteU64, hiddenJiffies, peekUnit, recordBudget, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try intros
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

private theorem requireStepComplete_routing (b : UInt64) :
    SameView (fun w : World => routingView w.wg) (Env.requireStepComplete b) := by
  apply SameView.of_wp
  intro s
  have dev := productGetDev_spec (fun store => store.2.2.2.dev.map routingState = s)
  unfold Hoare at dev
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.requireStepComplete, dev]

private theorem requireNothingDue_routing (jPass : UInt64) :
    SameView (fun w : World => routingView w.wg) (Env.requireNothingDue jPass) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  have timer := fun t => ((timerWorker_sameKernel t).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)).wp P
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.requireNothingDue,
    Env.sectionAppearsLater, timer, ambient, dev, readWG, modifyWGSpec, getAmbient, modifyAmbient, Env.peekNextSite, peekSiteU64, hiddenJiffies, peekUnit, recordBudget, invariant, unsupported]

theorem runTimers_routing (jHi : UInt64) :
    ProductRetainsRoutingCall (Env.runTimers jHi) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView a ha
      (fun _ _ _ h => h)).wp P
  have detach := fun pid t => native _ (delTimer_routing pid t)
  unfold Hoare at detach
  have timer := fun t => ((timerWorker_sameKernel t).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)).wp P
  have callback (worker : Worker) (pid : PeerId) (t : PeerTimer) :
      Hoare (Env.runTimerSection worker (MonadLift.monadLift (WG.timerCallback pid t)))
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    RetainsRoutingCall.wp
      (runTimerSection_routing worker _ (timerCallback_routing pid t).liftWG) s
  unfold Hoare at callback
  have step := fun b => (requireStepComplete_routing b).wp P
  have clear := RetainsRoutingCall.wp runOneClearWorker_routing s
  have send := RetainsRoutingCall.wp runOneSendWorker_routing s
  have crypt := RetainsRoutingCall.wp runCryptWorkers_routing s
  have deliver := deliverSent_routing.wp P
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.runTimers, detach, timer, callback,
    step, clear, send, crypt, deliver, ambient, dev, readWG, modifyWGSpec, getAmbient, modifyAmbient, Env.peekNextSite, peekSiteU64, hiddenJiffies, peekUnit, recordBudget, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try intros
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem runTimersPlaceholder_routing (jHi : UInt64) :
    ProductRetainsRoutingCall (Env.runTimersPlaceholder jHi) := by
  rw [← Environment.runTimersPlaceholderSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView a ha
      (fun _ _ _ h => h)).wp P
  have detach := fun pid t => native _ (delTimer_routing pid t)
  unfold Hoare at detach
  have timer := fun t => ((timerWorker_sameKernel t).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)).wp P
  have callback (worker : Worker) (pid : PeerId) (t : PeerTimer) :
      Hoare (Env.runTimerSection worker (MonadLift.monadLift (WG.timerCallback pid t)))
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    RetainsRoutingCall.wp
      (runTimerSection_routing worker _ (timerCallback_routing pid t).liftWG) s
  unfold Hoare at callback
  have crypt := RetainsRoutingCall.wp runCryptWorkers_routing s
  have send := RetainsRoutingCall.wp runSendWorkers_routing s
  have clear := RetainsRoutingCall.wp runOneClearWorker_routing s
  mvcgen [-Std.Do.Spec.monadLift_StateT, Environment.runTimersPlaceholderSource,
    detach, timer, callback, crypt, send, clear, ambient, dev, readWG, modifyWGSpec, getAmbient, modifyAmbient, Env.peekNextSite, peekSiteU64, hiddenJiffies, peekUnit, recordBudget, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try intros
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem idleTimers_routing : ProductRetainsRoutingCall Env.idleTimers := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  have timers := fun j => RetainsRoutingCall.wp (runTimers_routing j) s
  have placeholder := fun j => RetainsRoutingCall.wp (runTimersPlaceholder_routing j) s
  have noneDue := fun j => (requireNothingDue_routing j).wp P
  have discard (α : Type) := discard_view_spec (m := Except Stop)
    (fun w : World => routingView w.wg) (α := α) P
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.idleTimers,
    timers, placeholder, noneDue, discard, ambient, dev, readWG, modifyWGSpec, getAmbient, modifyAmbient, Env.peekNextSite, peekSiteU64, hiddenJiffies, peekUnit, recordBudget, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try intros
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem advance_routing (ticks : Nat) :
    SameView (fun w : World => routingView w.wg) (Env.advance ticks) :=
  (advance_sameKernel ticks).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)

theorem afterAdvance_routing : ProductRetainsRoutingCall Env.afterAdvance := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have modifyWGSpec := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  unfold Hoare at ambient dev readWG modifyWGSpec
  have timers := fun j => RetainsRoutingCall.wp (runTimers_routing j) s
  have placeholder := fun j => RetainsRoutingCall.wp (runTimersPlaceholder_routing j) s
  have noneDue := fun j => (requireNothingDue_routing j).wp P
  have discard (α : Type) := discard_view_spec (m := Except Stop)
    (fun w : World => routingView w.wg) (α := α) P
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.afterAdvance, getEnv,
    timers, placeholder, noneDue, discard, ambient, dev, readWG, modifyWGSpec, getAmbient, modifyAmbient, Env.peekNextSite, peekSiteU64, hiddenJiffies, peekUnit, recordBudget, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, productStoreView, wgStoreView]
  all_goals try trivial
  all_goals try intros
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

end Leanux.Proofs.WG.AllowedIps
