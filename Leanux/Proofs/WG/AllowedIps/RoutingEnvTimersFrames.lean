import Leanux.Proofs.WG.AllowedIps.RoutingEnvWorkersFrames
import Leanux.Proofs.WG.Environment.TimerSource

/-! Both original timer-selection modes and their enclosing idle/advance callers
retain routing on normal return. Saved scans and finite bounds remain the actual
source computations; no due-entry residency or successful-drain assumption is
introduced, and all original failures remain possible. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem runTimerSection_routing (worker : Worker) (body : M Unit)
    (hb : RetainsRoutingCall body) : RetainsRoutingCall (Env.runTimerSection worker body) := by
  apply ProjectedAction.of_wp
  intro s
  have hw := (runWorker_routing worker body hb).wp s
  mvcgen [Env.runTimerSection, hw, invariant]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

private theorem fireTimerAfterScan_routing (worker : Worker) (t : PeerTimer)
    (jHi : UInt64) (due : List PeerId) :
    RetainsRoutingCall (Environment.fireTimerAfterScan worker t jHi due) := by
  apply ProjectedAction.of_wp
  intro s
  have hp := (routing_kernel _ (peekUnit_sameKernel worker)).wp (RetainsRouting s)
  have hd := fun pid => (delTimer_routing pid t).wp (RetainsRouting s)
  have hw := fun pid => (runTimerSection_routing worker _ (timerCallback_routing pid t)).wp s
  mvcgen [Environment.fireTimerAfterScan, hp, hd, hw, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem fireTimer_routing (worker : Worker) (jHi : UInt64) :
    RetainsRoutingCall (Env.fireTimer worker jHi) := by
  rw [← Environment.fireTimerSource_eq]
  apply ProjectedAction.of_wp
  intro s
  have hf := fun t due => (fireTimerAfterScan_routing worker t jHi due).wp s
  mvcgen [Environment.fireTimerSource, hf, getDev, getK, invariant]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem runTimers_routing (jHi : UInt64) : RetainsRoutingCall (Env.runTimers jHi) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hb := (routing_kernel _ recordBudget_sameKernel).wp P
  have hp := (routing_kernel _ peekNextSite_sameKernel).wp P
  have hf := fun worker => (fireTimer_routing worker jHi).wp s
  have hc := runOneClearWorker_routing.wp s
  have hs := runOneSendWorker_routing.wp s
  have hx := runCryptWorkers_routing.wp s
  have hd := deliverSent_routing.wp P
  mvcgen [Env.runTimers, hb, hp, hf, hc, hs, hx, hd, getDev, getK, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try trivial
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem runTimersPlaceholder_routing (jHi : UInt64) :
    RetainsRoutingCall (Env.runTimersPlaceholder jHi) := by
  rw [← Environment.runTimersPlaceholderSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hd := fun pid t => (delTimer_routing pid t).wp P
  have ht := fun t => (routing_kernel _ (timerWorker_sameKernel t)).wp P
  have hw := fun worker pid t => (runTimerSection_routing worker _ (timerCallback_routing pid t)).wp s
  have hx := runCryptWorkers_routing.wp s
  have hs := runSendWorkers_routing.wp s
  have hc := runOneClearWorker_routing.wp s
  mvcgen [Environment.runTimersPlaceholderSource, hd, ht, hw, hx, hs, hc, getDev, getK, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try trivial
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem idleTimers_routing : RetainsRoutingCall Env.idleTimers := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ht := fun j => (runTimers_routing j).wp s
  have hp := (routing_kernel _ (peekSiteU64_sameKernel .jiffiesEnd)).wp P
  have hh := (routing_kernel _ (hiddenJiffies_sameKernel .jiffiesEnd)).wp P
  have hd (α : Type) := discard_view_spec routingView (α := α) P
  mvcgen [Env.idleTimers, ht, hp, hh, hd, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem advance_routing (ticks : Nat) : SameView routingView (Env.advance ticks) :=
  routing_kernel _ (advance_sameKernel ticks)

theorem afterAdvance_routing : RetainsRoutingCall Env.afterAdvance := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ht := fun j => (runTimers_routing j).wp s
  have hf := fun j => (runTimersPlaceholder_routing j).wp s
  have hp := (routing_kernel _ (peekSiteU64_sameKernel .jiffiesEnd)).wp P
  have hh := (routing_kernel _ (hiddenJiffies_sameKernel .jiffiesEnd)).wp P
  have hd (α : Type) := discard_view_spec routingView (α := α) P
  mvcgen [Env.afterAdvance, ht, hf, hp, hh, hd, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

end Leanux.Proofs.WG.AllowedIps
