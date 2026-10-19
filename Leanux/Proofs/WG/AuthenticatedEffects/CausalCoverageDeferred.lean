import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageWorkers
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageSend
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageTimers

/-! Both real timer-selection modes bracket the native validation and callback
with the exact returned token. Normal timer completion closes before deferred
work; Stop preserves the valid open prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem crypt : ProductAt frames (Driver.cryptObserved hooks) :=
  product_bind (schedule none) (fun _ => product_lift _)

theorem send_workers : ProductAt frames (Driver.sendWorkersObserved hooks) := by
  unfold Driver.sendWorkersObserved
  repeat' first
    | (coverage_head Driver.sendWorkerObserved; exact send_worker)
    | (coverage_head Driver.scheduleObserved; exact schedule _)
    | coverage_product_step

theorem after_xmit : ProductAt frames (Driver.afterXmitObserved hooks) := by
  unfold Driver.afterXmitObserved
  repeat' first
    | (coverage_head Driver.cryptObserved; exact crypt)
    | (coverage_head Driver.sendWorkersObserved; exact send_workers)
    | coverage_product_step

theorem timer_section (worker : Worker) (body : PrefixM Event Unit) (safe : ProductAt frames body) :
    ProductAt frames (Driver.timerSectionObserved worker body) := by
  unfold Driver.timerSectionObserved
  dsimp only
  split
  · apply product_bind (product_lift _)
    intro _
    apply product_bind (product_lift _)
    intro _
    exact runWorkerPrefix_preserves (fun _ _ ready => ready.1)
      (fun _ _ _ _ ready => ready) worker safe
  · apply product_bind (product_lift _)
    intro _
    exact runWorkerPrefix_preserves (fun _ _ ready => ready.1)
      (fun _ _ _ _ ready => ready) worker safe

theorem timer_enter_checked (d : Device) (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (frames : List (CausalScope.Token Cause)) :
    PrefixEnsures (fun h (_ : World) => Inv frames h) Safe (hooks.timerSelected d j pid timer entry)
      (fun index h (_ : World) => Inv (⟨index,.timer j pid timer entry⟩ :: frames) h) := by
  intro w h ready
  let selected : Event := .old (.timerSelected ⟨d,j,pid,timer,entry,w⟩)
  have kept : Inv frames (h ++ [selected]) := ready.emit rfl (fun impossible => impossible.elim)
  have pushed := kept.enter ⟨(h ++ [selected]).length,.timer j pid timer entry⟩
  refine ⟨[selected,.scope (.entered ⟨(h ++ [selected]).length,.timer j pid timer entry⟩)],?_,pushed.1,pushed⟩
  change (runPrefix (TimerDispatch.scope (Event.old ∘ TransmitSecurity.Journal.Event.timerSelected)
    d j pid timer entry (CausalScope.enterPrefix Event.scope (.timer j pid timer entry))) w h).2 = _
  rw [TimerDispatch.scope_run]
  change (h ++ [selected]) ++ [_] = h ++ [selected,_]
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  rfl

theorem timer_enter_bind (d : Device) (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (next : Nat → PrefixM Event α) (before after : List (CausalScope.Token Cause))
    (tail : ∀ index, Flow (⟨index,.timer j pid timer entry⟩ :: before) after (next index)) :
    Flow before after (hooks.timerSelected d j pid timer entry >>= next) :=
  PrefixEnsures.bind (timer_enter_checked d j pid timer entry before) tail

macro "coverage_timer_step" : tactic => `(tactic| first
  | (coverage_first_head Driver.Hooks.timerSelected; apply timer_enter_bind)
  | (coverage_first_head Driver.Hooks.timerFinished; apply leave_bind)
  | (coverage_head Driver.cryptObserved; exact crypt)
  | (coverage_head Driver.sendWorkersObserved; exact send_workers)
  | (coverage_head Driver.sendWorkerObserved; exact send_worker)
  | (coverage_head Driver.timerSectionObserved; apply timer_section; exact product_state _ (timer_callback _ _ (by simp)))
  | coverage_flow_step
  | coverage_product_step)

theorem timers (j : UInt64) : ProductAt frames (Driver.timersObserved hooks j) := by
  unfold Driver.timersObserved
  repeat' coverage_timer_step

theorem placeholder_timers (j : UInt64) : ProductAt frames (Driver.placeholderTimersObserved hooks j) := by
  unfold Driver.placeholderTimersObserved
  repeat' coverage_timer_step

theorem idle_timers : ProductAt frames (Driver.idleTimersObserved hooks) := by
  unfold Driver.idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (coverage_head Driver.timersObserved; exact timers _)
    | (coverage_head Driver.placeholderTimersObserved; exact placeholder_timers _)
    | coverage_product_step

theorem after_advance : ProductAt frames (Driver.afterAdvanceObserved hooks) := by
  unfold Driver.afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (coverage_head Driver.timersObserved; exact timers _)
    | (coverage_head Driver.placeholderTimersObserved; exact placeholder_timers _)
    | coverage_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
