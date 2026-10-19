import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeWorkers
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeSend
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeTimers

/-! Both real timer-selection modes bracket the native validation and callback
with the exact returned token. Normal timer completion closes before deferred
work; Stop preserves the valid open prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem deliver : ProductSafe hooks.deliver := by
  intro frames
  apply DeliverySource.observed_preserves Event.delivery (fun _ _ ready => ⟨frames,ready⟩)
  · intro h w sent ready
    simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,scope?,List.append_nil] using ready
  · exact product_lift _ frames

theorem crypt : ProductSafe (Driver.cryptObserved hooks) :=
  product_bind (schedule none) (fun _ => deliver)

theorem send_workers : ProductSafe (Driver.sendWorkersObserved hooks) := by
  unfold Driver.sendWorkersObserved
  repeat' first
    | (scope_balance_head Driver.Hooks.deliver; exact deliver)
    | (scope_balance_head Driver.sendWorkerObserved; exact send_worker)
    | (scope_balance_head Driver.scheduleObserved; exact schedule _)
    | scope_product_step

theorem after_xmit : ProductSafe (Driver.afterXmitObserved hooks) := by
  unfold Driver.afterXmitObserved
  repeat' first
    | (scope_balance_head Driver.Hooks.deliver; exact deliver)
    | (scope_balance_head Driver.cryptObserved; exact crypt)
    | (scope_balance_head Driver.sendWorkersObserved; exact send_workers)
    | scope_product_step

theorem timer_section (worker : Worker) (body : PrefixM Event Unit) (safe : ProductSafe body) :
    ProductSafe (Driver.timerSectionObserved worker body) := by
  unfold Driver.timerSectionObserved
  dsimp only
  split
  · apply product_bind (product_lift _)
    intro _
    apply product_bind (product_lift _)
    intro _ frames
    exact runWorkerPrefix_preserves (fun _ _ ready => ⟨frames,ready⟩)
      (fun _ _ _ _ ready => ready) worker (safe frames)
  · apply product_bind (product_lift _)
    intro _ frames
    exact runWorkerPrefix_preserves (fun _ _ ready => ⟨frames,ready⟩)
      (fun _ _ _ _ ready => ready) worker (safe frames)

theorem timer_enter_checked (d : Device) (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (frames : List (CausalScope.Token Cause)) :
    PrefixEnsures (fun h (_ : World) => CausalScope.stack (h.filterMap scope?) = .ok frames)
      (CausalScope.WellFormed scope?) (hooks.timerSelected d j pid timer entry)
      (fun index h (_ : World) => CausalScope.stack (h.filterMap scope?) = .ok (⟨index,.timer j pid timer entry⟩ :: frames)) := by
  intro w h ready
  let selected : Event := .old (.timerSelected ⟨d,j,pid,timer,entry,w⟩)
  have kept : CausalScope.stack ((h ++ [selected]).filterMap scope?) = .ok frames := by
    simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,selected,scope?,List.append_nil] using ready
  have pushed := CausalScope.stack_entered scope? Event.scope (fun _ => rfl)
    (h ++ [selected]) frames ⟨(h ++ [selected]).length,.timer j pid timer entry⟩ kept
  refine ⟨[selected,.scope (.entered ⟨(h ++ [selected]).length,.timer j pid timer entry⟩)],?_,⟨_,pushed⟩,pushed⟩
  simp only [hooks,CausalSources.timerEnter,TimerDispatch.scope_run]
  change (h ++ [selected]) ++ [_] = h ++ [selected,_]
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  rfl

theorem timer_enter_bind (d : Device) (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (next : Nat → PrefixM Event α) (before after : List (CausalScope.Token Cause))
    (tail : ∀ index, Flow (⟨index,.timer j pid timer entry⟩ :: before) after (next index)) :
    Flow before after (hooks.timerSelected d j pid timer entry >>= next) :=
  PrefixEnsures.bind (timer_enter_checked d j pid timer entry before) tail

macro "scope_timer_step" : tactic => `(tactic| first
  | (scope_balance_head Driver.Hooks.deliver; exact deliver)
  | (scope_first_head Driver.Hooks.timerSelected; apply universal; intro frames; apply timer_enter_bind)
  | (scope_first_head Driver.Hooks.timerFinished; apply leave_bind)
  | (scope_balance_head Driver.cryptObserved; exact crypt)
  | (scope_balance_head Driver.sendWorkersObserved; exact send_workers)
  | (scope_balance_head Driver.sendWorkerObserved; exact send_worker)
  | (scope_balance_head Driver.timerSectionObserved; apply timer_section; exact product_state _ (timer_callback _ _))
  | scope_flow_step
  | scope_product_step)

theorem timers (j : UInt64) : ProductSafe (Driver.timersObserved hooks j) := by
  unfold Driver.timersObserved
  repeat' scope_timer_step

theorem placeholder_timers (j : UInt64) : ProductSafe (Driver.placeholderTimersObserved hooks j) := by
  unfold Driver.placeholderTimersObserved
  repeat' scope_timer_step

theorem idle_timers : ProductSafe (Driver.idleTimersObserved hooks) := by
  unfold Driver.idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (scope_balance_head Driver.Hooks.deliver; exact deliver)
    | (scope_balance_head Driver.timersObserved; exact timers _)
    | (scope_balance_head Driver.placeholderTimersObserved; exact placeholder_timers _)
    | scope_product_step

theorem after_advance : ProductSafe (Driver.afterAdvanceObserved hooks) := by
  unfold Driver.afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (scope_balance_head Driver.Hooks.deliver; exact deliver)
    | (scope_balance_head Driver.timersObserved; exact timers _)
    | (scope_balance_head Driver.placeholderTimersObserved; exact placeholder_timers _)
    | scope_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
