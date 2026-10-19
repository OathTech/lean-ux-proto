import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeFlow

/-! Native timer arms and queue appends leave the lexical stack unchanged.
Their receipt records read the current stack but do not authorize its cause. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxHeartbeats 600000

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe (effects.arm pid timer delay caller) :=
  state_current _ (fun _ => state_receipt _ (state_lift _) _ (fun _ => rfl))

theorem queue (pid : PeerId) : StateSafe (effects.append pid) :=
  state_current _ (fun _ => state_receipt _ (state_lift _) _ (fun _ => rfl))

macro "scope_effect_step" : tactic => `(tactic| first
  | (scope_balance_head TimerEffects.Ops.step; exact state_lift _)
  | (scope_balance_head TimerEffects.Ops.arm; exact arm _ _ _ _)
  | (scope_balance_head TimerEffects.Ops.append; exact queue _)
  | scope_state_step)

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateSafe (TimerEffects.modifyWith effects site pid timer delay) := by
  unfold TimerEffects.modifyWith
  repeat' scope_effect_step

theorem derived (pid : PeerId) : StateSafe (TimerEffects.derivedWith effects pid) := by
  unfold TimerEffects.derivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact state_bind (modify_timer _ _ _ _) (fun _ => state_pure _)

theorem traversal (pid : PeerId) : StateSafe (TimerEffects.traversalWith effects pid) := by
  unfold TimerEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (scope_balance_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | scope_effect_step

theorem data_sent (pid : PeerId) : StateSafe (TimerEffects.dataSentWith effects pid) := by
  unfold TimerEffects.dataSentWith
  repeat' scope_effect_step

theorem data_received (pid : PeerId) : StateSafe (TimerEffects.dataReceivedWith effects pid) := by
  unfold TimerEffects.dataReceivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (scope_balance_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | scope_effect_step

theorem initiated (pid : PeerId) : StateSafe (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  repeat' scope_effect_step

theorem queued (pid : PeerId) (retry : Bool) : StateSafe (TimerEffects.queuedWith effects pid retry) := by
  unfold TimerEffects.queuedWith
  repeat' scope_effect_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
