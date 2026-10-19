import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReturnSource

/-! Return preparation preserves the native packet account and literal prior
history. Each fixed callback is checked by its concrete original source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReturnSource
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal CompletePrefix.Product

theorem prelude_checked : Checked prelude := by
  unfold prelude
  apply bind_checked
  · apply list
    intro c acc
    exact bind_checked (seccomp (Seccomp.enterHarnessCall c))
      (fun _=>pure_checked (ForInStep.yield ()))
  intro _
  exact fs taskWorkRun

theorem prelude_history (w : World) (h : List Event) :
    (runPrefix prelude w h).2=h := by
  have quiet : HistoryFrame some prelude := by
    unfold prelude
    apply HistoryFrame.bind
    · apply HistoryFrame.forIn
      intro c acc
      exact HistoryFrame.bind (HistoryFrame.lift _ _) (fun _=>HistoryFrame.pure _ _)
    intro _
    exact HistoryFrame.lift _ _
  simpa only [List.filterMap_some] using quiet w h

theorem callback_checked (call : Syscall) (action : PrefixM Event Unit)
    (member : action∈callbacks call) : Checked action := by
  cases call <;> simp only [callbacks,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals first
    | contradiction
    | (rcases member with rfl | rfl | rfl)
    | (rcases member with rfl | rfl)
    | (subst action)
  all_goals first
    | (prefix_product_head Driver.sendWorkersObserved; exact Execution.sends)
    | (prefix_product_head Driver.idleTimersObserved; exact Execution.idle)
    | (prefix_product_head Driver.afterXmitObserved; exact Execution.after_xmit)
    | (prefix_product_head Driver.afterAdvanceObserved; exact Execution.advance)
    | (prefix_product_native Env.netnsCleanup; exact cleanup)
    | (prefix_product_native Env.routeIntoWg0; exact product_store _ Framing.routeIntoWg0_sameKernel)

theorem sequence_checked (actions : List (PrefixM Event Unit))
    (checked : ∀ action∈actions,Checked action) : Checked (sequence actions) := by
  induction actions with
  | nil => exact pure_checked ()
  | cons action rest ih =>
    exact bind_checked (checked action (by simp))
      (fun _=>ih (fun value member=>checked value (by simp only [List.mem_cons]; exact Or.inr member)))

theorem prefix_checked (call : Syscall) (count : Nat) : Checked (callbackPrefix call count) :=
  bind_checked prelude_checked (fun _=>sequence_checked _
    (fun action member=>callback_checked call action (List.mem_of_mem_take member)))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReturnSource
