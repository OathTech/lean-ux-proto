import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainPointPaths

/-! Native carrier transport for fixed send-drain point entries and successful
returns. Child interiors are deliberately not inferred from these endpoints. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal
open CompleteProduct

theorem front_read_checked : Checked frontRead := wg_read
theorem front_check_checked : Checked frontCheck := product_store _ requireNoCryptWork_sameKernel
theorem front_reset_checked : Checked frontReset := wg_bookkeeping _ (fun _ => rfl)
theorem front_budget_checked : Checked frontBudget := ambient _

theorem FrontPoint.carrier (point : FrontPoint w history stage u middle)
    (before : Carrier history w) : Carrier middle u := by
  cases point with
  | entry => exact before
  | read run => exact Scheduler.checked_normal front_read_checked before run
  | checked read _ run =>
      exact Scheduler.checked_normal front_check_checked
        (Scheduler.checked_normal front_read_checked before read) run
  | reset read _ checked run =>
      exact Scheduler.checked_normal front_reset_checked
        (Scheduler.checked_normal front_check_checked
          (Scheduler.checked_normal front_read_checked before read) checked) run
  | budget read _ checked reset run =>
      exact Scheduler.checked_normal front_budget_checked
        (Scheduler.checked_normal front_reset_checked
          (Scheduler.checked_normal front_check_checked
            (Scheduler.checked_normal front_read_checked before read) checked) reset) run

theorem DeliveryPath.carrier (path : DeliveryPath w history u middle)
    (before : Carrier history w) : Carrier middle u :=
  Scheduler.checked_normal read_checked (path.loop.carrier before) path.read

theorem ChildEntry.carrier (path : ChildEntry w history child u middle)
    (before : Carrier history w) : Carrier middle u := by
  cases path with
  | delivery path => exact path.carrier before
  | worker path => exact path.carrier before
  | scheduler path => exact path.carrier before

theorem child_checked (child : Child) : Checked child.action := by
  cases child with
  | delivery => exact CompleteProduct.delivery
  | worker => exact scheduled_send
  | scheduler => exact schedule_checked

theorem ChildEntry.return_carrier (path : ChildEntry w history child u middle)
    (before : Carrier history w)
    (returned : runPrefix child.action u middle = (.ok ((),v),last)) : Carrier last v :=
  Scheduler.checked_normal (child_checked child) (path.carrier before) returned

theorem FinishPath.carrier (path : FinishPath w history acc u middle)
    (before : Carrier history w) : Carrier middle u :=
  Scheduler.checked_normal (CompleteProduct.list (Scheduler.indices path.budget) (none,()) step step_checked)
    (Scheduler.checked_normal front_checked before path.front) path.loop

theorem finish_checked (acc : LoopState) : Checked (finish acc) := by
  unfold finish
  cases acc.1 with
  | none => exact ambient _
  | some value => exact pure_checked value

theorem drain_checked : Checked (Driver.sendWorkersObserved hooks) := by
  rw [source_factor]
  apply bind_checked front_checked
  intro budget
  cases budget with
  | none => exact pure_checked _
  | some budget =>
      change Checked (body budget)
      rw [body_list]
      exact bind_checked (CompleteProduct.list (Scheduler.indices budget) (none,()) step step_checked) finish_checked

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
