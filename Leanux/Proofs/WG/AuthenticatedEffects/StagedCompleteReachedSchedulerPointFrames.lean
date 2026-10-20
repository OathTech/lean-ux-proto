import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointSource

/-! The native atoms have concrete paired frames. Consistency trials use their
original copied-world kernel frame, without treating trials as committed work. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal
open CompleteProduct

theorem Native.checked (token : Native action) : Checked (liftPrefix action) := by
  cases token with
  | reading source => exact source.checked
  | device => exact wg _ (state_store _ getDev_sameWGStore)
  | ambient => exact CompleteProduct.ambient _
  | budget => exact CompleteProduct.ambient _
  | occupancy a => exact occupancy_checked a
  | refills => exact refills_checked
  | pendingDevice worker queued => exact product_store _ (pendingDevice_sameKernel worker queued)
  | pending next => exact product_store _ (SourceScheduler.pendingNapi_kernel next)
  | work a => exact product_store _ (SourceScheduler.hasWork_kernel a)
  | trials active =>
      exact product_store _ (filterM_sameKernel productStoreView _ activationConsistent_sameKernel active)
  | hiddenSite => exact CompleteProduct.ambient _
  | unit worker => exact CompleteProduct.ambient _
  | resolve worker unit peers => exact CompleteProduct.ambient _
  | eraseWork pid => exact wg _ (erase_work pid)
  | start worker => exact CompleteProduct.ambient _
  | stop worker => exact CompleteProduct.ambient _
  | suspend a => exact CompleteProduct.ambient _
  | resume a => exact CompleteProduct.ambient _
  | invariant message => exact CompleteProduct.ambient _
  | unsupported message => exact CompleteProduct.ambient _
  | exhausted message => exact CompleteProduct.ambient _

theorem Child.checked (token : Child action) : Checked action := by
  cases token with
  | iteration a => exact iteration_checked a
  | napi => exact softirq

theorem Shape.checked (shape : Shape action) : Checked action := by
  induction shape with
  | pure value => exact pure_checked value
  | native token => exact token.checked
  | child token => exact token.checked
  | bind head tail ihHead ihTail => exact bind_checked ihHead ihTail
  | marked label shape ih => exact ih

theorem Shape.normal (shape : Shape action) (before : Carrier h w)
    (performed : runPrefix action w h = (.ok (value,u),middle)) : Carrier middle u :=
  Scheduler.checked_normal shape.checked before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
