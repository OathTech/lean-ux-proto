import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerSource

/-! Source-local native frames and closed worker contracts preserve the
concrete paired carrier on the same successful scheduler prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal
open CompleteProduct
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem iteration_checked (a : Activation) : Checked (iteration a) :=
  CompleteProduct.iteration encrypt_iteration decrypt_iteration receive_iteration
    (fun pid => tx_iter pid (tx_worker pid)) a

theorem run_checked (a : Activation) : Checked (SourceScheduler.run iteration a) :=
  SourceScheduler.run_preserves carrier_safe stable iteration iteration_checked a

theorem dispatch_checked (worker : Worker) : Checked (SourceScheduler.dispatch iteration worker) :=
  SourceScheduler.dispatch_preserves carrier_safe stable
    (fun pid => wg _ (work_queue (·.erase pid))) iteration iteration_checked worker

theorem occupancy_checked (a : Activation) : Checked (liftPrefix (Env.Activation.occupancy a)) :=
  product_store _ (SourceScheduler.occupancy_kernel a)

theorem runStep_checked (index : Nat) (state : RunState) : Checked (runStep index state) := by
  unfold runStep
  apply bind_checked (iteration_checked state.2)
  intro result
  cases result
  · exact bind_checked (ambient _) (fun _ => pure_checked _)
  · exact pure_checked _
  · exact bind_checked (ambient _) (fun _ => pure_checked _)

theorem dispatchChoose_checked (worker : Worker) : Checked (dispatchChoose worker) := by
  unfold dispatchChoose
  apply bind_checked (wg _ (state_store _ getDev_sameWGStore))
  intro device
  cases worker <;> dsimp only
  all_goals first
    | exact pure_checked _
    | exact conditional _ (fun _ => pure_checked _)
        (fun _ => bind_checked (ambient _) (fun _ => pure_checked _))
    | skip
  cases chosen : device.txWorkQueue.head? with
  | none => exact pure_checked _
  | some headPid =>
    apply bind_checked (ambient _)
    intro unit
    cases unit <;> simp only [pure_bind]
    · exact bind_checked (wg _ (erase_work headPid)) (fun _ =>
        bind_checked (ambient _) (fun _ => pure_checked _))
    · apply bind_checked (ambient _)
      intro pid
      exact bind_checked (wg _ (erase_work pid)) (fun _ =>
        bind_checked (ambient _) (fun _ => pure_checked _))

theorem choose_checked (stack : Option Worker) : Checked (choose stack) := by
  unfold choose
  repeat' first
    | (complete_product_native Lifetimes.pendingNapi; exact product_store _ (SourceScheduler.pendingNapi_kernel _))
    | (complete_product_native Env.Activation.hasWork; exact product_store _ (SourceScheduler.hasWork_kernel _))
    | (complete_product_native List.filterM; exact product_store _
        (filterM_sameKernel productStoreView _ activationConsistent_sameKernel _))
    | (complete_product_native unsupported; exact ambient _)
    | solve | complete_scheduler_native
    | complete_product_step

theorem perform_checked (choice : Choice) : Checked (perform choice) := by
  cases choice with
  | idle => exact pure_checked _
  | next => exact pure_checked _
  | resumed a => exact bind_checked (run_checked a) (fun _ => pure_checked _)
  | napi =>
    exact bind_checked softirq (fun _ => bind_checked (ambient _)
      (fun _ => conditional _ (fun _ => pure_checked _) (fun _ => pure_checked _)))
  | dispatch worker required =>
    unfold perform
    apply bind_checked (dispatch_checked worker)
    intro dispatched
    cases required <;> cases dispatched <;> simp only [Bool.false_eq_true,Bool.not_false,Bool.not_true,↓reduceIte]
    all_goals first | exact pure_checked _ | exact bind_checked (ambient _) (fun _ => pure_checked _)

theorem scheduleStep_checked (stack : Option Worker) (index : Nat) (state : ScheduleState) :
    Checked (scheduleStep stack index state) := bind_checked (choose_checked stack) perform_checked

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler
