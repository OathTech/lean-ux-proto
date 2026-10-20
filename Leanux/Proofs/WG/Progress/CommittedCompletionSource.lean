import Leanux.Proofs.WG.Progress.CommittedCompletionModel
import Leanux.Proofs.WG.Progress.CommittedRunSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes RxHistory.SchedulerSource

theorem run_preserves (origin : Origin) (a : Activation) :
    PrefixPreserves (fun history _ => NormalHistory history) (fun _ => True)
      (run origin a) := by
  intro entry history prior
  let receipt : Receipt := ⟨origin,a,Campaign2.Product.snapshot entry,
    (activationExitRun a entry).map Campaign2.Product.snapshot⟩
  refine ⟨[receipt], ?_, trivial, ?_⟩
  · rw [run_exact]
  · rw [run_exact]
    cases actual : (Env.Activation.run a).run entry with
    | error stop => trivial
    | ok out =>
      obtain ⟨value,final⟩ := out
      cases value
      have source := congrArg (fun action : Leanux.M _ => action.run entry)
        (observedActivationExit_source a)
      change Except.ok (receipt.exit.erase,entry) =
        Except.ok (Campaign2.Product.observeResult ((Env.Activation.run a).run entry),entry) at source
      have fresh : NormalReceipt receipt := by
        refine ⟨Campaign2.Product.snapshot final, ?_⟩
        have same := congrArg Prod.fst (Except.ok.inj source)
        simpa only [actual,Campaign2.Product.observeResult,Except.map] using same
      change NormalHistory (history ++ [receipt])
      intro r member
      rcases List.mem_append.mp member with earlier | latest
      · exact prior r earlier
      · simp only [List.mem_singleton] at latest
        subst r
        exact fresh

theorem lift_preserves {α : Type} (action : Leanux.M α) :
    PrefixPreserves (fun history _ => NormalHistory history) (fun _ => True)
      (liftPrefix action) :=
  PrefixEnsures.preserves (PrefixEnsures.lift action (fun _ _ _ => trivial)
    (fun _ _ _ _ prior _ => prior))

theorem atoms : AtomContracts (fun history _ => NormalHistory history) (fun _ => True)
    (fun {_} a => old a) := by
  constructor
  all_goals intros; exact lift_preserves _

theorem dispatch_preserves (worker : Worker) :
    PrefixPreserves (fun history _ => NormalHistory history) (fun _ => True) (dispatch worker) :=
  RxHistory.SchedulerSource.dispatch_preserves
    (I := fun history _ => NormalHistory history) (S := fun _ => True)
    (fun _ _ _ => trivial) (fun _ _ _ _ prior => prior)
    _ atoms _ (run_preserves .dispatch) worker

theorem schedule_preserves (stack : Option Worker) :
    PrefixPreserves (fun history _ => NormalHistory history) (fun _ => True) (schedule stack) :=
  RxHistory.SchedulerSource.schedule_preserves
    (I := fun history _ => NormalHistory history) (S := fun _ => True)
    (fun _ _ _ => trivial) (fun _ _ _ _ prior => prior)
    _ atoms _ _ _ dispatch_preserves (run_preserves .resume) (lift_preserves _) stack

end Leanux.Proofs.WG.Progress.CommittedRuns.Completion
