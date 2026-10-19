import Leanux.Proofs.WG.RetirementSecurity.HolderSchedulerAtoms

/-! Exact key credit through the original complete scheduler. All real
worker and NAPI obligations are discharged on the existing source spine;
there is no incoming universal worker contract or alternate driver. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem ahead (pid : PeerId) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves (fun _ _ entry=>entry.1.2.1.safe) _ atoms _ encrypt pid

theorem iteration (activation : Activation) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe (RxHistory.activationIteration activation) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ atoms _ _ _ _ _ encrypt ahead tx decrypt handshake activation

theorem run (activation : Activation) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe (RxHistory.activationRun activation) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves (I:=Inv initial loans before temporary locals active)
    (fun _ _ entry=>entry.1.2.1.safe) (fun _ _ _ same entry=>store entry same) _ atoms _ iteration activation

theorem dispatch (worker : Worker) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves (I:=Inv initial loans before temporary locals active)
    (fun _ _ entry=>entry.1.2.1.safe) (fun _ _ _ same entry=>store entry same) _ atoms _ run worker

theorem schedule (stack : Option Worker) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe (RxHistory.schedule stack) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves (I:=Inv initial loans before temporary locals active)
    (fun _ _ entry=>entry.1.2.1.safe) (fun _ _ _ same entry=>store entry same) _ atoms _ _ _ dispatch run softirq stack

theorem nested (worker : Worker) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe (RxHistory.nestedResched worker) := by
  rw [RxHistory.SchedulerSource.nested_factor]
  exact RxHistory.SchedulerSource.nested_preserves (I:=Inv initial loans before temporary locals active)
    (fun _ _ entry=>entry.1.2.1.safe) (fun _ _ _ same entry=>store entry same) _ schedule worker

end Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
