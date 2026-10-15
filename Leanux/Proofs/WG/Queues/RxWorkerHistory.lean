import Leanux.Proofs.WG.Queues.RxWorkerCuts
import Leanux.Proofs.WG.Origins.HistoryAdapters

/-! Concrete crypt-worker callbacks share the persistent poll journal. Only
source cuts without a poll are focused as a whole; actual NAPI calls use their
stamped observers. Failed callbacks retain their prefix and skip later cleanup. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def encryptIteration : Obs IterResult := do
  napiSoftirq
  mixed RxWorkers.encryptTail

theorem encryptIteration_erases : ErasesPrefix encryptIteration
    (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  rw [RxWorkers.encrypt_source]
  exact erasesPrefix_bind napiSoftirq_erases (fun _ => mixed_erases RxWorkers.encryptTail_erases)

theorem encryptIteration_preserves : PrefixPreserves BoundaryInv BoundarySafe encryptIteration :=
  PrefixPreserves.bind napiSoftirq_preserves (fun _ => mixed_preserves RxWorkers.encryptTail_preserves)

theorem encryptIteration_projects : ProjectsUnder AuditInv auditEvent encryptIteration
    (auditFocus (encryptIterPrefix (fun p => liftPrefix (Env.checksumHelp p))
      napiSoftirqPrefix (liftPrefix (Env.condResched .encryptWorker)))) := by
  rw [RxWorkers.encrypt_prefix]
  exact projectsFocus_bind napiSoftirq_projects napiSoftirqPrefix_allocation
    (fun _ => mixed_projects RxWorkers.encryptTail_preserves) (fun _ => RxWorkers.encryptTail_preserves)

def decryptStep : Obs Bool :=
  RxWorkers.decryptWith Origins.HistoryAdapters.prepare
    (fun pid => mixed (peerPutMixed (some pid))) napiSoftirq napiIrqExit

private theorem decryptStep_allocation : PrefixPreserves AllocationInv LifetimeEvent.Safe
    (decryptStepPrefix napiSoftirqPrefix napiIrqExitPrefix) :=
  decryptStepPrefix_preserves_ambient allocationAmbient decryptQueue_allocation
    napiSoftirqPrefix_allocation napiIrqExitPrefix_allocation

theorem decryptStep_erases : ErasesPrefix decryptStep (WG.decryptStep Env.napiSoftirq Env.napiIrqExit) := by
  rw [← RxWorkers.decrypt_source]
  unfold decryptStep RxWorkers.decryptWith RxWorkers.decryptSource
  repeat' first
    | with_reducible exact napiSoftirq_erases
    | with_reducible exact napiIrqExit_erases
    | with_reducible exact Origins.HistoryAdapters.prepare_erases
    | with_reducible exact mixed_erases (peerPutMixed_erases _)
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem decryptStep_preserves : PrefixPreserves BoundaryInv BoundarySafe decryptStep := by
  unfold decryptStep RxWorkers.decryptWith
  repeat' first
    | with_reducible exact napiSoftirq_preserves
    | with_reducible exact napiIrqExit_preserves
    | with_reducible exact Origins.HistoryAdapters.prepare_preserves
    | with_reducible exact mixed_preserves (allocationAmbient.peerPut _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem decryptStep_projects : ProjectsUnder AuditInv auditEvent decryptStep
    (auditFocus (decryptStepPrefix napiSoftirqPrefix napiIrqExitPrefix)) := by
  rw [← RxWorkers.decrypt_prefix]
  unfold decryptStep RxWorkers.decryptWith
  repeat' first
    | with_reducible exact napiSoftirq_projects
    | with_reducible exact napiIrqExit_projects
    | with_reducible exact Origins.HistoryAdapters.prepare_projects
    | with_reducible exact mixed_projects (allocationAmbient.peerPut _)
    | with_reducible exact projectsFocus_pure _
    | with_reducible exact napiSoftirqPrefix_allocation
    | with_reducible exact napiIrqExitPrefix_allocation
    | with_reducible exact RxWorkers.prepare_preserves
    | with_reducible exact allocationAmbient.peerPut _
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply projectsFocus_bind
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

def decryptIteration : Obs IterResult :=
  workerIterPrefix .decryptWorker none decryptStep
    (do liftPrefix (branch .decWorkerNeedResched (← liftPrefix (Env.condResched .decryptWorker))))

theorem decryptIteration_erases : ErasesPrefix decryptIteration
    (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
  workerIterPrefix_erases _ _ decryptStep_erases
    (erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_lift _))

theorem decryptIteration_preserves : PrefixPreserves BoundaryInv BoundarySafe decryptIteration :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) decryptStep_preserves
    (PrefixPreserves.bind
      (kernelLiftPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he) (condResched_sameKernel _))
      (fun _ => kernelLiftPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he) (sameKernel_branch _ _)))

theorem decryptIteration_projects : ProjectsUnder AuditInv auditEvent decryptIteration
    (auditFocus (decryptIterPrefix napiSoftirqPrefix napiIrqExitPrefix
      (liftPrefix (Env.condResched .decryptWorker)))) := by
  unfold decryptIteration decryptIterPrefix workerIterPrefix
  repeat' first
    | with_reducible exact decryptStep_projects
    | with_reducible exact decryptStep_allocation
    | with_reducible exact projectsFocus_lift _
    | with_reducible exact projectsFocus_pure _
    | with_reducible exact allocation_kernel _ (condResched_sameKernel _)
    | with_reducible exact allocation_kernel _ (sameKernel_branch _ _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply projectsFocus_bind
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Queues.RxHistory
