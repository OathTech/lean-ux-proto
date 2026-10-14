import Leanux.Proofs.WG.Queues.RxWorkerCuts

/-! Concrete crypt-worker callbacks share the persistent poll journal. Only
source cuts without a poll are focused as a whole; actual NAPI calls use their
stamped observers. Failed callbacks retain their prefix and skip later cleanup. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def mixed (a : MixedM α) : Obs α := audit (auditFocus a)

theorem mixed_erases (he : ErasesPrefix a original) : ErasesPrefix (mixed a) original :=
  audit_erases (auditFocus_erases he)

theorem mixed_preserves (ha : PrefixPreserves AllocationInv LifetimeEvent.Safe a) :
    PrefixPreserves BoundaryInv BoundarySafe (mixed a) :=
  audit_preserves _ (auditFocus_preserves ha)

theorem mixed_projects (ha : PrefixPreserves AllocationInv LifetimeEvent.Safe a) :
    ProjectsUnder AuditInv auditEvent (mixed a) (auditFocus a) :=
  audit_projects (auditFocus_preserves ha)

/-- Compose directly to one focused lifetime observer at the current audit
history, retaining probe interleaving and the continuation's actual prefix. -/
theorem projectsFocus_bind
    (hg : ProjectsUnder AuditInv auditEvent g (auditFocus a))
    (ha : PrefixPreserves AllocationInv LifetimeEvent.Safe a)
    (hf : ∀ x, ProjectsUnder AuditInv auditEvent (f x) (auditFocus (b x)))
    (hb : ∀ x, PrefixPreserves AllocationInv LifetimeEvent.Safe (b x)) :
    ProjectsUnder AuditInv auditEvent (g >>= f) (auditFocus (a >>= b)) := by
  have projected := projectsUnder_bind hg (auditFocus_preserves ha) hf
  have focused := FocusesUnder.bind (encode := AuditEvent.lifetime) (decode := AuditEvent.lifetime?)
    (fun _ => rfl) (FocusesUnder.focus a) ha (fun x => FocusesUnder.focus (b x)) hb
  intro w h hi
  exact (focused w (h.filterMap auditEvent) hi.1).symm.trans (projected w h hi)

theorem projectsFocus_lift (a : M α) :
    ProjectsUnder AuditInv auditEvent (liftPrefix a) (auditFocus (liftPrefix a)) := by
  intro w h hi
  have focused := FocusesUnder.lift (I := AllocationInv)
    (encode := AuditEvent.lifetime) (decode := AuditEvent.lifetime?) a w (h.filterMap auditEvent) hi.1
  exact focused.symm.trans (projectsUnder_lift (I := AuditInv) auditEvent a w h hi)

theorem projectsFocus_pure (x : α) :
    ProjectsUnder AuditInv auditEvent (pure x) (auditFocus (pure x)) := by
  intro w h hi
  have focused := FocusesUnder.pure (I := AllocationInv)
    (encode := AuditEvent.lifetime) (decode := AuditEvent.lifetime?) x w (h.filterMap auditEvent) hi.1
  exact focused.symm.trans (projectsUnder_pure (I := AuditInv) auditEvent x w h hi)

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
  RxWorkers.decryptWith (mixed RxWorkers.preparePrefix)
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
    | with_reducible exact mixed_erases RxWorkers.prepare_erases
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
    | with_reducible exact mixed_preserves RxWorkers.prepare_preserves
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
    | with_reducible exact mixed_projects RxWorkers.prepare_preserves
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
