import Leanux.Proofs.WG.Queues.RxActivationHistory

/-! Concrete activation runs and dispatch retain every reached poll. Queue
occupancy uses the existing lifetime observer, and the finite loop keeps its
actual continuation history, including a failed final iteration. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- Distribute the inner lifetime focus through a finite loop using its actual
allocation/append contract. The outer projection retains all prior probes. -/
theorem projectsFocus_forIn (xs : List γ) (init : β)
    (g : γ → β → Obs (ForInStep β)) (a : γ → β → MixedM (ForInStep β))
    (ha : ∀ x z, PrefixPreserves AllocationInv LifetimeEvent.Safe (a x z))
    (hg : ∀ x z, ProjectsUnder AuditInv auditEvent (g x z) (auditFocus (a x z))) :
    ProjectsUnder AuditInv auditEvent (forIn xs init g) (auditFocus (forIn xs init a)) := by
  induction xs generalizing init with
  | nil => exact projectsFocus_pure init
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply projectsFocus_bind (hg x init) (ha x init)
    · intro step
      cases step with
      | done z => exact projectsFocus_pure z
      | yield z => exact ih z
    · intro step
      cases step with
      | done z => exact PrefixPreserves.pure allocationAmbient.safe z
      | yield z => exact PrefixPreserves.forIn xs z a allocationAmbient.safe ha

theorem projectsFocus_range (r : Std.Legacy.Range) (init : β)
    (g : Nat → β → Obs (ForInStep β)) (a : Nat → β → MixedM (ForInStep β))
    (ha : ∀ x z, PrefixPreserves AllocationInv LifetimeEvent.Safe (a x z))
    (hg : ∀ x z, ProjectsUnder AuditInv auditEvent (g x z) (auditFocus (a x z))) :
    ProjectsUnder AuditInv auditEvent (forIn r init g) (auditFocus (forIn r init a)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact projectsFocus_forIn _ init g a ha hg

theorem boundaryLift_kernel (a : M α) (ha : SameKernel a) :
    PrefixPreserves BoundaryInv BoundarySafe (liftPrefix a) :=
  kernelLiftPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he) ha

def activationRun (a : Activation) : Obs Unit := do
  let occupancy ← mixed (activationOccupancyPrefix a)
  let mut act := a
  for _ in [0:occupancy + 1] do
    match ← activationIteration act with
    | .ended => _ ← liftPrefix (hidden (.sectionStop act.worker)); return
    | .continued => act := {act with iterations := act.iterations + 1}
    | .yielded =>
      liftPrefix (modify fun s => {s with suspended := s.suspended ++ [{act with iterations := act.iterations + 1}]})
      return
  liftPrefix (invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) in one run")

theorem activationRun_erases (a : Activation) :
    ErasesPrefix (activationRun a) (Env.Activation.run a) := by
  unfold activationRun Env.Activation.run
  repeat' first
    | with_reducible exact mixed_erases (activationOccupancyPrefix_erases _)
    | with_reducible exact activationIteration_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationRun_preserves (a : Activation) :
    PrefixPreserves BoundaryInv BoundarySafe (activationRun a) := by
  unfold activationRun
  repeat' first
    | with_reducible exact mixed_preserves (activationOccupancyPrefix_preserves allocationAmbient _)
    | with_reducible exact activationIteration_preserves _
    | with_reducible exact boundaryLift_kernel _ (hidden_sameKernel _)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationRun_projects (a : Activation) :
    ProjectsUnder AuditInv auditEvent (activationRun a) (auditFocus (activationRunPrefix a)) := by
  unfold activationRun activationRunPrefix
  repeat' first
    | with_reducible exact mixed_projects (activationOccupancyPrefix_preserves allocationAmbient _)
    | with_reducible exact activationIteration_projects _
    | with_reducible exact projectsFocus_lift _
    | with_reducible exact projectsFocus_pure _
    | with_reducible exact activationOccupancyPrefix_preserves allocationAmbient _
    | with_reducible exact activationIterPrefix_allocation _
    | with_reducible exact allocation_kernel _ (hidden_sameKernel _)
    | exact allocation_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact allocation_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply projectsFocus_range
    | with_reducible apply projectsFocus_bind
    | with_reducible apply PrefixPreserves.range _ _ _ allocationAmbient.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def dispatch (worker : Worker) : Obs Bool := do
  let d ← liftPrefix getDev
  let mut pid : Option Nat := none
  match worker with
  | .encryptWorker => if d.encryptQueue.empty then return false
  | .decryptWorker => if d.decryptQueue.empty then return false
  | .receiveWorker => if d.handshakeQueue.isEmpty then return false
  | .txWorker =>
    let some headPid := d.txWorkQueue.head? | return false
    let p ← match ← liftPrefix (peekUnit .txWorker) with
      | some u => liftPrefix (resolveUnit .txWorker u d.txWorkQueue)
      | none => pure headPid
    mixed (liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase p}))
    pid := some p
  | _ => return false
  _ ← liftPrefix (hidden (.sectionStart worker))
  activationRun {worker, pid}
  return true

theorem dispatch_erases (worker : Worker) : ErasesPrefix (dispatch worker) (Env.dispatch worker) := by
  unfold dispatch Env.dispatch
  repeat' first
    | with_reducible exact activationRun_erases _
    | with_reducible exact mixed_erases (erasesPrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem dispatch_preserves (worker : Worker) : PrefixPreserves BoundaryInv BoundarySafe (dispatch worker) := by
  unfold dispatch
  repeat' first
    | with_reducible exact activationRun_preserves _
    | with_reducible exact mixed_preserves (txWorkQueueErase_allocation _)
    | with_reducible exact boundaryLift_kernel _ getDev_sameKernel
    | with_reducible exact boundaryLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact boundaryLift_kernel _ (resolveUnit_sameKernel _ _ _)
    | with_reducible exact boundaryLift_kernel _ (hidden_sameKernel _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem dispatch_projects (worker : Worker) :
    ProjectsUnder AuditInv auditEvent (dispatch worker) (auditFocus (dispatchPrefix worker)) := by
  unfold dispatch dispatchPrefix
  repeat' first
    | with_reducible exact activationRun_projects _
    | with_reducible exact mixed_projects (txWorkQueueErase_allocation _)
    | with_reducible exact projectsFocus_lift _
    | with_reducible exact projectsFocus_pure _
    | with_reducible exact activationRunPrefix_allocation _
    | with_reducible exact txWorkQueueErase_allocation _
    | with_reducible exact allocation_kernel _ getDev_sameKernel
    | with_reducible exact allocation_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact allocation_kernel _ (resolveUnit_sameKernel _ _ _)
    | with_reducible exact allocation_kernel _ (hidden_sameKernel _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply projectsFocus_bind
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Queues.RxHistory
