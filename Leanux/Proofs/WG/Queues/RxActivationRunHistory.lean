import Leanux.Proofs.WG.Queues.RxActivationHistory

/-! Concrete activation runs and dispatch retain every reached poll. Queue
occupancy uses the existing lifetime observer, and the finite loop keeps its
actual continuation history, including a failed final iteration. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- Distribute the inner lifetime focus through a finite loop using its actual
allocation/append contract. The outer projection retains all prior probes. -/
theorem projectsFocus_forIn (xs : List γ) (init : β)
    (g : γ → β → Obs (ForInStep β)) (a : γ → β → PrefixM LifetimeEvent (ForInStep β))
    (ha : ∀ x z, PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe (a x z))
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
      | done z => exact PrefixPreserves.pure (fun _ _ hi => hi.safe) z
      | yield z => exact PrefixPreserves.forIn xs z a (fun _ _ hi => hi.safe) ha

theorem projectsFocus_range (r : Std.Legacy.Range) (init : β)
    (g : Nat → β → Obs (ForInStep β)) (a : Nat → β → PrefixM LifetimeEvent (ForInStep β))
    (ha : ∀ x z, PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe (a x z))
    (hg : ∀ x z, ProjectsUnder AuditInv auditEvent (g x z) (auditFocus (a x z))) :
    ProjectsUnder AuditInv auditEvent (forIn r init g) (auditFocus (forIn r init a)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact projectsFocus_forIn _ init g a ha hg

theorem boundaryLift_kernel (a : Leanux.M α) (ha : SameProductStore a) :
    PrefixPreserves BoundaryInv BoundarySafe (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.productStore he) ha

def activationRun (a : Activation) : Obs Unit := do
  let occupancy ← mixed (activationOccupancyPrefix a)
  let refills ← mixed activationRefillsPrefix
  let mut act := a
  for _ in [0:occupancy + refills + 1] do
    match ← activationIteration act with
    | .ended => _ ← liftPrefix (hidden (.sectionStop act.worker)); return
    | .continued => act := {act with iterations := act.iterations + 1}
    | .yielded =>
      liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended ++ [{act with iterations := act.iterations + 1}]})
      return
  liftPrefix (invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) plus the refills its run could take ({refills})")

theorem activationRun_erases (a : Activation) :
    ErasesPrefix (activationRun a) (Env.Activation.run a) := by
  unfold activationRun Env.Activation.run
  repeat' first
    | with_reducible exact mixed_erases (activationRefillsPrefix_erases)
    | with_reducible exact mixed_erases (activationOccupancyPrefix_erases _)
    | with_reducible exact activationIteration_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationRun_preserves (a : Activation) :
    PrefixPreserves BoundaryInv BoundarySafe (activationRun a) := by
  unfold activationRun
  repeat' first
    | with_reducible exact mixed_preserves (activationRefillsPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient))
    | with_reducible exact mixed_preserves (activationOccupancyPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) _)
    | with_reducible exact activationIteration_preserves _
    | with_reducible exact boundaryLift_kernel _ (by intro initial; exact productAmbient_spec (AmbientM.hidden _) _ (fun _ _ hi => hi))
    | exact boundaryLift_kernel _ (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | exact boundaryLift_kernel _ (by intro initial; exact productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi))
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationRun_projects (a : Activation) :
    ProjectsUnder AuditInv auditEvent (activationRun a) (auditFocus (activationRunPrefix a)) := by
  have hm (f : Ambient → Ambient) :
      PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe
        (liftPrefix (modifyAmbient f)) :=
    ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient
      (fun _ => True) (modify f))
  unfold activationRun activationRunPrefix
  repeat' first
    | with_reducible exact mixed_projects (activationRefillsPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient))
    | with_reducible exact mixed_projects (activationOccupancyPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) _)
    | with_reducible exact activationIteration_projects _
    | with_reducible exact projectsFocus_lift _
    | with_reducible exact projectsFocus_pure _
    | with_reducible exact activationRefillsPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient)
    | with_reducible exact activationOccupancyPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) _
    | with_reducible exact activationIterPrefix_allocation _
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (AmbientM.hidden _))
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) _)
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply projectsFocus_range
    | with_reducible apply projectsFocus_bind
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals apply hm

def dispatch (worker : Worker) : Obs Bool := do
  let d ← liftPrefix (liftWG getDev)
  let mut pid : Option Nat := none
  match worker with
  | .encryptWorker => if !(← liftPrefix (Env.pendingDevice worker !d.encryptQueue.empty)) then return false
  | .decryptWorker => if !(← liftPrefix (Env.pendingDevice worker !d.decryptQueue.empty)) then return false
  | .receiveWorker => if !(← liftPrefix (Env.pendingDevice worker !d.handshakeQueue.empty)) then return false
  | .txWorker =>
    let some headPid := d.txWorkQueue.head? | return false
    let p ← match ← liftPrefix (peekUnit .txWorker) with
      | some u => liftPrefix (resolveUnit .txWorker u d.txWorkQueue)
      | none => pure headPid
    mixed (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase p})))
    pid := some p
  | _ => return false
  _ ← liftPrefix (hidden (.sectionStart worker))
  activationRun {worker, pid}
  return true

theorem dispatch_erases (worker : Worker) : ErasesPrefix (dispatch worker) (Env.dispatch worker) := by
  unfold dispatch Env.dispatch
  repeat' first
    | with_reducible exact activationRun_erases _
    | with_reducible exact mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _))
    | with_reducible exact mixed_erases (erasesPrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals first
    | exact erasesPrefix_lift _
    | exact mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _))

theorem dispatch_preserves (worker : Worker) : PrefixPreserves BoundaryInv BoundarySafe (dispatch worker) := by
  unfold dispatch
  apply PrefixPreserves.bind
    (boundaryLift_kernel _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  repeat' first
    | with_reducible exact boundaryLift_kernel _ (pendingDevice_sameKernel _ _)
    | with_reducible exact activationRun_preserves _
    | with_reducible exact mixed_preserves (txWorkQueueErase_allocation _).liftWGObserver.preserves
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
  all_goals
    simp only [hidden, peekUnit, resolveUnit]
    apply boundaryLift_kernel
    intro initial
    exact productAmbient_spec _ _ (fun _ _ hi => hi)

theorem dispatch_projects (worker : Worker) :
    ProjectsUnder AuditInv auditEvent (dispatch worker) (auditFocus (dispatchPrefix worker)) := by
  unfold dispatch dispatchPrefix
  apply projectsFocus_bind
    (by rw [liftWGObserver_lift]; exact projectsFocus_lift _)
    (ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).nativeStore
      (fun _ => True) getDev getDev_sameWGStore))
  all_goals
    intro d
    repeat' first
      | with_reducible exact activationRun_projects _
      | with_reducible exact mixed_projects (txWorkQueueErase_allocation _).liftWGObserver.preserves
      | with_reducible exact projectsFocus_lift _
      | with_reducible exact projectsFocus_pure _
      | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store (fun _ => True) _ (pendingDevice_sameKernel _ _))
      | with_reducible exact activationRunPrefix_allocation _
      | with_reducible exact (txWorkQueueErase_allocation _).liftWGObserver.preserves
      | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
      | with_reducible apply projectsFocus_bind
      | with_reducible apply PrefixPreserves.bind
      | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
      | (with_reducible intro x; try dsimp only)
  all_goals
    simp only [hidden, peekUnit, resolveUnit]
    apply ProductAmbientContracts.drop
    exact (ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) _

end Leanux.Proofs.WG.Queues.RxHistory
