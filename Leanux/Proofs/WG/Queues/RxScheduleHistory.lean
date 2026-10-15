import Leanux.Proofs.WG.Queues.RxActivationRunHistory
import Leanux.Proofs.WG.Lifetimes.BatchAudit

/-! The actual record-driven scheduler carries stamped committed polls beside
its existing consistency-filter probes. Trial executions remain on copied Worlds;
only their true filter-entry marker enters the committed audit stream. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- Group the source's hoisted getter with its copied-world filter. This is
only bind reassociation; the marker and every non-hidden Stop are retained. -/
private theorem filter_erases_bind {f : List Activation → Obs α} {b : List Activation → M α}
    (hf : ∀ xs, ErasesPrefix (f xs) (b xs)) :
    ErasesPrefix (audit consistentFilterAudit >>= f)
      (do let w ← get; let xs ← w.suspended.filterM Env.Activation.consistent; b xs) := by
  simpa only [bind_assoc] using erasesPrefix_bind (audit_erases consistentFilterAudit_erases) hf

def schedule (stack : Option Worker := none) : Obs Unit := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix get).hidden.isNone then
      let d ← liftPrefix getDev
      let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
        match w with
        | .receiveWorker => !d.handshakeQueue.empty
        | .decryptWorker => !d.decryptQueue.empty
        | .encryptWorker => !d.encryptQueue.empty
        | _ => !d.txWorkQueue.isEmpty
      let some w := next | return
      if !(← dispatch w) then liftPrefix (invariant s!"{w.symbol} has work but was not dispatched")
      continue
    let next ← liftPrefix peekHiddenSite
    if let some (w, true) := next.bind Env.sectionOf then
      if ← dispatch w then continue else return
    if ← mixed (pendingNapiPrefix next) then
      napiSoftirq
      if (← liftPrefix peekHiddenSite) == some netRx then return
      continue
    match ← audit consistentFilterAudit with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← mixed (activationHasWorkPrefix {worker := w}) then
          liftPrefix (unsupported "the records do not determine which suspended worker resumed")
      liftPrefix (modify fun s => {s with suspended := s.suspended.filter (· != a)})
      activationRun a
    | _ => liftPrefix (unsupported "the records do not determine which suspended worker resumed")
  liftPrefix (budgetExhausted "the scheduler loop")

theorem schedule_erases (stack : Option Worker) :
    ErasesPrefix (schedule stack) (Env.schedule stack) := by
  rw [← scheduleWithPending_eq]
  unfold schedule scheduleWithPending
  repeat' first
    | with_reducible exact dispatch_erases _
    | with_reducible exact activationRun_erases _
    | with_reducible exact napiSoftirq_erases
    | with_reducible exact mixed_erases (pendingNapiPrefix_erases _)
    | with_reducible exact mixed_erases (activationHasWorkPrefix_erases _)
    | with_reducible apply filter_erases_bind
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
  all_goals simp_all only [List.find?_cons, List.find?_nil]
  all_goals grind -matchEqs only [dispatch_erases, erasesPrefix_lift]

theorem schedule_preserves (stack : Option Worker) :
    PrefixPreserves BoundaryInv BoundarySafe (schedule stack) := by
  unfold schedule
  repeat' first
    | with_reducible exact dispatch_preserves _
    | with_reducible exact activationRun_preserves _
    | with_reducible exact napiSoftirq_preserves
    | with_reducible exact mixed_preserves (pendingNapiPrefix_preserves allocationAmbient _)
    | with_reducible exact mixed_preserves (activationHasWorkPrefix_preserves allocationAmbient allocationTx _)
    | with_reducible exact audit_preserves _ consistentFilterAudit_preserves
    | with_reducible exact boundaryLift_kernel _ getDev_sameKernel
    | with_reducible exact boundaryLift_kernel _ peekHiddenSite_sameKernel
    | with_reducible exact boundaryLift_kernel _ recordBudget_sameKernel
    | with_reducible exact boundaryLift_kernel _ (budgetExhausted_sameKernel _)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

/-- Project to the existing full audit, including exact probe payloads and
interleaving, rather than merely erasing probes to the lifetime-only scheduler. -/
theorem schedule_projects (stack : Option Worker) :
    ProjectsUnder AuditInv auditEvent (schedule stack) (scheduleAudit stack) := by
  unfold schedule scheduleAudit
  simp only [List.find?_cons, List.find?_nil]
  repeat' first
    | with_reducible exact dispatch_projects _
    | with_reducible exact activationRun_projects _
    | with_reducible exact napiSoftirq_projects
    | with_reducible exact mixed_projects (pendingNapiPrefix_preserves allocationAmbient _)
    | with_reducible exact mixed_projects (activationHasWorkPrefix_preserves allocationAmbient allocationTx _)
    | with_reducible exact audit_projects consistentFilterAudit_preserves
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact auditFocus_preserves (dispatchPrefix_allocation _)
    | with_reducible exact auditFocus_preserves (activationRunPrefix_allocation _)
    | with_reducible exact auditFocus_preserves napiSoftirqPrefix_allocation
    | with_reducible exact auditFocus_preserves (pendingNapiPrefix_preserves allocationAmbient _)
    | with_reducible exact auditFocus_preserves (activationHasWorkPrefix_preserves allocationAmbient allocationTx _)
    | with_reducible exact consistentFilterAudit_preserves
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ peekHiddenSite_sameKernel
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (budgetExhausted_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply projectsUnder_range
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def nestedResched (self : Worker) : Obs Unit := do
  if ← liftPrefix (Env.condResched self) then schedule (some self)

theorem nestedResched_erases (self : Worker) :
    ErasesPrefix (nestedResched self) (Env.nestedResched self) := by
  unfold nestedResched Env.nestedResched
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro b
  split
  · exact schedule_erases _
  · exact erasesPrefix_pure _

theorem nestedResched_preserves (self : Worker) :
    PrefixPreserves BoundaryInv BoundarySafe (nestedResched self) := by
  unfold nestedResched
  apply PrefixPreserves.bind (boundaryLift_kernel _ (condResched_sameKernel self))
  intro b
  split
  · exact schedule_preserves _
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _

theorem nestedResched_projects (self : Worker) :
    ProjectsUnder AuditInv auditEvent (nestedResched self) (nestedReschedAudit self) := by
  unfold nestedResched nestedReschedAudit
  apply projectsUnder_bind (projectsUnder_lift _ _) (auditLift_kernel _ (condResched_sameKernel self))
  intro b
  split
  · exact schedule_projects _
  · exact projectsUnder_pure _ _

/-- Every reached consistency-filter marker certifies its actual saved World
and lifetime history, including a filter or later callback that Stops. Candidate
trial histories remain separate from the committed entry journal. -/
theorem schedule_trials (stack : Option Worker) (w : World) (h : List Event)
    (hi : BoundaryInv h w) (p : ProbeEntry)
    (hp : p ∈ probeEntries (auditHistory (runPrefix (schedule stack) w h).2)) :
    AllocationInv p.history p.world ∧
    (p.world.suspended.filterM Env.Activation.consistent).run p.world =
      (p.world.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
        (fun ys => (ys, p.world)) ∧
    ∀ a ∈ p.world.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  have hs := (schedule_preserves stack w h hi).choose_spec.2.1
  exact savedProbe_trials hs.1.2 hp

end Leanux.Proofs.WG.Queues.RxHistory
