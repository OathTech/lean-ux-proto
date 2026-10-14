import Leanux.Proofs.WG.Lifetimes.Audit
import Leanux.Proofs.WG.Lifetimes.BatchTrials

/-! The actual scheduler's consistency-filter entries, beside its committed
accesses. Activation.run uses plain condResched callbacks, not nestedResched;
its speculative observer therefore needs no recursive audit stream. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

/-- One marker per reached filter invocation, including an empty candidate list
or a filter that stops. The original filter still executes on the same World. -/
def consistentFilterAudit : AuditM (List Activation) := do
  markProbe
  liftPrefix ((← liftPrefix get).suspended.filterM Env.Activation.consistent)

@[simp] theorem consistentFilterAudit_run (w : World) (h : List AuditEvent) :
    runPrefix consistentFilterAudit w h =
      ((w.suspended.filterM Env.Activation.consistent).run w,
        h ++ [.probe ⟨w, lifetimeHistory h⟩]) := rfl

theorem consistentFilterAudit_erases : ErasesPrefix consistentFilterAudit
    (do (← get).suspended.filterM Env.Activation.consistent) := fun _ _ => rfl

theorem consistentFilterAudit_preserves : PrefixPreserves AuditInv AuditSafe consistentFilterAudit := by
  unfold consistentFilterAudit
  apply PrefixPreserves.bind markProbe_preserves
  intro _
  apply PrefixPreserves.bind (auditLift_kernel get (by intro w x v hr; cases hr; rfl))
  intro w
  exact auditLift_kernel _ (filterM_sameKernel _ activationConsistent_sameKernel _)

theorem consistentFilterAudit_projects : ProjectsUnder AllocationInv AuditEvent.lifetime?
    consistentFilterAudit (do liftPrefix ((← liftPrefix get).suspended.filterM Env.Activation.consistent)) := by
  unfold consistentFilterAudit
  apply markProbe_projects_bind
  apply projectsUnder_bind (projectsUnder_lift _ get)
    (allocation_kernel get (by intro w x v hr; cases hr; rfl))
  intro w
  exact projectsUnder_lift _ _

def scheduleAudit (stack : Option Worker := none) : AuditM Unit := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix get).hidden.isNone then
      let d ← liftPrefix getDev
      let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
        match w with
        | .receiveWorker => !d.handshakeQueue.isEmpty
        | .decryptWorker => !d.decryptQueue.empty
        | .encryptWorker => !d.encryptQueue.empty
        | _ => !d.txWorkQueue.isEmpty
      let some w := next | return
      if !(← auditFocus (dispatchPrefix w)) then liftPrefix (invariant s!"{w.symbol} has work but was not dispatched")
      continue
    let next ← liftPrefix peekHiddenSite
    if let some (w, true) := next.bind Env.sectionOf then
      if ← auditFocus (dispatchPrefix w) then continue else return
    if ← auditFocus (pendingNapiPrefix next) then
      auditFocus napiSoftirqPrefix
      if (← liftPrefix peekHiddenSite) == some netRx then return
      continue
    match ← consistentFilterAudit with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← auditFocus (activationHasWorkPrefix {worker := w}) then
          liftPrefix (unsupported "the records do not determine which suspended worker resumed")
      liftPrefix (modify fun s => {s with suspended := s.suspended.filter (· != a)})
      auditFocus (activationRunPrefix a)
    | _ => liftPrefix (unsupported "the records do not determine which suspended worker resumed")
  liftPrefix (budgetExhausted "the scheduler loop")


theorem scheduleAudit_erases (stack : Option Worker) : ErasesPrefix (scheduleAudit stack) (Env.schedule stack) := by
  rw [← scheduleWithPending_eq]
  unfold scheduleAudit scheduleWithPending consistentFilterAudit
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact auditFocus_erases (dispatchPrefix_erases _)
    | with_reducible exact auditFocus_erases napiSoftirqPrefix_erases
    | with_reducible exact auditFocus_erases (activationHasWorkPrefix_erases _)
    | with_reducible exact auditFocus_erases (activationRunPrefix_erases _)
    | with_reducible exact auditFocus_erases (pendingNapiPrefix_erases _)
    | with_reducible apply erasesPrefix_bind_pure markProbe_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  -- Avoid realizing shared matcher congruence auxiliaries independently of
  -- SourceScheduler: normalize this fixed worker list before ordinary congruence.
  all_goals simp_all only [List.find?_cons, List.find?_nil]
  all_goals grind -matchEqs only [auditFocus_erases, dispatchPrefix_erases, erasesPrefix_lift]

theorem scheduleAudit_preserves (stack : Option Worker) :
    PrefixPreserves AuditInv AuditSafe (scheduleAudit stack) := by
  unfold scheduleAudit
  repeat' first
    | with_reducible exact consistentFilterAudit_preserves
    | with_reducible exact auditFocus_preserves (dispatchPrefix_allocation _)
    | with_reducible exact auditFocus_preserves napiSoftirqPrefix_allocation
    | with_reducible exact auditFocus_preserves (activationHasWorkPrefix_preserves allocationAmbient allocationTx _)
    | with_reducible exact auditFocus_preserves (activationRunPrefix_allocation _)
    | with_reducible exact auditFocus_preserves (pendingNapiPrefix_preserves allocationAmbient _)
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ peekHiddenSite_sameKernel
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (budgetExhausted_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem scheduleAudit_projects (stack : Option Worker) :
    ProjectsUnder AllocationInv AuditEvent.lifetime? (scheduleAudit stack) (schedulePrefix stack) := by
  unfold scheduleAudit schedulePrefix consistentFilterAudit
  simp only [bind_assoc]
  repeat' first
    | with_reducible apply markProbe_projects_bind
    | with_reducible exact auditFocus_projects (dispatchPrefix_allocation _)
    | with_reducible exact auditFocus_projects napiSoftirqPrefix_allocation
    | with_reducible exact auditFocus_projects (activationHasWorkPrefix_preserves allocationAmbient allocationTx _)
    | with_reducible exact auditFocus_projects (activationRunPrefix_allocation _)
    | with_reducible exact auditFocus_projects (pendingNapiPrefix_preserves allocationAmbient _)
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact dispatchPrefix_allocation _
    | with_reducible exact napiSoftirqPrefix_allocation
    | with_reducible exact activationHasWorkPrefix_preserves allocationAmbient allocationTx _
    | with_reducible exact activationRunPrefix_allocation _
    | with_reducible exact pendingNapiPrefix_preserves allocationAmbient _
    | with_reducible exact allocation_kernel _ getDev_sameKernel
    | with_reducible exact allocation_kernel _ peekHiddenSite_sameKernel
    | with_reducible exact allocation_kernel _ recordBudget_sameKernel
    | with_reducible exact allocation_kernel _ (budgetExhausted_sameKernel _)
    | with_reducible exact allocation_kernel _ (filterM_sameKernel _ activationConsistent_sameKernel _)
    | exact allocation_kernel _ (by intro w x v hr; cases hr; rfl)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | exact allocation_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible apply projectsUnder_range
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.range _ _ _ allocationAmbient.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals simp_all only [List.find?_cons, List.find?_nil]
  all_goals grind -matchEqs only [auditFocus_projects, dispatchPrefix_allocation, projectsUnder_lift]

def nestedReschedAudit (self : Worker) : AuditM Unit := do
  if ← liftPrefix (Env.condResched self) then scheduleAudit (some self)

theorem nestedReschedAudit_erases (self : Worker) :
    ErasesPrefix (nestedReschedAudit self) (Env.nestedResched self) := by
  unfold nestedReschedAudit Env.nestedResched
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun b => by
    split
    · exact scheduleAudit_erases _
    · exact erasesPrefix_pure _)

theorem nestedReschedAudit_preserves (self : Worker) :
    PrefixPreserves AuditInv AuditSafe (nestedReschedAudit self) := by
  unfold nestedReschedAudit
  apply PrefixPreserves.bind (auditLift_kernel _ (condResched_sameKernel self))
  intro b
  split
  · exact scheduleAudit_preserves _
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _

theorem nestedReschedAudit_projects (self : Worker) :
    ProjectsUnder AllocationInv AuditEvent.lifetime? (nestedReschedAudit self) (nestedReschedPrefix self) := by
  unfold nestedReschedAudit nestedReschedPrefix
  apply projectsUnder_bind (projectsUnder_lift _ _) (allocation_kernel _ (condResched_sameKernel self))
  intro b
  split
  · exact scheduleAudit_projects _
  · exact projectsUnder_pure _ _

/-- The original receive worker's generic loop, with focused receive steps and
an audit-aware callback; the callback still runs only after an item was handled. -/
def handshakeReceiveWorkerAudit (afterItem : AuditM Unit) : AuditM Unit :=
  workerLoopPrefix .receiveWorker none (auditFocus receiveStepPrefix) afterItem
    MAX_QUEUED_INCOMING_HANDSHAKES "the handshake queue did not drain"

theorem handshakeReceiveWorkerAudit_erases (he : ErasesPrefix afterItem originalAfter) :
    ErasesPrefix (handshakeReceiveWorkerAudit afterItem) (handshakeReceiveWorker originalAfter) :=
  workerLoopPrefix_erases _ _ (auditFocus_erases receiveStepPrefix_erases) he _ _

theorem handshakeReceiveWorkerAudit_preserves (ha : PrefixPreserves AuditInv AuditSafe afterItem) :
    PrefixPreserves AuditInv AuditSafe (handshakeReceiveWorkerAudit afterItem) :=
  workerLoopPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    (auditFocus_preserves (HandshakeReceiveCall.allocation .step)) ha _ _

theorem handshakeReceiveWorkerAudit_projects
    (ha : PrefixPreserves AllocationInv LifetimeEvent.Safe afterPrefix)
    (hp : ProjectsUnder AllocationInv AuditEvent.lifetime? afterItem afterPrefix) :
    ProjectsUnder AllocationInv AuditEvent.lifetime?
      (handshakeReceiveWorkerAudit afterItem) (handshakeReceiveWorkerPrefix afterPrefix) := by
  have hs : PrefixPreserves AllocationInv LifetimeEvent.Safe receiveStepPrefix :=
    HandshakeReceiveCall.allocation .step
  have hsproj := auditFocus_projects hs
  unfold handshakeReceiveWorkerAudit handshakeReceiveWorkerPrefix workerLoopPrefix workerIterPrefix
  repeat' first
    | with_reducible exact hsproj
    | with_reducible exact hs
    | with_reducible exact hp
    | with_reducible exact ha
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | exact allocation_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible apply projectsUnder_range
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.range _ _ _ allocationAmbient.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

/-- Each recorded entry supplies its own invariant to every candidate trial.
The exact filter equality describes which prefix was evaluated; safety of the
remaining candidates does not assert that they ran. -/
theorem savedProbe_trials (hs : AllProbeValid h) (hp : p ∈ probeEntries h) :
    AllocationInv p.history p.world ∧
    (p.world.suspended.filterM Env.Activation.consistent).run p.world =
      (p.world.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
        (fun ys => (ys, p.world)) ∧
    ∀ a ∈ p.world.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 :=
  ⟨hs p hp, activationTrials_filter _ _ _, activationTrials_safe _ _ _ (hs p hp)⟩

/-- Concrete scheduler boundaries through which future callers carry audit facts. -/
inductive BatchAuditCall where
  | filter
  | schedule (stack : Option Worker)
  | nestedResched (worker : Worker)
  | receiveWorker

namespace BatchAuditCall

def Result : BatchAuditCall → Type
  | .filter => List Activation
  | _ => Unit

def original : (call : BatchAuditCall) → M call.Result
  | .filter => do (← get).suspended.filterM Env.Activation.consistent
  | .schedule stack => Env.schedule stack
  | .nestedResched worker => Env.nestedResched worker
  | .receiveWorker => handshakeReceiveWorker (Env.nestedResched .receiveWorker)

def committed : (call : BatchAuditCall) → MixedM call.Result
  | .filter => do liftPrefix ((← liftPrefix get).suspended.filterM Env.Activation.consistent)
  | .schedule stack => schedulePrefix stack
  | .nestedResched worker => nestedReschedPrefix worker
  | .receiveWorker => handshakeReceiveWorkerPrefix (nestedReschedPrefix .receiveWorker)

def observed : (call : BatchAuditCall) → AuditM call.Result
  | .filter => consistentFilterAudit
  | .schedule stack => scheduleAudit stack
  | .nestedResched worker => nestedReschedAudit worker
  | .receiveWorker => handshakeReceiveWorkerAudit (nestedReschedAudit .receiveWorker)

theorem erases (call : BatchAuditCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | filter => exact consistentFilterAudit_erases
  | schedule stack => exact scheduleAudit_erases stack
  | nestedResched worker => exact nestedReschedAudit_erases worker
  | receiveWorker => exact handshakeReceiveWorkerAudit_erases (nestedReschedAudit_erases .receiveWorker)

theorem preserves (call : BatchAuditCall) : PrefixPreserves AuditInv AuditSafe call.observed := by
  cases call with
  | filter => exact consistentFilterAudit_preserves
  | schedule stack => exact scheduleAudit_preserves stack
  | nestedResched worker => exact nestedReschedAudit_preserves worker
  | receiveWorker => exact handshakeReceiveWorkerAudit_preserves (nestedReschedAudit_preserves .receiveWorker)

theorem projects (call : BatchAuditCall) :
    ProjectsUnder AllocationInv AuditEvent.lifetime? call.observed call.committed := by
  cases call with
  | filter => exact consistentFilterAudit_projects
  | schedule stack => exact scheduleAudit_projects stack
  | nestedResched worker => exact nestedReschedAudit_projects worker
  | receiveWorker =>
    exact handshakeReceiveWorkerAudit_projects
      (nestedReschedPrefix_allocation .receiveWorker) (nestedReschedAudit_projects .receiveWorker)

/-- Empty observation history discharges all pre-existing marker obligations.
This is a local allocation-valid entry theorem, not initialized Runner closure. -/
theorem from_allocation (call : BatchAuditCall) (w : World) (hi : AllocationInv [] w) :
    AuditSafe (runPrefix call.observed w []).2 ∧
    ∀ p ∈ probeEntries (runPrefix call.observed w []).2,
      AllocationInv p.history p.world ∧
      (p.world.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  have hs := (call.preserves w [] (audit_initial hi)).choose_spec.2.1
  exact ⟨hs, fun p hp => savedProbe_trials hs.2 hp⟩

end BatchAuditCall

end Leanux.Proofs.WG.Lifetimes
