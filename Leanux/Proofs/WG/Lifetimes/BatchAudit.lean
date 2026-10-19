import Leanux.Proofs.WG.Lifetimes.Audit
import Leanux.Proofs.WG.Lifetimes.BatchTrials

/-! The actual scheduler's consistency-filter entries, beside its committed
accesses. Activation.run uses plain condResched callbacks, not nestedResched;
its speculative observer therefore needs no recursive audit stream. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

/-- One marker per reached filter invocation, including an empty candidate list
or a filter that stops. The original filter still executes on the same World. -/
def consistentFilterAudit : AuditM (List Activation) := do
  markProbe
  liftPrefix ((← liftPrefix getAmbient).suspended.filterM Env.Activation.consistent)

@[simp] theorem consistentFilterAudit_run (w : World) (h : List AuditEvent) :
    runPrefix consistentFilterAudit w h =
      ((w.ambient.suspended.filterM Env.Activation.consistent).run w,
        h ++ [.probe ⟨w, lifetimeHistory h⟩]) := rfl

theorem consistentFilterAudit_erases : ErasesPrefix consistentFilterAudit
    (do (← getAmbient).suspended.filterM Env.Activation.consistent) := fun _ _ => rfl

theorem consistentFilterAudit_preserves : PrefixPreserves AuditInv AuditSafe consistentFilterAudit := by
  unfold consistentFilterAudit
  apply PrefixPreserves.bind markProbe_preserves
  intro _
  apply PrefixPreserves.bind (auditLift_store getAmbient (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
  intro w
  exact auditLift_store _ ((filterM_sameKernel productStoreView _ activationConsistent_sameKernel _).of_factor (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl))

theorem consistentFilterAudit_projects : ProjectsUnder (fun h w => AllocationInv h w.wg) AuditEvent.lifetime?
    consistentFilterAudit (do liftPrefix ((← liftPrefix getAmbient).suspended.filterM Env.Activation.consistent)) := by
  unfold consistentFilterAudit
  apply markProbe_projects_bind
  apply projectsUnder_bind (projectsUnder_lift _ getAmbient)
    (allocation_store World.wg getAmbient (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
  intro w
  exact projectsUnder_lift _ _

def scheduleAudit (stack : Option Worker := none) : AuditM Unit := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix getAmbient).hidden.isNone then
      let d ← liftPrefix (liftWG getDev)
      let pending := (← liftPrefix getAmbient).pendingWork
      let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
        match w with
        | .receiveWorker => !d.handshakeQueue.empty || pending.contains w.index
        | .decryptWorker => !d.decryptQueue.empty || pending.contains w.index
        | .encryptWorker => !d.encryptQueue.empty || pending.contains w.index
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
      liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended.filter (· != a)})
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
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals first
    | exact erasesPrefix_lift _
    | (simp only [List.find?_cons, List.find?_nil] at *
       grind -matchEqs only [auditFocus_erases, dispatchPrefix_erases, erasesPrefix_lift])

/-- Select only the current observer head before attempting a composition rule. -/
elab "audit_contract_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  let action ←
    if ty.isAppOf ``PrefixPreserves then
      if args.size > 0 then pure args.back! else Lean.throwError "missing observer"
    else if ty.isAppOf ``PrefixEnsures || ty.isAppOf ``ProjectsUnder then
      if args.size ≥ 2 then pure args[args.size - 2]! else Lean.throwError "missing observer"
    else Lean.throwError "not an audit contract"
  let mut action := action.consumeMData
  let expected := name.getId.eraseMacroScopes.toString
  if expected == "markProbe" && action.isAppOf ``Bind.bind then
    let bound := action.getAppArgs
    unless bound.size ≥ 2 do Lean.throwError "missing bind action"
    action := bound[bound.size - 2]!.consumeMData
  if action.isAppOf ``auditFocus then
    let focused := action.getAppArgs
    unless focused.size > 0 do Lean.throwError "missing focused observer"
    action := focused.back!.consumeMData
  if expected != "liftPrefix" && action.isAppOf ``liftPrefix then
    let lifted := action.getAppArgs
    unless lifted.size > 0 do Lean.throwError "missing lifted action"
    action := lifted.back!.consumeMData
  let .const actual _ := action.getAppFn
    | Lean.throwError "not a constant-headed observer"
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different audit observer head"

elab "audit_contract " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let .const actual _ := ty.getAppFn | Lean.throwError "not a named audit contract"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different audit contract"

theorem scheduleAudit_preserves (stack : Option Worker) :
    PrefixPreserves AuditInv AuditSafe (scheduleAudit stack) := by
  apply PrefixEnsures.preserves
  unfold scheduleAudit
  repeat' first
    | (audit_contract_head consistentFilterAudit; exact consistentFilterAudit_preserves)
    | (audit_contract_head dispatchPrefix; exact auditFocus_preserves (dispatchPrefix_allocation _))
    | (audit_contract_head napiSoftirqPrefix; exact auditFocus_preserves napiSoftirqPrefix_allocation)
    | (audit_contract_head activationHasWorkPrefix; exact auditFocus_preserves (activationHasWorkPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) (ProductTxContracts.ofNative allocationTx) _))
    | (audit_contract_head activationRunPrefix; exact auditFocus_preserves (activationRunPrefix_allocation _))
    | (audit_contract_head pendingNapiPrefix; exact auditFocus_preserves (pendingNapiPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) _))
    | (audit_contract_head liftPrefix; first
        | exact auditLift_store _ (sameView_liftWG (fun w => wgStoreView w.wg) wgStoreView getDev getDev_sameWGStore (fun _ _ _ hi => hi))
        | exact auditLift_store _ (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))
        | exact auditLift_store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
    | (audit_contract_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
    | (audit_contract_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
        (I := fun _ h w => AuditInv h w) (hs := fun _ _ _ hi => hi.safe))
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

theorem scheduleAudit_projects (stack : Option Worker) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) AuditEvent.lifetime? (scheduleAudit stack) (schedulePrefix stack) := by
  unfold scheduleAudit schedulePrefix consistentFilterAudit
  simp only [bind_assoc, liftWGObserver_lift]
  repeat' first
    | (audit_contract ProjectsUnder; first
        | (audit_contract_head markProbe; apply markProbe_projects_bind)
        | (audit_contract_head dispatchPrefix; exact auditFocus_projects (dispatchPrefix_allocation _))
        | (audit_contract_head napiSoftirqPrefix; exact auditFocus_projects napiSoftirqPrefix_allocation)
        | (audit_contract_head activationHasWorkPrefix; exact auditFocus_projects (activationHasWorkPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) (ProductTxContracts.ofNative allocationTx) _))
        | (audit_contract_head activationRunPrefix; exact auditFocus_projects (activationRunPrefix_allocation _))
        | (audit_contract_head pendingNapiPrefix; exact auditFocus_projects (pendingNapiPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) _))
        | (audit_contract_head liftPrefix; exact projectsUnder_lift _ _)
        | (audit_contract_head Pure.pure; exact projectsUnder_pure _ _)
        | (audit_contract_head ForIn.forIn; apply projectsUnder_range)
        | (audit_contract_head Bind.bind; apply projectsUnder_bind))
    | (audit_contract PrefixPreserves; first
        | (audit_contract_head dispatchPrefix; exact dispatchPrefix_allocation _)
        | (audit_contract_head napiSoftirqPrefix; exact napiSoftirqPrefix_allocation)
        | (audit_contract_head activationHasWorkPrefix; exact activationHasWorkPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) (ProductTxContracts.ofNative allocationTx) _)
        | (audit_contract_head activationRunPrefix; exact activationRunPrefix_allocation _)
        | (audit_contract_head pendingNapiPrefix; exact pendingNapiPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) _)
        | (audit_contract_head liftWG; exact allocation_store World.wg _ (sameView_liftWG (fun w => wgStoreView w.wg) wgStoreView getDev getDev_sameWGStore (fun _ _ _ hi => hi)))
        | (first
            | audit_contract_head getAmbient
            | audit_contract_head modifyAmbient
            | audit_contract_head peekHiddenSite
            | audit_contract_head recordBudget
            | audit_contract_head budgetExhausted
            | audit_contract_head invariant
            | audit_contract_head unsupported
           exact allocation_store World.wg _ (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
        | (audit_contract_head List.filterM; exact allocation_store World.wg _ ((filterM_sameKernel productStoreView _ activationConsistent_sameKernel _).of_factor (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl)))
        | (audit_contract_head Pure.pure; exact PrefixPreserves.pure (ProductAmbientContracts.ofNative allocationAmbient).safe _)
        | (audit_contract_head ForIn.forIn; apply PrefixPreserves.range (State := World) _ _ _ (ProductAmbientContracts.ofNative allocationAmbient).safe)
        | (audit_contract_head Bind.bind; apply PrefixPreserves.bind))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)
  all_goals
    simp only [List.find?_cons, List.find?_nil] at *
    grind -matchEqs only [auditFocus_projects, dispatchPrefix_allocation, projectsUnder_lift]

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
  apply PrefixPreserves.bind (auditLift_store _ ((condResched_sameKernel self).of_factor (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl)))
  intro b
  split
  · exact scheduleAudit_preserves _
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _

theorem nestedReschedAudit_projects (self : Worker) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) AuditEvent.lifetime? (nestedReschedAudit self) (nestedReschedPrefix self) := by
  unfold nestedReschedAudit nestedReschedPrefix
  apply projectsUnder_bind (projectsUnder_lift _ _) (allocation_store World.wg _ ((condResched_sameKernel self).of_factor (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl)))
  intro b
  split
  · exact scheduleAudit_projects _
  · exact projectsUnder_pure _ _

/-- The original receive worker's generic loop, with focused receive steps and
an audit-aware callback; the callback still runs only after an item was handled. -/
def handshakeReceiveWorkerAudit (afterItem : AuditM Unit) : AuditM Unit :=
  workerLoopPrefix .receiveWorker none (auditFocus (liftWGObserver receiveStepPrefix)) afterItem
    (MAX_QUEUED_INCOMING_HANDSHAKES + 1) "the handshake queue did not drain"

theorem handshakeReceiveWorkerAudit_erases (he : ErasesPrefix afterItem originalAfter) :
    ErasesPrefix (handshakeReceiveWorkerAudit afterItem) (handshakeReceiveWorker originalAfter) :=
  workerLoopPrefix_erases _ _ (auditFocus_erases (liftWGObserver_erases receiveStepPrefix_erases)) he _ _

theorem handshakeReceiveWorkerAudit_preserves (ha : PrefixPreserves AuditInv AuditSafe afterItem) :
    PrefixPreserves AuditInv AuditSafe (handshakeReceiveWorkerAudit afterItem) :=
  workerLoopPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    (auditFocus_preserves ((HandshakeReceiveCall.allocation .step).liftWGObserver)) ha _ _

theorem handshakeReceiveWorkerAudit_projects
    (ha : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe afterPrefix)
    (hp : ProjectsUnder (fun h w => AllocationInv h w.wg) AuditEvent.lifetime? afterItem afterPrefix) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) AuditEvent.lifetime?
      (handshakeReceiveWorkerAudit afterItem) (handshakeReceiveWorkerPrefix afterPrefix) := by
  have hs : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (liftWGObserver receiveStepPrefix) :=
    (HandshakeReceiveCall.allocation .step).liftWGObserver
  have hsproj := auditFocus_projects hs
  unfold handshakeReceiveWorkerAudit handshakeReceiveWorkerPrefix workerLoopPrefix workerIterPrefix
  repeat' first
    | with_reducible exact hsproj
    | with_reducible exact hs
    | with_reducible exact hp
    | with_reducible exact ha
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact PrefixPreserves.pure (ProductAmbientContracts.ofNative allocationAmbient).safe _
    | exact allocation_store World.wg _ (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | with_reducible apply projectsUnder_range
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.range _ _ _ (ProductAmbientContracts.ofNative allocationAmbient).safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

/-- Each recorded entry supplies its own invariant to every candidate trial.
The exact filter equality describes which prefix was evaluated; safety of the
remaining candidates does not assert that they ran. -/
theorem savedProbe_trials (hs : AllProbeValid h) (hp : p ∈ probeEntries h) :
    AllocationInv p.history p.world.wg ∧
    (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
      (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
        (fun ys => (ys, p.world)) ∧
    ∀ a ∈ p.world.ambient.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 :=
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

def original : (call : BatchAuditCall) → Leanux.M call.Result
  | .filter => do (← getAmbient).suspended.filterM Env.Activation.consistent
  | .schedule stack => Env.schedule stack
  | .nestedResched worker => Env.nestedResched worker
  | .receiveWorker => handshakeReceiveWorker (Env.nestedResched .receiveWorker)

def committed : (call : BatchAuditCall) → PrefixM LifetimeEvent call.Result
  | .filter => do liftPrefix ((← liftPrefix getAmbient).suspended.filterM Env.Activation.consistent)
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
    ProjectsUnder (fun h w => AllocationInv h w.wg) AuditEvent.lifetime? call.observed call.committed := by
  cases call with
  | filter => exact consistentFilterAudit_projects
  | schedule stack => exact scheduleAudit_projects stack
  | nestedResched worker => exact nestedReschedAudit_projects worker
  | receiveWorker =>
    exact handshakeReceiveWorkerAudit_projects
      (nestedReschedPrefix_allocation .receiveWorker) (nestedReschedAudit_projects .receiveWorker)

/-- Empty observation history discharges all pre-existing marker obligations.
This is a local allocation-valid entry theorem, not initialized Runner closure. -/
theorem from_allocation (call : BatchAuditCall) (w : World) (hi : AllocationInv [] w.wg) :
    AuditSafe (runPrefix call.observed w []).2 ∧
    ∀ p ∈ probeEntries (runPrefix call.observed w []).2,
      AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  have hs := (call.preserves w [] (audit_initial hi)).choose_spec.2.1
  exact ⟨hs, fun p hp => savedProbe_trials hs.2 hp⟩

end BatchAuditCall

end Leanux.Proofs.WG.Lifetimes
