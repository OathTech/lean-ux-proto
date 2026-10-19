import Leanux.Proofs.WG.Lifetimes.BatchActivation

/-! Committed scheduler observations and separately certified copied-World
trials. Trial histories are never appended to committed histories. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem txWorkQueueErase_allocation (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid})) :=
  txWorkQueue_allocation (fun q => q.erase pid)

def dispatchPrefix (worker : Worker) : PrefixM LifetimeEvent Bool := do
  let d ← liftWGObserver (liftWGPrefix getDev)
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
    liftWGObserver (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase p}))
    pid := some p
  | _ => return false
  _ ← liftPrefix (hidden (.sectionStart worker))
  activationRunPrefix {worker, pid}
  return true

theorem dispatchPrefix_erases (worker : Worker) : ErasesPrefix (dispatchPrefix worker) (Env.dispatch worker) := by
  unfold dispatchPrefix Env.dispatch
  repeat' first
    | with_reducible exact activationRunPrefix_erases _
    | with_reducible exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals exact liftWGObserver_erases (erasesStatePrefix_lift _)

theorem dispatchPrefix_allocation (worker : Worker) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (dispatchPrefix worker) := by
  unfold dispatchPrefix
  repeat' first
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store (fun _ => True) _ (pendingDevice_sameKernel _ _))
    | with_reducible exact activationRunPrefix_allocation _
    | with_reducible exact (txWorkQueueErase_allocation _).liftWGObserver
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).nativeStore (fun _ => True) getDev getDev_sameWGStore)
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (AmbientM.peekUnit _))
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (AmbientM.resolveUnit _ _ _))
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (AmbientM.hidden _))
    | with_reducible exact PrefixPreserves.pure (ProductAmbientContracts.ofNative allocationAmbient).safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals first
    | exact (txWorkQueueErase_allocation _).liftWGObserver
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).nativeStore (fun _ => True) getDev getDev_sameWGStore)
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (AmbientM.peekUnit _))
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (AmbientM.resolveUnit _ _ _))
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (AmbientM.hidden _))

/-- Keep the eager getDev even when `next` is not NET_RX. The saved-map
predicate itself is demanded only by the Bool.and right-hand side. -/
def pendingNapi (next : Option Nat) : Leanux.M Bool := do
  let d ← getDev
  return next == some (HiddenSite.sectionStart .netRx).info.id && d.peers.toList.any (·.2.napiScheduled)

def pendingNapiPrefix (next : Option Nat) : PrefixM LifetimeEvent Bool := do
  let d ← liftWGObserver (liftWGPrefix getDev)
  if next == some (HiddenSite.sectionStart .netRx).info.id then
    liftWGObserver (savedPeerAny (·.napiScheduled) d.peers.toList)
  else pure false

theorem pendingNapiPrefix_erases (next : Option Nat) :
    ErasesPrefix (pendingNapiPrefix next) (pendingNapi next) := by
  unfold pendingNapiPrefix pendingNapi
  apply erasesPrefix_bind (liftWGObserver_erases (erasesStatePrefix_lift _))
  intro d
  cases ht : (next == some (HiddenSite.sectionStart .netRx).info.id) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.true_and]
  · exact erasesPrefix_pure _
  · exact liftWGObserver_erases (savedPeerAny_erases (·.napiScheduled) d.peers.toList)

theorem pendingNapiPrefix_preserves (c : ProductAmbientContracts I) (next : Option Nat) :
    PrefixPreserves I LifetimeEvent.Safe (pendingNapiPrefix next) := by
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  unfold pendingNapiPrefix
  apply PrefixEnsures.bind (getDev_saved_spec_product c (fun _ => True))
  intro d
  split
  · exact savedPeerAny_spec_product c (fun _ => True) (·.napiScheduled) d.peers.toList
  · exact (c.pure (fun s => True ∧ SavedPeers d.peers.toList s) false).consequence
      (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, True.intro⟩)

def schedulePrefix (stack : Option Worker := none) : PrefixM LifetimeEvent Unit := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix getAmbient).hidden.isNone then
      let d ← liftWGObserver (liftWGPrefix getDev)
      let pending := (← liftPrefix getAmbient).pendingWork
      let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
        match w with
        | .receiveWorker => !d.handshakeQueue.empty || pending.contains w.index
        | .decryptWorker => !d.decryptQueue.empty || pending.contains w.index
        | .encryptWorker => !d.encryptQueue.empty || pending.contains w.index
        | _ => !d.txWorkQueue.isEmpty
      let some w := next | return
      if !(← dispatchPrefix w) then liftPrefix (invariant s!"{w.symbol} has work but was not dispatched")
      continue
    let next ← liftPrefix peekHiddenSite
    if let some (w, true) := next.bind Env.sectionOf then
      if ← dispatchPrefix w then continue else return
    if ← pendingNapiPrefix next then
      napiSoftirqPrefix
      if (← liftPrefix peekHiddenSite) == some netRx then return
      continue
    match ← liftPrefix ((← liftPrefix getAmbient).suspended.filterM Env.Activation.consistent) with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← activationHasWorkPrefix {worker := w} then
          liftPrefix (unsupported "the records do not determine which suspended worker resumed")
      liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended.filter (· != a)})
      activationRunPrefix a
    | _ => liftPrefix (unsupported "the records do not determine which suspended worker resumed")
  liftPrefix (budgetExhausted "the scheduler loop")

open Leanux.Env in
def scheduleWithPending (stack : Option Worker := none) : Leanux.M Unit := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  -- record-driven (review item 7): every turn consumes a record (a section
  -- start, a NET_RX section, a resumption's records) or returns; without
  -- records the filter's bound
  for _ in [0:(← recordBudget)] do
    if (← getAmbient).hidden.isNone then
      let d ← getDev
      let pending := (← getAmbient).pendingWork
      let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
        match w with
        | .receiveWorker => !d.handshakeQueue.empty || pending.contains w.index
        | .decryptWorker => !d.decryptQueue.empty || pending.contains w.index
        | .encryptWorker => !d.encryptQueue.empty || pending.contains w.index
        | _ => !d.txWorkQueue.isEmpty
      let some w := next | return
      if !(← Env.dispatch w) then invariant s!"{w.symbol} has work but was not dispatched"
      continue
    let next ← peekHiddenSite
    if let some (w, true) := next.bind sectionOf then
      if ← Env.dispatch w then continue else return
    if ← pendingNapi next then
      napiSoftirq
      if (← peekHiddenSite) == some netRx then return   -- left to the caller
      continue
    match ← (← getAmbient).suspended.filterM Activation.consistent with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← Activation.hasWork { worker := w } then
          unsupported "the records do not determine which suspended worker resumed"
      modifyAmbient fun s => { s with suspended := s.suspended.filter (· != a) }
      Activation.run a
    | _ => unsupported "the records do not determine which suspended worker resumed"
  budgetExhausted "the scheduler loop"

theorem scheduleWithPending_eq (stack : Option Worker) :
    scheduleWithPending stack = Env.schedule stack := by
  simp only [scheduleWithPending, Env.schedule, pendingNapi, bind_assoc, pure_bind]
  congr 1

theorem schedulePrefix_erases (stack : Option Worker) :
    ErasesPrefix (schedulePrefix stack) (Env.schedule stack) := by
  rw [← scheduleWithPending_eq]
  unfold schedulePrefix scheduleWithPending
  repeat' first
    | with_reducible exact dispatchPrefix_erases _
    | with_reducible exact napiSoftirqPrefix_erases
    | with_reducible exact activationHasWorkPrefix_erases _
    | with_reducible exact activationRunPrefix_erases _
    | with_reducible exact pendingNapiPrefix_erases _
    | with_reducible exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
  all_goals first
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | grind only [dispatchPrefix_erases, erasesPrefix_lift]

elab "batch_lift_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "not an observer contract"
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``liftPrefix do Lean.throwError "not a product lift"
  let .const actual _ := action.getAppArgs.back!.consumeMData.getAppFn
    | Lean.throwError "not a constant-headed product action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different product action head"

theorem schedulePrefix_allocation (stack : Option Worker) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (schedulePrefix stack) := by
  let c := ProductAmbientContracts.ofNative allocationAmbient
  apply PrefixEnsures.preserves
  unfold schedulePrefix
  repeat' first
    | (maintenance_head dispatchPrefix; exact dispatchPrefix_allocation _)
    | (maintenance_head napiSoftirqPrefix; exact napiSoftirqPrefix_allocation)
    | (maintenance_head activationHasWorkPrefix; exact activationHasWorkPrefix_preserves c (ProductTxContracts.ofNative allocationTx) _)
    | (maintenance_head activationRunPrefix; exact activationRunPrefix_allocation _)
    | (maintenance_head pendingNapiPrefix; exact pendingNapiPrefix_preserves c _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) getDev getDev_sameWGStore))
    | (batch_lift_head peekHiddenSite; exact ProductAmbientContracts.drop (c.ambient (fun _ => True) AmbientM.peekHiddenSite))
    | (batch_lift_head recordBudget; exact ProductAmbientContracts.drop (c.ambient (fun _ => True) AmbientM.recordBudget))
    | (batch_lift_head budgetExhausted; exact ProductAmbientContracts.drop (c.ambient (fun _ => True) (AmbientM.budgetExhausted _)))
    | (batch_lift_head unsupported; exact ProductAmbientContracts.drop (c.ambient (fun _ => True) (AmbientM.unsupported _)))
    | (batch_lift_head invariant; exact ProductAmbientContracts.drop (c.invariant (fun _ => True) _))
    | (batch_lift_head List.filterM; exact ProductAmbientContracts.drop (c.store (fun _ => True) _ (filterM_sameKernel productStoreView _ activationConsistent_sameKernel _)))
    | (first | batch_lift_head getAmbient | batch_lift_head modifyAmbient
       exact ProductAmbientContracts.drop (c.store (fun _ => True) _ (by
         apply (ProjectedAction.iff_run _ _ _).mpr
         intro w x v hr
         cases hr
         rfl)))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
        (I := fun _ h w => AllocationInv h w.wg) (hs := fun _ _ _ hi => hi.safe))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AllocationInv h w.wg))
    | maintenance_reduce
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (maintenance_intro; try dsimp only)

def nestedReschedPrefix (self : Worker) : PrefixM LifetimeEvent Unit := do
  if ← liftPrefix (Env.condResched self) then schedulePrefix (some self)

theorem nestedReschedPrefix_erases (self : Worker) :
    ErasesPrefix (nestedReschedPrefix self) (Env.nestedResched self) := by
  unfold nestedReschedPrefix Env.nestedResched
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun b => by
    split
    · exact schedulePrefix_erases _
    · exact erasesPrefix_pure _)

theorem nestedReschedPrefix_allocation (self : Worker) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (nestedReschedPrefix self) := by
  unfold nestedReschedPrefix
  apply PrefixPreserves.bind (ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store _ _ (condResched_sameKernel self)))
  intro b
  split
  · exact schedulePrefix_allocation _
  · exact PrefixPreserves.pure (ProductAmbientContracts.ofNative allocationAmbient).safe _

/-- The original consistency decision agrees with the separately observed trial,
while preserving the caller's World and history. Hidden mismatch means false;
other Stops propagate. -/
theorem activationConsistent_trial (a : Activation) (w : World) (h : List LifetimeEvent) :
    runPrefix (liftPrefix (Env.Activation.consistent a)) w h =
      ((match (runPrefix (activationRunPrefix a) w h).1 with
        | .ok _ => .ok (true, w)
        | .error (.hidden _) => .ok (false, w)
        | .error e => .error e), h) := by
  rw [activationRunPrefix_erases a w h]
  simp only [runPrefix_lift, Env.Activation.consistent, StateT.run_bind, StateT.run_get, pure_bind]
  cases (Env.Activation.run a).run w with
  | ok out => rfl
  | error e => cases e <;> rfl

end Leanux.Proofs.WG.Lifetimes
