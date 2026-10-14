import Leanux.Proofs.WG.Lifetimes.BatchActivation

/-! Committed scheduler observations and separately certified copied-World
trials. Trial histories are never appended to committed histories. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem txWorkQueueErase_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid})) :=
  txWorkQueue_allocation (fun q => q.erase pid)

def dispatchPrefix (worker : Worker) : MixedM Bool := do
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
    liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase p})
    pid := some p
  | _ => return false
  _ ← liftPrefix (hidden (.sectionStart worker))
  activationRunPrefix {worker, pid}
  return true

theorem dispatchPrefix_erases (worker : Worker) : ErasesPrefix (dispatchPrefix worker) (Env.dispatch worker) := by
  unfold dispatchPrefix Env.dispatch
  repeat' first
    | with_reducible exact activationRunPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem dispatchPrefix_allocation (worker : Worker) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (dispatchPrefix worker) := by
  unfold dispatchPrefix
  repeat' first
    | with_reducible exact activationRunPrefix_allocation _
    | with_reducible exact txWorkQueueErase_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (peekUnit_sameKernel _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (resolveUnit_sameKernel _ _ _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (hidden_sameKernel _))
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

/-- Keep the eager getDev even when `next` is not NET_RX. The saved-map
predicate itself is demanded only by the Bool.and right-hand side. -/
def pendingNapi (next : Option Nat) : M Bool := do
  let d ← getDev
  return next == some (HiddenSite.sectionStart .netRx).info.id && d.peers.toList.any (·.2.napiScheduled)

def pendingNapiPrefix (next : Option Nat) : MixedM Bool := do
  let d ← liftPrefix getDev
  if next == some (HiddenSite.sectionStart .netRx).info.id then
    savedPeerAny (·.napiScheduled) d.peers.toList
  else pure false

theorem pendingNapiPrefix_erases (next : Option Nat) :
    ErasesPrefix (pendingNapiPrefix next) (pendingNapi next) := by
  unfold pendingNapiPrefix pendingNapi
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro d
  cases ht : (next == some (HiddenSite.sectionStart .netRx).info.id) <;>
    simp only [ht, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.true_and]
  · exact erasesPrefix_pure _
  · exact savedPeerAny_erases (·.napiScheduled) d.peers.toList

theorem pendingNapiPrefix_preserves (c : AmbientContracts I) (next : Option Nat) :
    PrefixPreserves I LifetimeEvent.Safe (pendingNapiPrefix next) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  unfold pendingNapiPrefix
  apply PrefixEnsures.bind (getDev_saved_spec c (fun _ => True))
  intro d
  split
  · exact savedPeerAny_spec c (fun _ => True) (·.napiScheduled) d.peers.toList
  · exact (c.pure (fun s => True ∧ SavedPeers d.peers.toList s) false).consequence
      (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, True.intro⟩)

def schedulePrefix (stack : Option Worker := none) : MixedM Unit := do
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
      if !(← dispatchPrefix w) then liftPrefix (invariant s!"{w.symbol} has work but was not dispatched")
      continue
    let next ← liftPrefix peekHiddenSite
    if let some (w, true) := next.bind Env.sectionOf then
      if ← dispatchPrefix w then continue else return
    if ← pendingNapiPrefix next then
      napiSoftirqPrefix
      if (← liftPrefix peekHiddenSite) == some netRx then return
      continue
    match ← liftPrefix ((← liftPrefix get).suspended.filterM Env.Activation.consistent) with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← activationHasWorkPrefix {worker := w} then
          liftPrefix (unsupported "the records do not determine which suspended worker resumed")
      liftPrefix (modify fun s => {s with suspended := s.suspended.filter (· != a)})
      activationRunPrefix a
    | _ => liftPrefix (unsupported "the records do not determine which suspended worker resumed")
  liftPrefix (budgetExhausted "the scheduler loop")

open Leanux.Env in
def scheduleWithPending (stack : Option Worker := none) : M Unit := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  -- record-driven (review item 7): every turn consumes a record (a section
  -- start, a NET_RX section, a resumption's records) or returns; without
  -- records the filter's bound
  for _ in [0:(← recordBudget)] do
    if (← get).hidden.isNone then
      let d ← getDev
      let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
        match w with
        | .receiveWorker => !d.handshakeQueue.isEmpty
        | .decryptWorker => !d.decryptQueue.empty
        | .encryptWorker => !d.encryptQueue.empty
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
    match ← (← get).suspended.filterM Activation.consistent with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← Activation.hasWork { worker := w } then
          unsupported "the records do not determine which suspended worker resumed"
      modify fun s => { s with suspended := s.suspended.filter (· != a) }
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
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
  all_goals grind only [dispatchPrefix_erases, erasesPrefix_lift]

theorem schedulePrefix_allocation (stack : Option Worker) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (schedulePrefix stack) := by
  unfold schedulePrefix
  repeat' first
    | with_reducible exact dispatchPrefix_allocation _
    | with_reducible exact napiSoftirqPrefix_allocation
    | with_reducible exact activationHasWorkPrefix_preserves allocationAmbient allocationTx _
    | with_reducible exact activationRunPrefix_allocation _
    | with_reducible exact pendingNapiPrefix_preserves allocationAmbient _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ peekHiddenSite_sameKernel)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ recordBudget_sameKernel)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (budgetExhausted_sameKernel _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _
        (filterM_sameKernel _ activationConsistent_sameKernel _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (by intro w x v hr; cases hr; rfl))
    | exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (by intro w x v hr; cases hr))
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.range _ _ _ allocationAmbient.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def nestedReschedPrefix (self : Worker) : MixedM Unit := do
  if ← liftPrefix (Env.condResched self) then schedulePrefix (some self)

theorem nestedReschedPrefix_erases (self : Worker) :
    ErasesPrefix (nestedReschedPrefix self) (Env.nestedResched self) := by
  unfold nestedReschedPrefix Env.nestedResched
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun b => by
    split
    · exact schedulePrefix_erases _
    · exact erasesPrefix_pure _)

theorem nestedReschedPrefix_allocation (self : Worker) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (nestedReschedPrefix self) := by
  unfold nestedReschedPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (allocationAmbient.kernel _ _ (condResched_sameKernel self)))
  intro b
  split
  · exact schedulePrefix_allocation _
  · exact PrefixPreserves.pure allocationAmbient.safe _

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
