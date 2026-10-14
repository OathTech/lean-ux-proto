import Leanux.Proofs.WG.Lifetimes.BatchScheduler

/-! A callback-parameterized copy of the original scheduler control flow.
Only committed activation/NAPI calls use the supplied observers. Consistency
trials execute the original action on its copied World and emit no events. -/
set_option maxHeartbeats 2000000
namespace Leanux.Proofs.WG.Queues.SourceScheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
variable {Event : Type}

private theorem invariant_kernel (why : String) : SameKernel (invariant (α := α) why) := by
  intro w x v hr
  cases hr

theorem occupancy_kernel (a : Activation) : SameKernel (Env.Activation.occupancy a) :=
  activationOccupancy_sameKernel a

theorem hasWork_kernel (a : Activation) : SameKernel (Env.Activation.hasWork a) :=
  activationHasWork_sameKernel a

theorem pendingNapi_kernel (next : Option Nat) : SameKernel (Lifetimes.pendingNapi next) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Lifetimes.pendingNapi, getDev, getK, invariant]

def run (iteration : Activation → PrefixM Event IterResult) (a : Activation) : PrefixM Event Unit := do
  let occupancy ← liftPrefix (Env.Activation.occupancy a)
  let mut act := a
  for _ in [0:occupancy + 1] do
    match ← iteration act with
    | .ended => _ ← liftPrefix (hidden (.sectionStop act.worker)); return
    | .continued => act := {act with iterations := act.iterations + 1}
    | .yielded =>
      liftPrefix (modify fun s => {s with suspended := s.suspended ++ [{act with iterations := act.iterations + 1}]})
      return
  liftPrefix (invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) in one run")

def dispatch (iteration : Activation → PrefixM Event IterResult) (worker : Worker) : PrefixM Event Bool := do
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
  run iteration {worker, pid}
  return true

def schedule (iteration : Activation → PrefixM Event IterResult) (napi : PrefixM Event Unit) (stack : Option Worker := none) : PrefixM Event Unit := do
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
      if !(← dispatch iteration w) then liftPrefix (invariant s!"{w.symbol} has work but was not dispatched")
      continue
    let next ← liftPrefix peekHiddenSite
    if let some (w, true) := next.bind Env.sectionOf then
      if ← dispatch iteration w then continue else return
    if ← liftPrefix (Lifetimes.pendingNapi next) then
      napi
      if (← liftPrefix peekHiddenSite) == some netRx then return
      continue
    match ← liftPrefix ((← liftPrefix get).suspended.filterM Env.Activation.consistent) with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← liftPrefix (Env.Activation.hasWork {worker := w}) then
          liftPrefix (unsupported "the records do not determine which suspended worker resumed")
      liftPrefix (modify fun s => {s with suspended := s.suspended.filter (· != a)})
      run iteration a
    | _ => liftPrefix (unsupported "the records do not determine which suspended worker resumed")
  liftPrefix (budgetExhausted "the scheduler loop")

theorem run_erases (iteration : Activation → PrefixM Event IterResult)
    (hi : ∀ a, ErasesPrefix (iteration a) (Env.Activation.iter a)) (a : Activation) :
    ErasesPrefix (run iteration a) (Env.Activation.run a) := by
  unfold run Env.Activation.run
  repeat' first
    | with_reducible exact hi _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem dispatch_erases (iteration : Activation → PrefixM Event IterResult)
    (hi : ∀ a, ErasesPrefix (iteration a) (Env.Activation.iter a)) (worker : Worker) :
    ErasesPrefix (dispatch iteration worker) (Env.dispatch worker) := by
  unfold dispatch Env.dispatch
  repeat' first
    | with_reducible exact run_erases iteration hi _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem schedule_erases (iteration : Activation → PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (hi : ∀ a, ErasesPrefix (iteration a) (Env.Activation.iter a))
    (hn : ErasesPrefix napi Env.napiSoftirq) (stack : Option Worker) :
    ErasesPrefix (schedule iteration napi stack) (Env.schedule stack) := by
  rw [← Lifetimes.scheduleWithPending_eq]
  unfold schedule Lifetimes.scheduleWithPending
  repeat' first
    | with_reducible exact dispatch_erases iteration hi _
    | with_reducible exact run_erases iteration hi _
    | with_reducible exact hn
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
  all_goals grind only [dispatch_erases, erasesPrefix_lift]

variable {I : List Event → World → Prop} {S : List Event → Prop}

theorem run_preserves (hs : ∀ h w, I h w → S h)
    (hk : ∀ h w v, v.k = w.k → I h w → I h v)
    (iteration : Activation → PrefixM Event IterResult)
    (hi : ∀ a, PrefixPreserves I S (iteration a)) (a : Activation) :
    PrefixPreserves I S (run iteration a) := by
  unfold run
  repeat' first
    | with_reducible exact hi _
    | with_reducible exact kernelLiftPrefix_preserves hs hk (occupancy_kernel _)
    | with_reducible exact kernelLiftPrefix_preserves hs hk (hidden_sameKernel _)
    | with_reducible exact kernelLiftPrefix_preserves hs hk (invariant_kernel _)
    | exact kernelLiftPrefix_preserves hs hk (by intro w x v hr; cases hr; rfl)
    | with_reducible exact PrefixPreserves.pure hs _
    | with_reducible apply PrefixPreserves.range _ _ _ hs
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem dispatch_preserves (hs : ∀ h w, I h w → S h)
    (hk : ∀ h w v, v.k = w.k → I h w → I h v)
    (he : ∀ pid, PrefixPreserves I S (liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid})))
    (iteration : Activation → PrefixM Event IterResult)
    (hi : ∀ a, PrefixPreserves I S (iteration a)) (worker : Worker) :
    PrefixPreserves I S (dispatch iteration worker) := by
  unfold dispatch
  repeat' first
    | with_reducible exact run_preserves hs hk iteration hi _
    | with_reducible exact he _
    | with_reducible exact kernelLiftPrefix_preserves hs hk Lifetimes.getDev_sameKernel
    | with_reducible exact kernelLiftPrefix_preserves hs hk (peekUnit_sameKernel _)
    | with_reducible exact kernelLiftPrefix_preserves hs hk (resolveUnit_sameKernel _ _ _)
    | with_reducible exact kernelLiftPrefix_preserves hs hk (hidden_sameKernel _)
    | with_reducible exact PrefixPreserves.pure hs _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem schedule_preserves (hs : ∀ h w, I h w → S h)
    (hk : ∀ h w v, v.k = w.k → I h w → I h v)
    (he : ∀ pid, PrefixPreserves I S (liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid})))
    (iteration : Activation → PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (hi : ∀ a, PrefixPreserves I S (iteration a)) (hn : PrefixPreserves I S napi) (stack : Option Worker) :
    PrefixPreserves I S (schedule iteration napi stack) := by
  unfold schedule
  repeat' first
    | with_reducible exact dispatch_preserves hs hk he iteration hi _
    | with_reducible exact run_preserves hs hk iteration hi _
    | with_reducible exact hn
    | with_reducible exact kernelLiftPrefix_preserves hs hk Lifetimes.getDev_sameKernel
    | with_reducible exact kernelLiftPrefix_preserves hs hk (pendingNapi_kernel _)
    | with_reducible exact kernelLiftPrefix_preserves hs hk (hasWork_kernel _)
    | with_reducible exact kernelLiftPrefix_preserves hs hk peekHiddenSite_sameKernel
    | with_reducible exact kernelLiftPrefix_preserves hs hk recordBudget_sameKernel
    | with_reducible exact kernelLiftPrefix_preserves hs hk (budgetExhausted_sameKernel _)
    | with_reducible exact kernelLiftPrefix_preserves hs hk (filterM_sameKernel _ activationConsistent_sameKernel _)
    | with_reducible exact kernelLiftPrefix_preserves hs hk (invariant_kernel _)
    | exact kernelLiftPrefix_preserves hs hk (by intro w x v hr; cases hr; rfl)
    | exact kernelLiftPrefix_preserves hs hk (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure hs _
    | with_reducible apply PrefixPreserves.range _ _ _ hs
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Queues.SourceScheduler
