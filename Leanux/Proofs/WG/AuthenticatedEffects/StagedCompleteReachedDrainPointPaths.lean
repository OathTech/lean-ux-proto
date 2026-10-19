import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainPointSource

/-! Literal prefixes and remaining original source for every drain boundary.
Only finitely named source continuations occur here; no user-chosen action can
be declared a cut by supplying a monadic factorization. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal

def frontPrefix : FrontStage → PrefixM Event Bool
  | .entry => pure true
  | .read => do _ ← frontRead; return true
  | .checked => do
      let saved ← frontRead
      if saved.dev.isNone then return false
      frontCheck
      return true
  | .reset => do
      let saved ← frontRead
      if saved.dev.isNone then return false
      frontCheck
      frontReset
      return true
  | .budget => do
      let saved ← frontRead
      if saved.dev.isNone then return false
      frontCheck
      frontReset
      _ ← frontBudget
      return true

inductive FrontSuffix where
  | entry
  | read (saved : WGWorld)
  | checked
  | reset
  | budget (value : Nat)

def FrontSuffix.stage : FrontSuffix → FrontStage
  | .entry => .entry
  | .read _ => .read
  | .checked => .checked
  | .reset => .reset
  | .budget _ => .budget

def FrontSuffix.action : FrontSuffix → PrefixM Event Unit
  | .entry => Driver.sendWorkersObserved hooks
  | .read saved => afterRead saved >>= afterFront
  | .checked => do frontReset; let budget ← frontBudget; afterFront (some budget)
  | .reset => do let budget ← frontBudget; afterFront (some budget)
  | .budget count => afterFront (some count)

theorem FrontPoint.prefix (point : FrontPoint w history stage u middle) :
    runPrefix (frontPrefix stage) w history = (.ok (true,u),middle) := by
  cases point <;> simp only [frontPrefix,runPrefix_bind,runPrefix_pure, *]
  all_goals simp only [Bool.false_eq_true,↓reduceIte,runPrefix_bind,runPrefix_pure, *]

/-- Every front point has a fixed remaining source, even if that remainder
later stops; no successful enclosing drain is assumed. -/
theorem FrontPoint.continuation (point : FrontPoint w history stage u middle) :
    ∃ tail : FrontSuffix, tail.stage = stage ∧
      runPrefix (Driver.sendWorkersObserved hooks) w history = runPrefix tail.action u middle := by
  cases point with
  | entry => exact ⟨.entry,rfl,rfl⟩
  | read performed =>
      rename_i saved
      refine ⟨.read saved,rfl,?_⟩
      rw [source_factor,front_factor,bind_assoc,runPrefix_bind,performed]
      rfl
  | checked read present performed =>
      refine ⟨.checked,rfl,?_⟩
      rw [source_factor,front_factor,bind_assoc,runPrefix_bind,read]
      simp only [afterRead,present,Bool.false_eq_true,↓reduceIte,bind_assoc,runPrefix_bind,performed,
        FrontSuffix.action,runPrefix_pure]
  | reset read present checked performed =>
      refine ⟨.reset,rfl,?_⟩
      rw [source_factor,front_factor,bind_assoc,runPrefix_bind,read]
      simp only [afterRead,present,Bool.false_eq_true,↓reduceIte,bind_assoc,runPrefix_bind,checked,performed,
        FrontSuffix.action,runPrefix_pure]
  | budget read present checked reset performed =>
      rename_i count
      refine ⟨.budget count,rfl,?_⟩
      rw [source_factor,front_factor,bind_assoc,runPrefix_bind,read]
      simp only [afterRead,present,Bool.false_eq_true,↓reduceIte,bind_assoc,runPrefix_bind,checked,reset,performed,
        FrontSuffix.action,runPrefix_pure]

structure DeliveryPath (w : World) (history : History) (u : World) (middle : History) where
  beforeRead : World
  beforeHistory : History
  loop : LoopPath w history beforeRead beforeHistory
  device : Device
  read : runPrefix (liftPrefix (liftWG getDev)) beforeRead beforeHistory = (.ok (device,u),middle)
  empty : device.sendWorkQueue.isEmpty = true

def deliveryEntryPrefix (count : Nat) : PrefixM Event Bool := do
  let some _ ← loopEntryPrefix count | return false
  return (← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty

theorem DeliveryPath.prefix (path : DeliveryPath w history u middle) :
    runPrefix (deliveryEntryPrefix path.loop.done.length) w history = (.ok (true,u),middle) := by
  rw [deliveryEntryPrefix,runPrefix_bind,path.loop.prefix]
  change runPrefix (liftPrefix (liftWG getDev) >>= _) _ _ = _
  rw [runPrefix_bind,path.read]
  simp only [runPrefix_pure,path.empty]

theorem DeliveryPath.continuation (path : DeliveryPath w history u middle) :
    runPrefix (Driver.sendWorkersObserved hooks) w history =
      runPrefix (hooks.deliver >>= fun _ => pure ()) u middle := by
  rw [path.loop.continuation]
  simp only [step,bind_assoc]
  rw [runPrefix_bind,path.read]
  simp only [path.empty,↓reduceIte,bind_assoc,pure_bind,afterStep,finish]

inductive ChildEntry (w : World) (history : History) : Child → World → History → Type where
  | delivery (path : DeliveryPath w history u middle) : ChildEntry w history .delivery u middle
  | worker (path : WorkerPath w history u middle) : ChildEntry w history .worker u middle
  | scheduler (path : SchedulePath w history u middle) : ChildEntry w history .scheduler u middle

def ChildEntry.count (path : ChildEntry w history child u middle) : Nat :=
  match path with
  | .delivery path => path.loop.done.length
  | .worker path => path.done.length
  | .scheduler path => path.worker.done.length

def childEntryPrefix : Child → Nat → PrefixM Event Bool
  | .delivery => deliveryEntryPrefix
  | .worker => workerEntryPrefix
  | .scheduler => scheduleEntryPrefix

def ChildEntry.after (path : ChildEntry w history child u middle) : PrefixM Event Unit :=
  match path with
  | .delivery _ => pure ()
  | .worker path => do Driver.scheduleObserved hooks none; remaining path.rest
  | .scheduler path => remaining path.worker.rest

theorem ChildEntry.prefix (path : ChildEntry w history child u middle) :
    runPrefix (childEntryPrefix child path.count) w history = (.ok (true,u),middle) := by
  cases path with
  | delivery path => exact path.prefix
  | worker path => exact path.prefix
  | scheduler path => exact path.prefix

theorem ChildEntry.continuation (path : ChildEntry w history child u middle) :
    runPrefix (Driver.sendWorkersObserved hooks) w history =
      runPrefix (child.action >>= fun _ => path.after) u middle := by
  cases path with
  | delivery path => exact path.continuation
  | worker path => exact path.continuation
  | scheduler path => exact path.continuation

theorem ChildEntry.return_continuation (path : ChildEntry w history child u middle)
    (returned : runPrefix child.action u middle = (.ok ((),v),last)) :
    runPrefix (Driver.sendWorkersObserved hooks) w history = runPrefix path.after v last := by
  rw [path.continuation,runPrefix_bind,returned]

structure FinishPath (w : World) (history : History) (acc : LoopState) (u : World) (middle : History) where
  budget : Nat
  beforeLoop : World
  beforeHistory : History
  front : runPrefix SendDrain.front w history = (.ok (some budget,beforeLoop),beforeHistory)
  loop : runPrefix (forIn (Scheduler.indices budget) (none,()) step) beforeLoop beforeHistory =
    (.ok (acc,u),middle)

def finishEntryPrefix : PrefixM Event (Option LoopState) := do
  let some budget ← front | return none
  return some (← forIn (Scheduler.indices budget) (none,()) step)

theorem FinishPath.prefix (path : FinishPath w history acc u middle) :
    runPrefix finishEntryPrefix w history = (.ok (some acc,u),middle) := by
  rw [finishEntryPrefix,runPrefix_bind,path.front]
  change runPrefix (forIn (Scheduler.indices path.budget) (none,()) step >>= _) _ _ = _
  rw [runPrefix_bind,path.loop]
  rfl

theorem FinishPath.continuation (path : FinishPath w history acc u middle) :
    runPrefix (Driver.sendWorkersObserved hooks) w history = runPrefix (finish acc) u middle := by
  rw [source_factor,runPrefix_bind,path.front]
  change runPrefix (body path.budget) _ _ = _
  rw [body_list,runPrefix_bind,path.loop]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
