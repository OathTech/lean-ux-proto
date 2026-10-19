import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendDrainCases

/-! The real entry of an earlier failed drain operation is also exposed by a
fixed original loop prefix. Failure never supplies a synthetic post-world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal

def loopEntryPrefix (count : Nat) : PrefixM Event (Option LoopState) := do
  let some budget ← front | return none
  let acc ← forIn ((Scheduler.indices budget).take count) (none,()) step
  return some acc

def afterStep (rest : List Nat) (decision : ForInStep LoopState) : PrefixM Event Unit := do
  let acc ← match decision with
    | .done acc => pure acc
    | .yield acc => forIn rest acc step
  finish acc

theorem LoopPath.bound (path : LoopPath w history u middle) : path.done.length < path.budget := by
  have length := congrArg List.length path.shape
  simp only [Scheduler.indices,List.length_range',List.length_append,List.length_cons] at length
  omega

theorem LoopPath.prefix (path : LoopPath w history u middle) :
    runPrefix (loopEntryPrefix path.done.length) w history = (.ok (some path.acc,u),middle) := by
  rw [loopEntryPrefix,runPrefix_bind,path.entered]
  have taken : (Scheduler.indices path.budget).take path.done.length = path.done := by
    rw [path.shape]; simp
  change runPrefix (forIn ((Scheduler.indices path.budget).take path.done.length) (none,()) step >>= _) _ _ = _
  rw [taken,runPrefix_bind,path.leading.run]
  rfl

theorem LoopPath.continuation (path : LoopPath w history u middle) :
    runPrefix (Driver.sendWorkersObserved hooks) w history =
      runPrefix (step path.index path.acc >>= afterStep path.rest) u middle := by
  change _ = runPrefix (step path.index path.acc >>= fun decision => afterStep path.rest decision) u middle
  rw [source_factor,runPrefix_bind,path.entered]
  change runPrefix (body path.budget) path.loopWorld path.loopHistory = _
  rw [body_list,path.shape,path.leading.continue,List.forIn_cons]
  simp only [bind_assoc,afterStep]
  apply congrArg (fun action : PrefixM Event Unit => runPrefix action u middle)
  apply congrArg (fun next => step path.index path.acc >>= next)
  funext decision
  cases decision <;> rfl

theorem front_stopped
    (stopped : runPrefix front w history = (.error reason,last)) :
    runPrefix (Driver.sendWorkersObserved hooks) w history = (.error reason,last) := by
  rw [source_factor,runPrefix_bind,stopped]

theorem front_absent
    (absent : runPrefix front w history = (.ok (none,u),middle)) :
    runPrefix (Driver.sendWorkersObserved hooks) w history = (.ok ((),u),middle) := by
  rw [source_factor,runPrefix_bind,absent]
  rfl

theorem WorkerPath.failed (path : WorkerPath w history u middle)
    (stopped : runPrefix (Driver.sendWorkerObserved hooks) u middle = (.error reason,last)) :
    runPrefix (Driver.sendWorkersObserved hooks) w history = (.error reason,last) := by
  rw [path.continuation,runPrefix_bind,stopped]

theorem SchedulePath.failed (path : SchedulePath w history u middle)
    (stopped : runPrefix (Driver.scheduleObserved hooks none) u middle = (.error reason,last)) :
    runPrefix (Driver.sendWorkersObserved hooks) w history = (.error reason,last) := by
  rw [path.continuation,runPrefix_bind,stopped]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain
