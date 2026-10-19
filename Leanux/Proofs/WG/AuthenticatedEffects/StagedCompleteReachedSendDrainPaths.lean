import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendDrainFrames

/-! Actual send-work and scheduler entry paths. The bounded loop prefix is
literal and consists only of completed yields; the next device read supplies
the native nonempty-queue guard, and the original suffix remains attached. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal

structure WorkerPath (w : World) (history : List Event) (u : World) (middle : List Event) where
  budget : Nat
  loopWorld : World
  loopHistory : List Event
  entered : runPrefix front w history = (.ok (some budget,loopWorld),loopHistory)
  done : List Nat
  index : Nat
  rest : List Nat
  shape : Scheduler.indices budget = done ++ index :: rest
  acc : LoopState
  beforeRead : World
  beforeHistory : List Event
  leading : Scheduler.Yields step done (none,()) loopWorld loopHistory acc beforeRead beforeHistory
  device : Device
  read : runPrefix (liftPrefix (liftWG getDev)) beforeRead beforeHistory = (.ok (device,u),middle)
  nonempty : device.sendWorkQueue.isEmpty = false

structure SchedulePath (w : World) (history : List Event) (u : World) (middle : List Event) where
  beforeSend : World
  beforeHistory : List Event
  worker : WorkerPath w history beforeSend beforeHistory
  sent : runPrefix (Driver.sendWorkerObserved hooks) beforeSend beforeHistory = (.ok ((),u),middle)

theorem WorkerPath.bound (path : WorkerPath w history u middle) : path.done.length < path.budget := by
  have length := congrArg List.length path.shape
  simp only [Scheduler.indices,List.length_range',List.length_append,List.length_cons] at length
  omega

theorem WorkerPath.carrier (path : WorkerPath w history u middle)
    (before : CompleteProduct.Carrier history w) : CompleteProduct.Carrier middle u :=
  Scheduler.checked_normal read_checked
    (path.leading.carrier step_checked (Scheduler.checked_normal front_checked before path.entered)) path.read

theorem WorkerPath.prefix (path : WorkerPath w history u middle) :
    runPrefix (workerEntryPrefix path.done.length) w history = (.ok (true,u),middle) := by
  rw [workerEntryPrefix,runPrefix_bind,path.entered]
  have taken : (Scheduler.indices path.budget).take path.done.length = path.done := by
    rw [path.shape]; simp
  change runPrefix (forIn ((Scheduler.indices path.budget).take path.done.length) (none,()) step >>= _) _ _ = _
  rw [taken,runPrefix_bind,path.leading.run]
  change runPrefix (liftPrefix (liftWG getDev) >>= _) _ _ = _
  rw [runPrefix_bind,path.read]
  simp only [runPrefix_pure,path.nonempty,Bool.not_false]

theorem WorkerPath.continuation (path : WorkerPath w history u middle) :
    runPrefix (Driver.sendWorkersObserved hooks) w history =
      runPrefix (do Driver.sendWorkerObserved hooks; Driver.scheduleObserved hooks none; remaining path.rest) u middle := by
  rw [source_factor,runPrefix_bind,path.entered]
  change runPrefix (body path.budget) path.loopWorld path.loopHistory = _
  rw [body_list,path.shape,path.leading.continue]
  rw [List.forIn_cons]
  simp only [step,bind_assoc]
  rw [runPrefix_bind,path.read]
  simp only [path.nonempty,Bool.false_eq_true,↓reduceIte,bind_assoc,pure_bind,remaining]

theorem SchedulePath.carrier (path : SchedulePath w history u middle)
    (before : CompleteProduct.Carrier history w) : CompleteProduct.Carrier middle u :=
  Scheduler.checked_normal CompleteProduct.scheduled_send (path.worker.carrier before) path.sent

theorem SchedulePath.prefix (path : SchedulePath w history u middle) :
    runPrefix (scheduleEntryPrefix path.worker.done.length) w history = (.ok (true,u),middle) := by
  rw [scheduleEntryPrefix,runPrefix_bind,path.worker.prefix]
  change runPrefix (Driver.sendWorkerObserved hooks >>= fun _ => pure true) _ _ = _
  rw [runPrefix_bind,path.sent]
  rfl

theorem SchedulePath.continuation (path : SchedulePath w history u middle) :
    runPrefix (Driver.sendWorkersObserved hooks) w history =
      runPrefix (Driver.scheduleObserved hooks none >>= fun _ => remaining path.worker.rest) u middle := by
  rw [path.worker.continuation,runPrefix_bind,path.sent]

/-- The actual worker-entry world carries the complete fixed-ticket account. -/
theorem WorkerPath.accounted (path : WorkerPath w history u middle)
    (before : CompleteProduct.Carrier history w) :
    ∃ ledger, CompleteCarrier.Accounted middle ledger [] [] u.wg := (path.carrier before).1

/-- The actual scheduler-entry world carries the complete fixed-ticket account. -/
theorem SchedulePath.accounted (path : SchedulePath w history u middle)
    (before : CompleteProduct.Carrier history w) :
    ∃ ledger, CompleteCarrier.Accounted middle ledger [] [] u.wg := (path.carrier before).1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain
