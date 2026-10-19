import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendDrainPaths

/-! Exhaustive failures of the original send drain retain a successful literal
prefix and the actual failing operation. Exceptions are never assigned a
returned world. Delivery and budget failures remain distinct from worker calls. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal

structure LoopPath (w : World) (history : List Event) (u : World) (middle : List Event) where
  budget : Nat
  loopWorld : World
  loopHistory : List Event
  entered : runPrefix front w history = (.ok (some budget,loopWorld),loopHistory)
  done : List Nat
  index : Nat
  rest : List Nat
  shape : Scheduler.indices budget = done ++ index :: rest
  acc : LoopState
  leading : Scheduler.Yields step done (none,()) loopWorld loopHistory acc u middle

def LoopPath.worker (path : LoopPath w history u middle)
    (read : runPrefix (liftPrefix (liftWG getDev)) u middle = (.ok (device,v),last))
    (nonempty : device.sendWorkQueue.isEmpty = false) : WorkerPath w history v last :=
  ⟨path.budget,path.loopWorld,path.loopHistory,path.entered,path.done,path.index,path.rest,
    path.shape,path.acc,u,middle,path.leading,device,read,nonempty⟩

theorem LoopPath.carrier (path : LoopPath w history u middle)
    (before : CompleteProduct.Carrier history w) : CompleteProduct.Carrier middle u :=
  path.leading.carrier step_checked (Scheduler.checked_normal front_checked before path.entered)

inductive Failure (w : World) (history : List Event) (reason : Stop) (last : List Event) : Prop where
  | front (failed : runPrefix front w history = (.error reason,last)) : Failure w history reason last
  | read (path : LoopPath w history u middle)
      (failed : runPrefix (liftPrefix (liftWG getDev)) u middle = (.error reason,last)) :
      Failure w history reason last
  | delivery (path : LoopPath w history u middle)
      (read : runPrefix (liftPrefix (liftWG getDev)) u middle = (.ok (device,v),current))
      (empty : device.sendWorkQueue.isEmpty = true)
      (failed : runPrefix hooks.deliver v current = (.error reason,last)) : Failure w history reason last
  | worker (path : WorkerPath w history u middle)
      (failed : runPrefix (Driver.sendWorkerObserved hooks) u middle = (.error reason,last)) :
      Failure w history reason last
  | schedule (path : SchedulePath w history u middle)
      (failed : runPrefix (Driver.scheduleObserved hooks none) u middle = (.error reason,last)) :
      Failure w history reason last
  | finish (entered : runPrefix front w history = (.ok (some budget,u),middle))
      (loop : runPrefix (forIn (Scheduler.indices budget) (none,()) step) u middle = (.ok (acc,v),current))
      (failed : runPrefix (finish acc) v current = (.error reason,last)) : Failure w history reason last

theorem step_failed (path : LoopPath w history u middle)
    (failed : runPrefix (step path.index path.acc) u middle = (.error reason,last)) :
    Failure w history reason last := by
  rw [step,runPrefix_bind] at failed
  cases read : runPrefix (liftPrefix (liftWG getDev)) u middle with
  | mk result current =>
    rw [read] at failed
    cases result with
    | error error => cases failed; exact .read path read
    | ok out =>
      obtain ⟨device,v⟩ := out
      by_cases empty : device.sendWorkQueue.isEmpty = true
      · simp only [empty,↓reduceIte] at failed
        rw [runPrefix_bind] at failed
        cases delivered : runPrefix hooks.deliver v current with
        | mk result after =>
          rw [delivered] at failed
          cases result with
          | error error => cases failed; exact .delivery path read empty delivered
          | ok out => simp only [runPrefix_pure] at failed; cases failed
      · simp only [empty,Bool.false_eq_true,↓reduceIte] at failed
        rw [runPrefix_bind] at failed
        cases sent : runPrefix (Driver.sendWorkerObserved hooks) v current with
        | mk result after =>
          rw [sent] at failed
          cases result with
          | error error =>
            cases failed
            exact .worker (path.worker read (Bool.eq_false_iff.mpr empty)) sent
          | ok out =>
            obtain ⟨value,next⟩ := out
            cases value
            change runPrefix (Driver.scheduleObserved hooks none >>= fun _ =>
              pure (ForInStep.yield ((none,()) : LoopState))) next after = _ at failed
            rw [runPrefix_bind] at failed
            cases scheduled : runPrefix (Driver.scheduleObserved hooks none) next after with
            | mk result ending =>
              rw [scheduled] at failed
              cases result with
              | error error =>
                cases failed
                exact .schedule ⟨v,current,path.worker read (Bool.eq_false_iff.mpr empty),sent⟩ scheduled
              | ok out => simp only [runPrefix_pure] at failed; cases failed

/-- Every actual failed drain is classified at its real source operation after
an exact completed prefix; no completed enclosing caller is assumed. -/
theorem failed (stopped : runPrefix (Driver.sendWorkersObserved hooks) w history = (.error reason,last)) :
    Failure w history reason last := by
  rw [source_factor,runPrefix_bind] at stopped
  cases entered : runPrefix front w history with
  | mk result middle =>
    rw [entered] at stopped
    cases result with
    | error error => cases stopped; exact .front entered
    | ok out =>
      obtain ⟨budget,u⟩ := out
      cases budget with
      | none => simp only [afterFront,runPrefix_pure] at stopped; cases stopped
      | some budget =>
        change runPrefix (body budget) u middle = _ at stopped
        rw [body_list,runPrefix_bind] at stopped
        cases loop : runPrefix (forIn (Scheduler.indices budget) (none,()) step) u middle with
        | mk result current =>
          rw [loop] at stopped
          cases result with
          | error error =>
            cases stopped
            obtain ⟨done,index,rest,acc,v,before,shape,leading,failed⟩ :=
              Scheduler.loop_failed step (Scheduler.indices budget) (none,()) u middle loop
            exact step_failed ⟨budget,u,middle,entered,done,index,rest,shape,acc,leading⟩ failed
          | ok out =>
            obtain ⟨acc,v⟩ := out
            exact .finish entered loop stopped

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain
