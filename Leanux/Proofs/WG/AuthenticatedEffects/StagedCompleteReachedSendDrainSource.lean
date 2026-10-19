import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerIteration
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductWork
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeferredFrames

/-! Fixed source cuts in the send-work drain. The no-device guard, native
crypt-work check, queuedThisCall reset and recorded budget remain in their
original order. Each loop iteration either delivers or runs send then schedule. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal
abbrev LoopState := Option Unit × Unit

def front : PrefixM Event (Option Nat) := do
  if (← liftPrefix getWG).dev.isNone then return none
  liftPrefix Env.requireNoCryptWork
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  return some (← liftPrefix recordBudget)

def step (_ : Nat) (_ : LoopState) : PrefixM Event (ForInStep LoopState) := do
  if (← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then
    hooks.deliver
    return .done (some (),())
  Driver.sendWorkerObserved hooks
  Driver.scheduleObserved hooks none
  return .yield (none,())

def finish (acc : LoopState) : PrefixM Event Unit :=
  match acc.1 with
  | some value => pure value
  | none => liftPrefix (budgetExhausted "the send work queue")

def body (budget : Nat) : PrefixM Event Unit := do
  let acc ← forIn ([0:budget] : Std.Legacy.Range) (none,()) step
  finish acc

def afterFront : Option Nat → PrefixM Event Unit
  | none => pure ()
  | some budget => body budget

theorem source_factor : Driver.sendWorkersObserved hooks = (front >>= afterFront) := by
  unfold Driver.sendWorkersObserved front
  simp only [bind_assoc]
  congr 1
  funext w
  split
  · rfl
  · simp only [bind_assoc]
    congr 1
    funext ignored
    congr 1
    funext ignored
    congr 1
    funext budget
    simp only [pure_bind,afterFront,body,finish]
    apply congr
    · apply congrArg (fun action : PrefixM Event LoopState =>
        fun next : LoopState → PrefixM Event Unit => action >>= next)
      apply congrArg (fun action => forIn ([0:budget] : Std.Legacy.Range) (none,()) action)
      funext index acc
      unfold step
      apply congrArg (fun next => liftPrefix (liftWG getDev) >>= next)
      funext d
      split <;> rfl
    · funext acc
      cases acc.1 <;> rfl

theorem body_list (budget : Nat) : body budget =
    (forIn (Scheduler.indices budget) (none,()) step >>= finish) := by
  simp only [body,Scheduler.indices,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]

def remaining (rest : List Nat) : PrefixM Event Unit := forIn rest (none,()) step >>= finish

def workerEntryPrefix (count : Nat) : PrefixM Event Bool := do
  let some budget ← front | return false
  _ ← forIn ((Scheduler.indices budget).take count) (none,()) step
  let d ← liftPrefix (liftWG getDev)
  return !d.sendWorkQueue.isEmpty

def scheduleEntryPrefix (count : Nat) : PrefixM Event Bool := do
  if ← workerEntryPrefix count then
    Driver.sendWorkerObserved hooks
    return true
  return false

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain
