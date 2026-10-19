import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendDrainCuts

/-! Source points for the original send drain. These are literal front/step/
finish actions, not a second evaluator or arbitrary monadic decompositions.
Successful native runs name their actual worlds; errors never invent one. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal

abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)

def frontRead : PrefixM Event WGWorld := liftPrefix getWG
def frontCheck : PrefixM Event Unit := liftPrefix Env.requireNoCryptWork
def frontReset : PrefixM Event Unit :=
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
def frontBudget : PrefixM Event Nat := liftPrefix recordBudget

def afterRead (saved : WGWorld) : PrefixM Event (Option Nat) := do
  if saved.dev.isNone then return none
  frontCheck
  frontReset
  return some (← frontBudget)

theorem front_factor : front = (frontRead >>= afterRead) := rfl

inductive FrontStage where
  | entry | read | checked | reset | budget

inductive FrontPoint (w : World) (history : History) :
    FrontStage → World → History → Prop where
  | entry : FrontPoint w history .entry w history
  | read (run : runPrefix frontRead w history = (.ok (saved,u),middle)) :
      FrontPoint w history .read u middle
  | checked (read : runPrefix frontRead w history = (.ok (saved,u),middle))
      (present : saved.dev.isNone = false)
      (run : runPrefix frontCheck u middle = (.ok ((),v),last)) :
      FrontPoint w history .checked v last
  | reset (read : runPrefix frontRead w history = (.ok (saved,u),middle))
      (present : saved.dev.isNone = false)
      (checked : runPrefix frontCheck u middle = (.ok ((),v),last))
      (run : runPrefix frontReset v last = (.ok ((),next),ending)) :
      FrontPoint w history .reset next ending
  | budget (read : runPrefix frontRead w history = (.ok (saved,u),middle))
      (present : saved.dev.isNone = false)
      (checked : runPrefix frontCheck u middle = (.ok ((),v),last))
      (reset : runPrefix frontReset v last = (.ok ((),next),ending))
      (run : runPrefix frontBudget next ending = (.ok (budget,final),afterBudget)) :
      FrontPoint w history .budget final afterBudget

inductive FrontExecution (w : World) (history : History) :
    Result (Option Nat) → History → Prop where
  | readStopped (run : runPrefix frontRead w history = (.error reason,last)) :
      FrontExecution w history (.error reason) last
  | absent (read : runPrefix frontRead w history = (.ok (saved,u),middle))
      (absent : saved.dev.isNone = true) : FrontExecution w history (.ok (none,u)) middle
  | checkStopped (read : runPrefix frontRead w history = (.ok (saved,u),middle))
      (present : saved.dev.isNone = false)
      (run : runPrefix frontCheck u middle = (.error reason,last)) :
      FrontExecution w history (.error reason) last
  | resetStopped (read : runPrefix frontRead w history = (.ok (saved,u),middle))
      (present : saved.dev.isNone = false)
      (checked : runPrefix frontCheck u middle = (.ok ((),v),last))
      (run : runPrefix frontReset v last = (.error reason,ending)) :
      FrontExecution w history (.error reason) ending
  | budgetStopped (read : runPrefix frontRead w history = (.ok (saved,u),middle))
      (present : saved.dev.isNone = false)
      (checked : runPrefix frontCheck u middle = (.ok ((),v),last))
      (reset : runPrefix frontReset v last = (.ok ((),next),ending))
      (run : runPrefix frontBudget next ending = (.error reason,afterBudget)) :
      FrontExecution w history (.error reason) afterBudget
  | ready (read : runPrefix frontRead w history = (.ok (saved,u),middle))
      (present : saved.dev.isNone = false)
      (checked : runPrefix frontCheck u middle = (.ok ((),v),last))
      (reset : runPrefix frontReset v last = (.ok ((),next),ending))
      (run : runPrefix frontBudget next ending = (.ok (budget,final),afterBudget)) :
      FrontExecution w history (.ok (some budget,final)) afterBudget

inductive Child where
  | delivery | worker | scheduler

def Child.action : Child → PrefixM Event Unit
  | .delivery => hooks.deliver
  | .worker => Driver.sendWorkerObserved hooks
  | .scheduler => Driver.scheduleObserved hooks none

inductive StepExecution (index : Nat) (acc : LoopState) (w : World) (history : History) :
    Result (ForInStep LoopState) → History → Prop where
  | readStopped (run : runPrefix (liftPrefix (liftWG getDev)) w history = (.error reason,last)) :
      StepExecution index acc w history (.error reason) last
  | deliveryStopped
      (read : runPrefix (liftPrefix (liftWG getDev)) w history = (.ok (device,u),middle))
      (empty : device.sendWorkQueue.isEmpty = true)
      (run : runPrefix hooks.deliver u middle = (.error reason,last)) :
      StepExecution index acc w history (.error reason) last
  | done (read : runPrefix (liftPrefix (liftWG getDev)) w history = (.ok (device,u),middle))
      (empty : device.sendWorkQueue.isEmpty = true)
      (run : runPrefix hooks.deliver u middle = (.ok ((),v),last)) :
      StepExecution index acc w history (.ok (.done (some (),()),v)) last
  | workerStopped
      (read : runPrefix (liftPrefix (liftWG getDev)) w history = (.ok (device,u),middle))
      (nonempty : device.sendWorkQueue.isEmpty = false)
      (run : runPrefix (Driver.sendWorkerObserved hooks) u middle = (.error reason,last)) :
      StepExecution index acc w history (.error reason) last
  | scheduleStopped
      (read : runPrefix (liftPrefix (liftWG getDev)) w history = (.ok (device,u),middle))
      (nonempty : device.sendWorkQueue.isEmpty = false)
      (sent : runPrefix (Driver.sendWorkerObserved hooks) u middle = (.ok ((),v),last))
      (run : runPrefix (Driver.scheduleObserved hooks none) v last = (.error reason,ending)) :
      StepExecution index acc w history (.error reason) ending
  | yielded
      (read : runPrefix (liftPrefix (liftWG getDev)) w history = (.ok (device,u),middle))
      (nonempty : device.sendWorkQueue.isEmpty = false)
      (sent : runPrefix (Driver.sendWorkerObserved hooks) u middle = (.ok ((),v),last))
      (run : runPrefix (Driver.scheduleObserved hooks none) v last = (.ok ((),next),ending)) :
      StepExecution index acc w history (.ok (.yield (none,()),next)) ending

/-- The finite original loop records every completed yield and its final done,
error or empty suffix. There is no requirement that the enclosing drain fail. -/
inductive LoopExecution : List Nat → LoopState → World → History →
    Result LoopState → History → Prop where
  | nil : LoopExecution [] acc w history (.ok (acc,w)) history
  | stopped (current : StepExecution index acc w history (.error reason) last) :
      LoopExecution (index :: rest) acc w history (.error reason) last
  | done (current : StepExecution index acc w history (.ok (.done final,u)) middle) :
      LoopExecution (index :: rest) acc w history (.ok (final,u)) middle
  | yielded (current : StepExecution index acc w history (.ok (.yield next,u)) middle)
      (remaining : LoopExecution rest next u middle result last) :
      LoopExecution (index :: rest) acc w history result last

inductive Execution (w : World) (history : History) : Result Unit → History → Prop where
  | frontStopped (front : FrontExecution w history (.error reason) last) :
      Execution w history (.error reason) last
  | absent (front : FrontExecution w history (.ok (none,u)) middle) :
      Execution w history (.ok ((),u)) middle
  | loopStopped (front : FrontExecution w history (.ok (some budget,u)) middle)
      (loop : LoopExecution (Scheduler.indices budget) (none,()) u middle (.error reason) last) :
      Execution w history (.error reason) last
  | finish (front : FrontExecution w history (.ok (some budget,u)) middle)
      (loop : LoopExecution (Scheduler.indices budget) (none,()) u middle (.ok (acc,v)) last)
      (run : runPrefix (SendDrain.finish acc) v last = (result,ending)) :
      Execution w history result ending

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
