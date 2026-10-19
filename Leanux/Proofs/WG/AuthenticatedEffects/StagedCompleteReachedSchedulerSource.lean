import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCryptSources
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductTx

/-! Fixed scheduler subprograms retain the original record budget, native
selection and copied-world consistency trial. Only dispatch/run/softirq execute
committed observed callbacks. The equations below identify the original source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev RunState := Option Unit × Activation
abbrev ScheduleState := Option Unit × Unit

def iteration (a : Activation) := Driver.iterationObserved hooks a

def runStep (_ : Nat) (state : RunState) : PrefixM Event (ForInStep RunState) := do
  let act := state.2
  match ← iteration act with
  | .ended =>
    _ ← liftPrefix (hidden (.sectionStop act.worker))
    return .done (some (),act)
  | .continued => return .yield (none,{act with iterations := act.iterations + 1})
  | .yielded =>
    liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended ++ [{act with iterations := act.iterations + 1}]})
    return .done (some (),act)

def runFinish (a : Activation) (occupancy : Nat) (state : RunState) : PrefixM Event Unit :=
  match state.1 with
  | some value => pure value
  | none => liftPrefix (invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) in one run")

def runBody (a : Activation) (occupancy : Nat) : PrefixM Event Unit := do
  let result ← forIn ([0:occupancy + 1] : Std.Legacy.Range) (none,a) runStep
  runFinish a occupancy result

theorem run_factor (a : Activation) :
    SourceScheduler.run iteration a = (do
      let occupancy ← liftPrefix (Env.Activation.occupancy a)
      runBody a occupancy) := by
  unfold SourceScheduler.run runBody
  apply congrArg (fun next => liftPrefix (Env.Activation.occupancy a) >>= next)
  funext occupancy
  dsimp only
  apply congr
  · apply congrArg (fun body : PrefixM Event RunState => fun finish : RunState → PrefixM Event Unit => body >>= finish)
    apply congrArg (fun step => forIn ([0:occupancy + 1] : Std.Legacy.Range) (none,a) step)
    funext index state
    unfold runStep
    apply congrArg (fun next => iteration state.2 >>= next)
    funext result
    cases result <;> rfl
  · funext state
    unfold runFinish
    cases state.1 <;> rfl


/-- Exact pre-run dispatch: TX resolution and work-queue removal occur before
sectionStart, and no event from a copied consistency trial is introduced. -/
def dispatchChoose (worker : Worker) : PrefixM Event (Option Activation) := do
  let d ← liftPrefix (liftWG getDev)
  let mut pid : Option Nat := none
  match worker with
  | .encryptWorker => if d.encryptQueue.empty then return none
  | .decryptWorker => if d.decryptQueue.empty then return none
  | .receiveWorker => if d.handshakeQueue.empty then return none
  | .txWorker =>
    let some headPid := d.txWorkQueue.head? | return none
    let p ← match ← liftPrefix (peekUnit .txWorker) with
      | some u => liftPrefix (resolveUnit .txWorker u d.txWorkQueue)
      | none => pure headPid
    liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase p}))
    pid := some p
  | _ => return none
  _ ← liftPrefix (hidden (.sectionStart worker))
  return some {worker,pid}

def dispatchAfter : Option Activation → PrefixM Event Bool
  | none => pure false
  | some a => do SourceScheduler.run iteration a; return true

theorem dispatch_factor (worker : Worker) :
    SourceScheduler.dispatch iteration worker = (dispatchChoose worker >>= dispatchAfter) := by
  unfold SourceScheduler.dispatch dispatchChoose
  simp only [bind_assoc]
  congr 1
  funext d
  cases worker <;> simp only [pure_bind,dispatchAfter]
  all_goals repeat' first
    | rfl
    | (split; all_goals simp_all only [pure_bind,dispatchAfter,bind_assoc])
    | (congr 1; funext x)

inductive Choice where
  | idle
  | dispatch (worker : Worker) (required : Bool)
  | napi
  | resumed (activation : Activation)
  | next

def choose (stack : Option Worker) : PrefixM Event Choice := do
  if (← liftPrefix getAmbient).hidden.isNone then
    let d ← liftPrefix (liftWG getDev)
    let next := [Worker.receiveWorker,.decryptWorker,.encryptWorker,.txWorker].find? fun w =>
      match w with
      | .receiveWorker => !d.handshakeQueue.empty
      | .decryptWorker => !d.decryptQueue.empty
      | .encryptWorker => !d.encryptQueue.empty
      | _ => !d.txWorkQueue.isEmpty
    let some worker := next | return .idle
    return .dispatch worker true
  let next ← liftPrefix peekHiddenSite
  if let some (worker,true) := next.bind Env.sectionOf then return .dispatch worker false
  if ← liftPrefix (Lifetimes.pendingNapi next) then return .napi
  match ← liftPrefix ((← liftPrefix getAmbient).suspended.filterM Env.Activation.consistent) with
  | [] => return .idle
  | [a] =>
    if let some worker := stack then
      if ← liftPrefix (Env.Activation.hasWork {worker}) then
        liftPrefix (unsupported "the records do not determine which suspended worker resumed")
    liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended.filter (· != a)})
    return .resumed a
  | _ =>
    liftPrefix (unsupported "the records do not determine which suspended worker resumed")
    return .next

def perform : Choice → PrefixM Event (ForInStep ScheduleState)
  | .idle => pure (.done (some (),()))
  | .next => pure (.yield (none,()))
  | .dispatch worker required => do
    let dispatched ← SourceScheduler.dispatch iteration worker
    if required then
      if !dispatched then liftPrefix (invariant s!"{worker.symbol} has work but was not dispatched")
      return .yield (none,())
    else if dispatched then return .yield (none,()) else return .done (some (),())
  | .napi => do
    Driver.softirqObserved hooks
    if (← liftPrefix peekHiddenSite) == some (HiddenSite.sectionStart .netRx).info.id then
      return .done (some (),())
    return .yield (none,())
  | .resumed a => do
    SourceScheduler.run iteration a
    return .yield (none,())

def scheduleStep (stack : Option Worker) (_ : Nat) (_ : ScheduleState) :
    PrefixM Event (ForInStep ScheduleState) := choose stack >>= perform

def scheduleFinish (state : ScheduleState) : PrefixM Event Unit :=
  match state.1 with
  | some value => pure value
  | none => liftPrefix (budgetExhausted "the scheduler loop")

def scheduleBody (stack : Option Worker) (budget : Nat) : PrefixM Event Unit := do
  let result ← forIn ([0:budget] : Std.Legacy.Range) (none,()) (scheduleStep stack)
  scheduleFinish result

theorem schedule_factor (stack : Option Worker) :
    Driver.scheduleObserved hooks stack = (do
      let budget ← liftPrefix recordBudget
      scheduleBody stack budget) := by
  unfold Driver.scheduleObserved SourceScheduler.schedule scheduleBody scheduleStep choose scheduleFinish
  simp only [bind_assoc]
  congr 1
  funext budget
  congr 1
  · congr 1
    funext index state
    repeat' first
      | rfl
      | (simp only [pure_bind,perform,bind_assoc])
      | (split; all_goals simp_all [perform,bind_assoc])
      | (congr 1; funext x)
    all_goals try rw [show iteration = Driver.iterationObserved CausalJournal.hooks from rfl]
    all_goals grind

  · funext state
    cases state.1 <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler
