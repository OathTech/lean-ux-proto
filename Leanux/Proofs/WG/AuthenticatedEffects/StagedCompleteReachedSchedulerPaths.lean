import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerLoop

/-! Source-indexed scheduler entries. Each path consists of the original
budget read, a literal range prefix of completed yields, and the actual next
selection. Its continuation is the untouched original range suffix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal

def indices (bound : Nat) : List Nat := List.range' 0 bound

theorem runBody_list (a : Activation) (occupancy : Nat) :
    runBody a occupancy = (forIn (indices (occupancy + 1)) (none,a) runStep >>= runFinish a occupancy) := by
  simp only [runBody,indices,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]

theorem scheduleBody_list (stack : Option Worker) (budget : Nat) :
    scheduleBody stack budget =
      (forIn (indices budget) (none,()) (scheduleStep stack) >>= scheduleFinish) := by
  simp only [scheduleBody,indices,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]

def iterationTail (a : Activation) (result : IterResult) : PrefixM Event (ForInStep RunState) := do
  match result with
  | .ended =>
    _ ← liftPrefix (hidden (.sectionStop a.worker))
    return .done (some (),a)
  | .continued => return .yield (none,{a with iterations := a.iterations + 1})
  | .yielded =>
    liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended ++ [{a with iterations := a.iterations + 1}]})
    return .done (some (),a)

theorem runStep_factor (index : Nat) (acc : RunState) :
    runStep index acc = (iteration acc.2 >>= iterationTail acc.2) := rfl

def runAfter (a : Activation) (occupancy : Nat) (remaining : List Nat) :
    ForInStep RunState → PrefixM Event Unit
  | .done acc => runFinish a occupancy acc
  | .yield acc => forIn remaining acc runStep >>= runFinish a occupancy

def scheduleAfter (stack : Option Worker) (remaining : List Nat) :
    ForInStep ScheduleState → PrefixM Event Unit
  | .done acc => scheduleFinish acc
  | .yield acc => forIn remaining acc (scheduleStep stack) >>= scheduleFinish

def runEntryPrefix (a : Activation) (count : Nat) : PrefixM Event RunState := do
  let occupancy ← liftPrefix (Env.Activation.occupancy a)
  forIn ((indices (occupancy + 1)).take count) (none,a) runStep

def scheduleEntryPrefix (stack : Option Worker) (count : Nat) : PrefixM Event Choice := do
  let budget ← liftPrefix recordBudget
  _ ← forIn ((indices budget).take count) (none,()) (scheduleStep stack)
  choose stack

structure RunPath (a : Activation) (w : World) (history : List Event)
    (active : Activation) (u : World) (middle : List Event) where
  occupancy : Nat
  readWorld : World
  readHistory : List Event
  read : runPrefix (liftPrefix (Env.Activation.occupancy a)) w history =
    (.ok (occupancy,readWorld),readHistory)
  done : List Nat
  index : Nat
  remaining : List Nat
  shape : indices (occupancy + 1) = done ++ index :: remaining
  tag : Option Unit
  leading : Yields runStep done (none,a) readWorld readHistory (tag,active) u middle

structure SchedulePath (stack : Option Worker) (w : World) (history : List Event)
    (choice : Choice) (u : World) (middle : List Event) where
  budget : Nat
  readWorld : World
  readHistory : List Event
  read : runPrefix (liftPrefix recordBudget) w history = (.ok (budget,readWorld),readHistory)
  done : List Nat
  index : Nat
  remaining : List Nat
  shape : indices budget = done ++ index :: remaining
  acc : ScheduleState
  beforeChoice : World
  beforeHistory : List Event
  leading : Yields (scheduleStep stack) done (none,()) readWorld readHistory acc beforeChoice beforeHistory
  chosen : runPrefix (choose stack) beforeChoice beforeHistory = (.ok (choice,u),middle)

theorem RunPath.bound (path : RunPath a w history active u middle) :
    path.done.length < path.occupancy + 1 := by
  have length := congrArg List.length path.shape
  simp only [indices,List.length_range',List.length_append,List.length_cons] at length
  omega

theorem SchedulePath.bound (path : SchedulePath stack w history choice u middle) :
    path.done.length < path.budget := by
  have length := congrArg List.length path.shape
  simp only [indices,List.length_range',List.length_append,List.length_cons] at length
  omega

theorem checked_normal {action : PrefixM Event α}
    (checked : CompleteProduct.Checked action) (before : CompleteProduct.Carrier history w)
    (performed : runPrefix action w history = (.ok (value,u),middle)) : CompleteProduct.Carrier middle u := by
  have kept := (checked w history before).choose_spec.2.2
  rw [performed] at kept
  exact kept

theorem RunPath.carrier (path : RunPath a w history active u middle)
    (before : CompleteProduct.Carrier history w) : CompleteProduct.Carrier middle u :=
  path.leading.carrier runStep_checked (checked_normal (occupancy_checked a) before path.read)

theorem RunPath.prefix (path : RunPath a w history active u middle) :
    runPrefix (runEntryPrefix a path.done.length) w history = (.ok ((path.tag,active),u),middle) := by
  rw [runEntryPrefix,runPrefix_bind,path.read]
  have taken : (indices (path.occupancy + 1)).take path.done.length = path.done := by
    rw [path.shape]; simp
  change runPrefix (forIn ((indices (path.occupancy + 1)).take path.done.length) (none,a) runStep)
    path.readWorld path.readHistory = _
  rw [taken]
  exact path.leading.run

theorem RunPath.continuation (path : RunPath a w history active u middle) :
    runPrefix (SourceScheduler.run iteration a) w history =
      runPrefix (iteration active >>= fun result => iterationTail active result >>=
        runAfter a path.occupancy path.remaining) u middle := by
  rw [run_factor,runPrefix_bind,path.read]
  change runPrefix (runBody a path.occupancy) path.readWorld path.readHistory = _
  rw [runBody_list,path.shape,path.leading.continue]
  rw [List.forIn_cons,bind_assoc,runStep_factor,bind_assoc]
  apply congrArg (fun body : PrefixM Event Unit => runPrefix body u middle)
  apply congrArg (fun next => iteration active >>= next)
  funext result
  apply congrArg (fun next => iterationTail active result >>= next)
  funext decision
  cases decision <;> simp only [runAfter,pure_bind]

theorem SchedulePath.carrier (path : SchedulePath stack w history choice u middle)
    (before : CompleteProduct.Carrier history w) : CompleteProduct.Carrier middle u := by
  have budget := checked_normal (CompleteProduct.ambient (recordBudget : AmbientM Nat)) before path.read
  exact checked_normal (choose_checked stack)
    (path.leading.carrier (scheduleStep_checked stack) budget) path.chosen

theorem SchedulePath.prefix (path : SchedulePath stack w history choice u middle) :
    runPrefix (scheduleEntryPrefix stack path.done.length) w history = (.ok (choice,u),middle) := by
  rw [scheduleEntryPrefix,runPrefix_bind,path.read]
  have taken : (indices path.budget).take path.done.length = path.done := by
    rw [path.shape]; simp
  change runPrefix (forIn ((indices path.budget).take path.done.length) (none,()) (scheduleStep stack) >>=
    fun _ => choose stack) path.readWorld path.readHistory = _
  rw [taken,runPrefix_bind,path.leading.run]
  exact path.chosen

theorem SchedulePath.continuation (path : SchedulePath stack w history choice u middle) :
    runPrefix (Driver.scheduleObserved hooks stack) w history =
      runPrefix (perform choice >>= scheduleAfter stack path.remaining) u middle := by
  rw [schedule_factor,runPrefix_bind,path.read]
  change runPrefix (scheduleBody stack path.budget) path.readWorld path.readHistory = _
  rw [scheduleBody_list,path.shape,path.leading.continue]
  rw [List.forIn_cons,bind_assoc]
  change runPrefix ((choose stack >>= perform) >>= _) path.beforeChoice path.beforeHistory = _
  rw [bind_assoc,runPrefix_bind,path.chosen]
  dsimp only
  apply congrArg (fun body : PrefixM Event Unit => runPrefix body u middle)
  apply congrArg (fun next => perform choice >>= next)
  funext decision
  cases decision <;> simp only [scheduleAfter,pure_bind]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler
