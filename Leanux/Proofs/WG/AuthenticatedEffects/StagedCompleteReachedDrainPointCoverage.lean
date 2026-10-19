import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainPointContract

/-! All actual loop visits lift into the fixed drain point relation. Visits
include successful and stopped iterations, but never a suffix skipped by done.
The original range and successful yield prefix determine the enclosing path. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal

inductive Visit : List Nat → LoopState → World → History → Result LoopState → History →
    Nat → LoopState → World → History → Prop where
  | first (execution : LoopExecution (index :: rest) acc w history result last) :
      Visit (index :: rest) acc w history result last index acc w history
  | later (current : StepExecution index acc w history (.ok (.yield next,u)) middle)
      (visit : Visit rest next u middle result last selected final v ending) :
      Visit (index :: rest) acc w history result last selected final v ending

theorem Visit.execution (visit : Visit indices acc w history result last index current u middle) :
    LoopExecution indices acc w history result last := by
  induction visit with
  | first execution => exact execution
  | later current visit ih => exact .yielded current ih

/-- Every visit is preceded only by the literal successful yield prefix.
A done iteration cannot supply a later visit. -/
theorem Visit.prefix (visit : Visit indices acc w history result last index current u middle) :
    ∃ done rest, indices = done ++ index :: rest ∧
      Scheduler.Yields step done acc w history current u middle := by
  induction visit with
  | first execution => exact ⟨[],_,rfl,.nil⟩
  | @later index acc w history next u middle rest result last selected final v ending current visit ih =>
      obtain ⟨done,remaining,shape,leading⟩ := ih
      exact ⟨index :: done,remaining,by simp only [List.cons_append,shape],
        .cons current.run leading⟩

theorem Visit.step (visit : Visit indices acc w history result last index current u middle) :
    ∃ decision ending, StepExecution index current u middle decision ending := by
  induction visit with
  | first execution =>
      cases execution with
      | stopped current => exact ⟨_,_,current⟩
      | done current => exact ⟨_,_,current⟩
      | yielded current remaining => exact ⟨_,_,current⟩
  | later current visit ih => exact ih

theorem no_empty_visit : ¬Visit [] acc w history result last index current u middle := by
  intro visit
  cases visit

/-- The early-done branch has no later iteration, even if the original range
has a nonempty suffix. A yielded trace cannot share its native step result. -/
theorem Visit.after_done
    (done : StepExecution index acc w history (.ok (.done final,u)) middle)
    (visit : Visit (index :: rest) acc w history result last selected current v ending) :
    selected = index ∧ current = acc ∧ v = w ∧ ending = history := by
  cases visit with
  | first execution => exact ⟨rfl,rfl,rfl,rfl⟩
  | later current remaining =>
      have impossible := done.run.symm.trans current.run
      cases impossible

theorem Visit.drain_path
    (entered : runPrefix front w history = (.ok (some budget,loopWorld),loopHistory))
    (visit : Visit (Scheduler.indices budget) (none,()) loopWorld loopHistory result last index current u middle) :
    ∃ path : LoopPath w history u middle, path.index = index ∧ path.acc = current := by
  obtain ⟨done,rest,shape,leading⟩ := visit.prefix
  exact ⟨⟨budget,loopWorld,loopHistory,entered,done,index,rest,shape,current,leading⟩,rfl,rfl⟩

/-- All visited iteration entries, including those in successful drains, carry
the actual original-prefix world and its complete native carrier. -/
theorem Visit.drain_point
    (before : CompleteProduct.Carrier history w)
    (entered : runPrefix front w history = (.ok (some budget,loopWorld),loopHistory))
    (visit : Visit (Scheduler.indices budget) (none,()) loopWorld loopHistory result last index current u middle) :
    ∃ path : LoopPath w history u middle,
      path.index = index ∧ path.acc = current ∧
      Point inside w history (.loop path.done.length) u middle ∧ CompleteProduct.Carrier middle u := by
  obtain ⟨path,indexEq,accEq⟩ := visit.drain_path entered
  exact ⟨path,indexEq,accEq,.loop path,path.carrier before⟩

inductive StepChild (w : World) (history : History) : Child → World → History → Prop where
  | delivery (read : runPrefix (liftPrefix (liftWG getDev)) w history = (.ok (device,u),middle))
      (empty : device.sendWorkQueue.isEmpty = true) : StepChild w history .delivery u middle
  | worker (read : runPrefix (liftPrefix (liftWG getDev)) w history = (.ok (device,u),middle))
      (nonempty : device.sendWorkQueue.isEmpty = false) : StepChild w history .worker u middle
  | scheduler (read : runPrefix (liftPrefix (liftWG getDev)) w history = (.ok (device,u),middle))
      (nonempty : device.sendWorkQueue.isEmpty = false)
      (sent : runPrefix (Driver.sendWorkerObserved hooks) u middle = (.ok ((),v),last)) :
      StepChild w history .scheduler v last

theorem StepChild.drain_entry (path : LoopPath w history u middle)
    (call : StepChild u middle child v last) : Nonempty (ChildEntry w history child v last) := by
  cases call with
  | delivery read empty => exact ⟨.delivery ⟨u,middle,path,_,read,empty⟩⟩
  | worker read nonempty => exact ⟨.worker (path.worker read nonempty)⟩
  | scheduler read nonempty sent => exact ⟨.scheduler ⟨_,_,path.worker read nonempty,sent⟩⟩

/-- Child interiors are lifted at the actual selected invocation, after all
earlier yields. The interior relation itself remains the child's explicit
source obligation, rather than an arbitrary chosen monadic factor. -/
theorem Visit.child_point
    (entered : runPrefix front w history = (.ok (some budget,loopWorld),loopHistory))
    (visit : Visit (Scheduler.indices budget) (none,()) loopWorld loopHistory result last index current u middle)
    (call : StepChild u middle child v callHistory)
    (nativePoint : inside child v callHistory cutWorld cutHistory) :
    ∃ path : ChildEntry w history child v callHistory,
      Point inside w history (.childInterior child path.count) cutWorld cutHistory := by
  obtain ⟨loop,_,_⟩ := visit.drain_path entered
  obtain ⟨path⟩ := call.drain_entry loop
  exact ⟨path,.childInterior path nativePoint⟩

/-- The same actual loop visit supplies child-native coverage, cut evidence,
and the original remaining drain. The child's supplied source remainder is
transported only after its native point and real invocation have been fixed. -/
theorem Visit.native_child {native inside : ChildPoints} {Good : History → World → Prop}
    (children : ChildContracts native inside Good)
    (before : CompleteProduct.Carrier history w)
    (entered : runPrefix front w history = (.ok (some budget,loopWorld),loopHistory))
    (visit : Visit (Scheduler.indices budget) (none,()) loopWorld loopHistory result last index current u middle)
    (call : StepChild u middle child v callHistory)
    (nativePoint : native child v callHistory cutWorld cutHistory) :
    ∃ path : ChildEntry w history child v callHistory,
      Point inside w history (.childInterior child path.count) cutWorld cutHistory ∧
      Good cutHistory cutWorld ∧
      runPrefix (Driver.sendWorkersObserved hooks) w history =
        runPrefix (children.remainder nativePoint >>= fun _ => path.after) cutWorld cutHistory := by
  obtain ⟨loop,_,_⟩ := visit.drain_path entered
  obtain ⟨path⟩ := call.drain_entry loop
  have accountedPoint := children.coverage nativePoint
  exact ⟨path,.childInterior path accountedPoint,
    children.at (path.carrier before) accountedPoint,path.interior_continuation children nativePoint⟩

/-- A normal loop either yielded every original index or finished at the
first actual done. In both cases every earlier successful iteration is kept. -/
theorem normal_loop
    (performed : runPrefix (forIn indices acc step) w history = (.ok (final,u),middle)) :
    Scheduler.Yields step indices acc w history final u middle ∨
      ∃ done index rest current v before,
        indices = done ++ index :: rest ∧
        Scheduler.Yields step done acc w history current v before ∧
        StepExecution index current v before (.ok (.done final,u)) middle := by
  induction indices generalizing acc w history with
  | nil =>
      simp only [List.forIn_nil,runPrefix_pure] at performed
      cases performed
      exact .inl .nil
  | cons index indices ih =>
      rw [List.forIn_cons,runPrefix_bind] at performed
      cases current : runPrefix (step index acc) w history with
      | mk result after =>
        rw [current] at performed
        cases result with
        | error reason => cases performed
        | ok pair =>
          obtain ⟨decision,v⟩ := pair
          cases decision with
          | done out =>
              simp only [runPrefix_pure] at performed
              cases performed
              exact .inr ⟨[],index,indices,acc,w,history,rfl,.nil,step_cases current⟩
          | yield next =>
              rcases ih performed with all | ⟨done,selected,rest,acc',v',before,shape,leading,ending⟩
              · exact .inl (.cons current all)
              · exact .inr ⟨index :: done,selected,rest,acc',v',before,
                  by simp only [List.cons_append,shape],.cons current leading,ending⟩

/-- The original budget's empty/exhausted path reaches finish without assuming
that finish returns. In particular the zero-budget error has a real entry. -/
theorem exhausted_finish
    (entered : runPrefix front w history = (.ok (some budget,loopWorld),loopHistory))
    (leading : Scheduler.Yields step (Scheduler.indices budget) (none,()) loopWorld loopHistory acc u middle) :
    Nonempty (FinishPath w history acc u middle) :=
  ⟨⟨budget,loopWorld,loopHistory,entered,leading.run⟩⟩

/-- The proof-only execution records characterize the original run exactly;
they are not another executable model of the drain. -/
theorem execution_iff : Execution w history result last ↔
    runPrefix (Driver.sendWorkersObserved hooks) w history = (result,last) :=
  ⟨Execution.run,execution_cases⟩

/-- A recorded zero budget reaches the original budget failure without running
delivery, a send worker, or the scheduler. Its entry is the real front result. -/
theorem zero_budget_continuation
    (entered : runPrefix front w history = (.ok (some 0,u),middle)) :
    runPrefix (Driver.sendWorkersObserved hooks) w history =
      runPrefix (liftPrefix (budgetExhausted "the send work queue") : PrefixM Event Unit) u middle := by
  rw [source_factor,runPrefix_bind,entered]
  change runPrefix (body 0) u middle = _
  rw [body_list]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
