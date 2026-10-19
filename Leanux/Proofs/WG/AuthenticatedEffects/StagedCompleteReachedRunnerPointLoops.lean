import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointResidual

/-! Finite source decomposition includes empty, stopped, done and yield
branches. Only actual successful yields lead to a later original list item. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
open Leanux Leanux.Proofs.Logged Queues Queues.RxCredits TransmitSecurity CausalJournal

variable {ι σ : Type} {body : ι→σ→PrefixOuter Event (ForInStep σ)}

inductive LoopExecution (shapes : ∀i s,Shape (body i s)) :
    List ι → σ → History → Result σ → History → Prop where
  | nil : LoopExecution shapes [] acc h (.ok acc) h
  | stopped (current : Execution (shapes i acc) h (.error reason) last) :
      LoopExecution shapes (i::rest) acc h (.error reason) last
  | done (current : Execution (shapes i acc) h (.ok (.done final)) last) :
      LoopExecution shapes (i::rest) acc h (.ok final) last
  | yielded (current : Execution (shapes i acc) h (.ok (.yield next)) middle)
      (remaining : LoopExecution shapes rest next middle result last) :
      LoopExecution shapes (i::rest) acc h result last

theorem LoopExecution.run {shapes : ∀i s,Shape (body i s)} (executed : LoopExecution shapes xs acc h result last) :
    runPrefixOuter (forIn xs acc body) h=(result,last) := by
  induction executed with
  | nil => rfl
  | stopped current => rw [List.forIn_cons,runPrefixOuter_bind,current.run]
  | done current => rw [List.forIn_cons,runPrefixOuter_bind,current.run]; rfl
  | yielded current remaining ih => rw [List.forIn_cons,runPrefixOuter_bind,current.run]; exact ih

theorem loop_cases (shapes : ∀i s,Shape (body i s))
    (performed : runPrefixOuter (forIn xs acc body) h=(result,last)) :
    LoopExecution shapes xs acc h result last := by
  induction xs generalizing acc h with
  | nil => simp only [List.forIn_nil,runPrefixOuter_pure] at performed; cases performed; exact .nil
  | cons i rest ih =>
    rw [List.forIn_cons,runPrefixOuter_bind] at performed
    cases source : runPrefixOuter (body i acc) h with
    | mk outcome middle =>
      rw [source] at performed
      cases outcome with
      | error reason => cases performed; exact .stopped ((execution_iff _).mpr source)
      | ok decision =>
        cases decision with
        | done final =>
          simp only [runPrefixOuter_pure] at performed
          cases performed
          exact .done ((execution_iff _).mpr source)
        | yield next => exact .yielded ((execution_iff _).mpr source) (ih performed)

inductive LoopVisit (shapes : ∀i s,Shape (body i s)) :
    List ι → σ → History → ι → σ → History → Prop where
  | here : LoopVisit shapes (i::rest) acc h i acc h
  | next (leading : runPrefixOuter (body first acc) h=(.ok (.yield next),middle))
      (later : LoopVisit shapes rest next middle i current last) :
      LoopVisit shapes (first::rest) acc h i current last

theorem Point.source_cast {left right : PrefixOuter Event α} (same : left=right)
    {shape : Shape left} (point : Point inside shape h site u middle) :
    Point inside (same ▸ shape) h site u middle := by cases same; exact point

theorem LoopVisit.point (visit : LoopVisit shapes xs acc h i current middle)
    (point : Point inside (shapes i current) middle site u last) :
    ∃position,Point inside (listShape xs acc body shapes) h position u last := by
  induction visit with
  | here =>
    exact ⟨_,Point.source_cast _ (.left _ point)⟩
  | next leading later ih =>
    obtain ⟨position,reached⟩ := ih point
    exact ⟨_,Point.source_cast _ (.right _ _ leading reached)⟩

theorem operation_never_done (trace : Runner.Trace) (op : Runner.Operation) (acc : State)
    (performed : runPrefixOuter (RunnerOperation.operation (Driver.syscallObserved hooks) trace op acc) h=(.ok decision,last)) :
    ∃next,decision=.yield next ∧ next.2.1.size=acc.2.1.size+1 :=
  RunnerOperation.operation_index _ _ _ _ performed

/-- Every numeric position before a normally returned original operation
loop has its literal take-prefix, source-selected operation and drop-suffix.
This is not a claim that a stopped loop visited later operations. -/
theorem normal_operation_prefix (trace : Runner.Trace) (acc : State)
    (performed : runPrefixOuter (forIn trace.ops.toList acc
      (RunnerOperation.operation (Driver.syscallObserved hooks) trace)) h=(.ok result,last))
    (bound : count<trace.ops.toList.length) :
    ∃op current next middle after,
      trace.ops.toList[count]?=some op ∧
      runPrefixOuter (forIn (trace.ops.toList.take count) acc
        (RunnerOperation.operation (Driver.syscallObserved hooks) trace)) h=(.ok current,middle) ∧
      runPrefixOuter (RunnerOperation.operation (Driver.syscallObserved hooks) trace op current) middle=(.ok (.yield next),after) ∧
      runPrefixOuter (forIn (trace.ops.toList.drop (count+1)) next
        (RunnerOperation.operation (Driver.syscallObserved hooks) trace)) after=(.ok result,last) :=
  RunnerOperationCuts.list_cut _ _ _ _ performed bound

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
