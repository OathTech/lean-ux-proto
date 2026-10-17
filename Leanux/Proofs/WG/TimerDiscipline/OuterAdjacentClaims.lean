import Leanux.Proofs.WG.TimerDiscipline.OuterAdjacentSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- All qualifying adjacent pairs in the actual complete timer episode have
retry certificates. Other turns and Stop outcomes retain the unchanged observer
semantics; this does not claim that the whole episode is a retry sequence. -/
theorem runTimers_adjacent_retry_pairs (jPass : UInt64) :
    Campaign2.Product.Ensures (observedRunTimersEpisode jPass) (fun _ => True)
      (fun result _ => ∀ front suffix left right,
        result.1.turns = front ++ left :: right :: suffix → OuterAdjacentRetryPair jPass left right) := by
  intro initial result final _ run front suffix left right adjacent
  let start : World := {initial with wg := {initial.wg with queuedThisCall := []}}
  let budget : Nat := match initial.ambient.hidden with
    | some records => records.length + 1
    | none => DOMAIN_FILTER_TURNS
  have budgetRun : (recordBudget : Leanux.M Nat).run start = .ok (budget,start) := rfl
  change (if start.wg.dev.isNone then Except.ok ((_,false),start) else _) = _ at run
  by_cases absent : start.wg.dev.isNone = true
  · simp only [absent,ite_true] at run
    have value := congrArg Prod.fst (Except.ok.inj run)
    dsimp only at value
    rw [← value] at adjacent
    have count := congrArg List.length adjacent
    simp only [List.length_nil,List.length_append,List.length_cons] at count
    omega
  · simp only [absent,Bool.false_eq_true,ite_false] at run
    rw [budgetRun] at run
    change ((observedTimerOuterTurns jPass (List.range' 0 budget) (false,none)).run start >>= fun out =>
      (timerOuterFinish out.1.1).run out.2 >>= fun tail =>
        Except.ok ((_,tail.1),tail.2)) = _ at run
    cases turns : (observedTimerOuterTurns jPass (List.range' 0 budget) (false,none)).run start with
    | error stop => rw [turns] at run; cases run
    | ok out =>
      obtain ⟨⟨control,receipts⟩,middle⟩ := out
      rw [turns] at run
      change ((timerOuterFinish control).run middle >>= _) = _ at run
      cases finish : (timerOuterFinish control).run middle with
      | error stop => rw [finish] at run; cases run
      | ok out =>
        rw [finish] at run
        have lists := congrArg (fun out => out.1.1.turns) (Except.ok.inj run)
        dsimp only at lists
        rw [← lists] at adjacent
        obtain ⟨i,k,before,next,step,firstState,secondState,lastState,first,second⟩ :=
          observedTimerOuterTurns_adjacent_run jPass (List.range' 0 budget) (false,none) control
            start middle receipts front suffix left right turns adjacent
        exact observedTimerOuterTurns_pair jPass i k before next step firstState secondState lastState
          left right first second


end Leanux.Proofs.WG.TimerDiscipline
