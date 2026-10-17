import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- Normal return supplies a receipt for every actual original turn from an
arbitrary entry. Callback success is derived, never assumed at entry. -/
theorem runTimers_episode_receipt (jPass : UInt64) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observedRunTimersEpisode jPass)
      (fun initial => initial = entry)
      (fun result final => OuterTimerEpisodeValid jPass entry result.1 result.2 final) := by
  intro initial result final pre run
  cases pre
  let start : World := {initial with wg := {initial.wg with queuedThisCall := []}}
  let budget : Nat := match initial.ambient.hidden with
    | some records => records.length + 1
    | none => DOMAIN_FILTER_TURNS
  have budgetRun : (recordBudget : Leanux.M Nat).run start = .ok (budget,start) := rfl
  change (if start.wg.dev.isNone then Except.ok ((_,false),start) else _) = _ at run
  by_cases absent : start.wg.dev.isNone = true
  · simp only [absent,ite_true] at run
    obtain ⟨valueEq,stateEq⟩ := Prod.mk.inj (Except.ok.inj run)
    rw [← valueEq,← stateEq]
    refine ⟨rfl,?_⟩
    change if start.wg.dev.isNone then _ else _
    rw [absent]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
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
        obtain ⟨value,last⟩ := out
        rw [finish] at run
        cases run
        refine ⟨rfl,?_⟩
        change if start.wg.dev.isNone then _ else _
        rw [ite_eq_right absent]
        exact ⟨rfl,observedTimerOuterTurns_chain jPass (List.range' 0 budget) (false,none)
          start middle control receipts turns,rfl⟩


end Leanux.Proofs.WG.TimerDiscipline
