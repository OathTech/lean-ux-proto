import Leanux.Proofs.WG.Progress.TimerBudgetModel
import Leanux.Proofs.WG.Progress.TimerTurnRecordSource
import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeSource

/-! Adequacy of the existing observed timer loop, using concrete strict decrease on every yielded turn. No callback-success hypothesis or new operational walker is introduced. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env
open Leanux.Proofs.WG.TimerDiscipline

/-- Every normal observed loop has a final actual done turn when its index list is longer than the supplied records. Stops propagate before a receipt list can be returned. -/
theorem timerOuterTurns_budget_done
    (jPass : UInt64) (indices : List Nat) (control : TimerOuterControl)
    (records : List HiddenRecord) (before after : World)
    (finalControl : TimerOuterControl) (receipts : List OuterTimerTurnReceipt)
    (present : before.ambient.hidden=some records)
    (enough : records.length < indices.length)
    (run : (observedTimerOuterTurns jPass indices control).run before=
      .ok ((finalControl,receipts),after)) :
    ∃ front last, receipts=front++[last] ∧ last.result=.done finalControl := by
  induction indices generalizing control records before after finalControl receipts with
  | nil=>simp only [List.length_nil] at enough; omega
  | cons iteration indices ih=>
    rw [observedTimerOuterTurns,StateT.run_bind] at run
    cases turn : (observedTimerOuterTurn jPass iteration control).run before with
    | error stop=>rw [turn] at run; cases run
    | ok pair=>
      obtain ⟨⟨step,receipt⟩,middle⟩:=pair
      have raw:=congrArg (fun action : Leanux.M (ForInStep TimerOuterControl)=>action.run before)
        (observedTimerOuterTurn_erase jPass iteration control)
      change ((observedTimerOuterTurn jPass iteration control).run before >>=
        fun out=>Except.ok (out.1.1,out.2))=
        (timerOuterTurn jPass iteration control).run before at raw
      rw [turn] at raw
      have effect : (timerOuterTurn jPass iteration control).run before=.ok (step,middle):=raw.symm
      obtain ⟨_,_,_,resultEq,_,_⟩:=
        observedTimerOuterTurn_valid jPass iteration control before middle step receipt turn
      rw [turn] at run
      cases step with
      | done next=>
        cases run
        exact ⟨[],receipt,rfl,resultEq⟩
      | yield next=>
        obtain ⟨remaining,stored,_,shorter⟩:=
          timerOuterTurn_yield_strict jPass iteration control next records before middle present effect
        change ((observedTimerOuterTurns jPass indices next).run middle >>= fun out=>
          Except.ok ((out.1.1,receipt::out.1.2),out.2))=_ at run
        cases tailRun : (observedTimerOuterTurns jPass indices next).run middle with
        | error stop=>rw [tailRun] at run; cases run
        | ok pair=>
          obtain ⟨⟨lastControl,tail⟩,lastState⟩:=pair
          rw [tailRun] at run
          cases run
          obtain ⟨front,last,history,done⟩:=ih next remaining middle lastState lastControl tail
            stored (by simp only [List.length_cons] at enough; omega) tailRun
          exact ⟨receipt::front,last,by rw [history]; rfl,done⟩

/-- Whole-episode source join, including the original reset, optional-device branch and actual finish. The conclusion applies only when that unchanged episode returns normally. -/
theorem runTimersEpisode_budget_done (jPass : UInt64) (records : List HiddenRecord)
    (initial final : World) (receipt : OuterTimerEpisodeReceipt) (result : Bool)
    (present : initial.ambient.hidden=some records)
    (run : (observedRunTimersEpisode jPass).run initial=.ok ((receipt,result),final)) :
    TimerEpisodeBudgetDone records receipt := by
  let start : World:={initial with wg:={initial.wg with queuedThisCall:=[]}}
  have budgetRun : (recordBudget : Leanux.M Nat).run start=.ok (records.length+1,start) := by
    change Except.ok ((match initial.ambient.hidden with
      | some rs=>rs.length+1
      | none=>DOMAIN_FILTER_TURNS),start)=_
    rw [present]
  change (if start.wg.dev.isNone then Except.ok ((_,false),start) else _) = _ at run
  by_cases absent : start.wg.dev.isNone=true
  · simp only [absent,ite_true] at run
    have receiptEq:=congrArg (fun out=>out.1.1) (Except.ok.inj run)
    dsimp only at receiptEq
    rw [←receiptEq]
    change if start.wg.dev.isNone then _ else _
    rw [absent]
    exact ⟨rfl,rfl⟩
  · simp only [absent,Bool.false_eq_true,ite_false] at run
    rw [budgetRun] at run
    change ((observedTimerOuterTurns jPass (List.range' 0 (records.length+1)) (false,none)).run start >>= fun out=>
      (timerOuterFinish out.1.1).run out.2 >>= fun tail=>
        Except.ok ((_,tail.1),tail.2))=_ at run
    cases turns : (observedTimerOuterTurns jPass (List.range' 0 (records.length+1)) (false,none)).run start with
    | error stop=>rw [turns] at run; cases run
    | ok pair=>
      obtain ⟨⟨control,receipts⟩,middle⟩:=pair
      rw [turns] at run
      change ((timerOuterFinish control).run middle >>= _)=_ at run
      cases finish : (timerOuterFinish control).run middle with
      | error stop=>rw [finish] at run; cases run
      | ok pair=>
        obtain ⟨value,last⟩:=pair
        rw [finish] at run
        cases run
        change if start.wg.dev.isNone then _ else _
        rw [ite_eq_right absent]
        exact ⟨rfl,timerOuterTurns_budget_done jPass (List.range' 0 (records.length+1))
          (false,none) records start middle control receipts present
          (by simp only [List.length_range']; omega) turns⟩

end Leanux.Proofs.WG.Progress.RecordSuffix
