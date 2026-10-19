import Leanux.Proofs.WG.Progress.RecordBudgetSource
import Leanux.Proofs.WG.Progress.SendLoopRecordFrames
import Leanux.Proofs.WG.Progress.SendCompletionSource

/-! Concrete send-worker turns, whole-loop suffix retention and adequacy of its original captured record budget. The unchanged completion factor and generic finite-loop proof are reused; all worker/scheduler/delivery callbacks are concrete. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem sendCompletionTurn_record_effect (records : List HiddenRecord)
    (index : Nat) (state : Option Unit×Unit) :
    Hoare (sendCompletionTurn index state) (fun w=>Tail records w.ambient.hidden)
      (fun result w=>Tail records w.ambient.hidden ∧
        (∀ value,result=.yield value→StrictTail records w.ambient.hidden)) := by
  unfold sendCompletionTurn
  apply hoare_bind _ _ (native_product records _ (native_getDev records))
  intro d
  split
  · apply hoare_bind _ _ (deliverSent_retains records)
    intro _
    exact hoare_consequence (hoare_pure (ForInStep.done ((some (),()) : Option Unit×Unit)) (fun w : World=>Tail records w.ambient.hidden))
      (fun _ h=>h) (by rintro result w ⟨rfl,post⟩; exact ⟨post,by intro value bad; cases bad⟩)
  · apply hoare_bind _ _ (sendWorker_strict records)
    intro _
    apply hoare_bind _ _ (retain_strict _ (fun rs=>schedule_retains rs none) records)
    intro _
    exact hoare_consequence (hoare_pure (ForInStep.yield ((none,()) : Option Unit×Unit)) (fun w : World=>StrictTail records w.ambient.hidden))
      (fun _ h=>h) (by rintro result w ⟨rfl,post⟩; exact ⟨strict_tail post,fun _ _=>post⟩)

theorem sendCompletionLoop_normal_done (turns : List Nat) (records : List HiddenRecord)
    (before after : World) (result : Option Unit×Unit)
    (present : before.ambient.hidden=some records)
    (enough : records.length<turns.length)
    (run : (forIn turns ((none,()) : Option Unit×Unit) sendCompletionTurn).run before=.ok (result,after)) :
    result.1.isSome=true := by
  apply forIn_record_budget_done sendCompletionTurn (fun value=>value.1.isSome=true)
    ?_ turns (none,()) records before after result present enough run
  intro index state input
  apply (hoare_iff_run _ _ _).mpr
  intro entry out final stored executed
  cases out with
  | done value=>exact (sendCompletionTurn_completion index state entry final (.done value) executed).1
  | yield value=>
    exact ((hoare_iff_run _ _ _).mp (sendCompletionTurn_record_effect input index state)
      entry (.yield value) final (stored ▸ tail_self input) executed).2 value rfl

theorem runSendWorkers_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.runSendWorkers := by
  rw [runSendWorkers_completion_source]
  apply preserves_bind (stack_getWG_retains records)
  intro g
  split
  · exact preserves_pure _
  · apply preserves_bind (requireNoCryptWork_retains records)
    intro _
    apply preserves_bind (native_product records _ (native_modify records (fun g=>{g with queuedThisCall:=[]})))
    intro _
    apply preserves_bind (recordBudget_retains records)
    intro budget
    apply preserves_bind
    · apply list_view_spec (fun w : World=>w.ambient.hidden) (Tail records)
      intro index state
      exact hoare_consequence (sendCompletionTurn_record_effect records index state)
        (fun _ h=>h) (fun _ _ h=>h.1)
    intro result
    cases result.1 with
    | some value=>exact preserves_pure _
    | none=>
      apply (hoare_iff_run _ _ _).mpr
      intro before value after pre run
      change ((AmbientM.budgetExhausted "the send work queue").run before.ambient >>= _) = _ at run
      dsimp only [AmbientM.budgetExhausted,StateT.run,StateT.bind,get,getThe,
        MonadStateOf.get,StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure] at run
      cases hidden : before.ambient.hidden <;> rw [hidden] at run
      all_goals change Except.error _ = Except.ok _ at run
      all_goals cases run

theorem runSendWorkers_supplied_source (records : List HiddenRecord)
    (before : World) (present : before.ambient.hidden=some records) :
    Env.runSendWorkers.run before =
      ((do
        if (←getWG).dev.isNone then return
        requireNoCryptWork
        modifyWG fun g=>{g with queuedThisCall:=[]}
        let _←forIn (List.range' 0 (records.length+1))
          ((none,()) : Option Unit×Unit) sendCompletionTurn
        pure () : Leanux.M Unit).run before) := by
  rw [runSendWorkers_completion_source]
  simp only [StateT.run_bind]
  change ((Except.ok (before.wg,before) : Except Stop _) >>= _) =
    ((Except.ok (before.wg,before) : Except Stop _) >>= _)
  dsimp only [Bind.bind,Except.bind]
  cases absent : before.wg.dev.isNone with
  | true => simp only [ite_true]
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    change (Env.requireNoCryptWork.run before >>= _) = (Env.requireNoCryptWork.run before >>= _)
    cases required : Env.requireNoCryptWork.run before with
    | error stop=>rfl
    | ok pair=>
      obtain ⟨ignored,middle⟩:=pair
      have stored:=(hoare_iff_run _ _ _).mp (requireNoCryptWork_hidden (some records))
        before ignored middle present required
      let entry : World := {middle with wg:={middle.wg with queuedThisCall:=[]}}
      have budget : (recordBudget : Leanux.M Nat).run entry=.ok (records.length+1,entry) := by
        change Except.ok ((match middle.ambient.hidden with
          | some rs=>rs.length+1
          | none=>DOMAIN_FILTER_TURNS),entry)=_
        rw [stored]
      dsimp only [Bind.bind,Except.bind]
      change ((modifyWG (fun g=>{g with queuedThisCall:=[]}) : Leanux.M Unit).run middle >>= _) =
        ((modifyWG (fun g=>{g with queuedThisCall:=[]}) : Leanux.M Unit).run middle >>= _)
      have edited : (modifyWG (fun g=>{g with queuedThisCall:=[]}) : Leanux.M Unit).run middle =
          .ok ((),entry) := rfl
      rw [edited]
      dsimp only [StateT.bind,StateT.run,Bind.bind,Except.bind]
      change (recordBudget : Leanux.M Nat) entry=.ok (records.length+1,entry) at budget
      rw [budget]
      dsimp only

      cases loop : (forIn (List.range' 0 (records.length+1))
          ((none,()) : Option Unit×Unit) sendCompletionTurn) entry with
      | error stop=>rfl
      | ok pair=>
        obtain ⟨state,after⟩:=pair
        have done:=sendCompletionLoop_normal_done (List.range' 0 (records.length+1))
          records entry after state stored (by simp only [List.length_range']; omega) loop
        cases state with
        | mk result unused=>
          cases unused
          cases result with
          | none=>cases done
          | some value=>cases value; rfl

end Leanux.Proofs.WG.Progress.RecordSuffix
