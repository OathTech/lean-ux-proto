import Leanux.Proofs.WG.Progress.BatchDrainModel
import Leanux.Proofs.WG.Progress.SchedulerRecordSource
import Leanux.Proofs.WG.Progress.TimerLoopRecordFrames
import Leanux.Proofs.WG.Progress.RecordBudgetSource

/-! Exact recorded afterBatch turn factoring and record-budget adequacy. This scope ends before afterBatchDrainSuffix; no completion guard is assumed or changed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

/-- The unchanged body of one recorded batch turn; the following source equation establishes correspondence before its contracts are used. -/
def afterBatchRecordedTurn (_ : Nat) (_ : Unit) : Leanux.M (ForInStep Unit) := do
  schedule
  if (← peekNextSite)==some (HiddenSite.sectionStart .sendWorker).info.id &&
      !(← getDev).sendWorkQueue.isEmpty then
    runOneSendWorker
    return .yield ()
  else
    return .done ()

/-- Exact original loop factor, preserving scheduling, both reads, queue selection, send callback and break order on all outcomes. -/
theorem afterBatchRecordedLoop_source :
    afterBatchRecordedLoop = (do
      let budget ← recordBudget
      let _ ← forIn [0:budget] () afterBatchRecordedTurn
      pure ()) := by
  unfold afterBatchRecordedLoop afterBatchRecordedTurn
  rfl

/-- Every normal yielded turn has run the real send worker after the actual scheduler. Its section records make the decrease strict. -/
theorem afterBatchRecordedTurn_record_effect (records : List HiddenRecord) (iteration : Nat) :
    Hoare (afterBatchRecordedTurn iteration ())
      (fun w=>Tail records w.ambient.hidden)
      (fun result w=>Tail records w.ambient.hidden ∧
        (result=.yield ()→StrictTail records w.ambient.hidden)) := by
  have get : Preserves (fun w : World=>Tail records w.ambient.hidden)
      (getDev : Leanux.M Device):=native_product records _ (native_getDev records)
  have finish : Hoare (pure (.done ()) : Leanux.M (ForInStep Unit))
      (fun w=>Tail records w.ambient.hidden)
      (fun result w=>Tail records w.ambient.hidden ∧
        (result=.yield ()→StrictTail records w.ambient.hidden)) := by
    apply hoare_consequence (hoare_pure (ForInStep.done ()) (fun w : World=>Tail records w.ambient.hidden))
      (fun _ h=>h)
    intro result final post
    refine ⟨post.2,?_⟩
    intro impossible
    have absurd : ForInStep.done ()=ForInStep.yield ():=post.1.symm.trans impossible
    cases absurd
  have sent : Hoare (do runOneSendWorker; pure (.yield ()) : Leanux.M (ForInStep Unit))
      (fun w=>Tail records w.ambient.hidden)
      (fun result w=>Tail records w.ambient.hidden ∧
        (result=.yield ()→StrictTail records w.ambient.hidden)) := by
    apply hoare_bind _ _ (sendWorker_strict records)
    intro _
    apply hoare_consequence (hoare_pure (ForInStep.yield ()) (fun w : World=>StrictTail records w.ambient.hidden))
      (fun _ h=>h)
    intro result final post
    exact ⟨strict_tail post.2,fun _=>post.2⟩
  unfold afterBatchRecordedTurn
  apply hoare_bind _ _ (schedule_retains records none)
  intro _
  apply hoare_bind _ _ (peekNextSite_retains records)
  intro next
  apply hoare_bind _ _ get
  intro d
  split
  · exact sent
  · exact finish

/-- Concrete normal yielded-turn decrease with no callback premise. -/
theorem afterBatchRecordedTurn_yield_strict (iteration : Nat)
    (records : List HiddenRecord) (before after : World)
    (present : before.ambient.hidden=some records)
    (run : (afterBatchRecordedTurn iteration ()).run before=.ok (.yield (),after)) :
    StrictTail records after.ambient.hidden :=
  ((hoare_iff_run _ _ _).mp (afterBatchRecordedTurn_record_effect records iteration)
    before (.yield ()) after (present ▸ tail_self records) run).2 rfl

/-- The original read captures exactly the supplied record count plus one. -/
theorem afterBatchRecordedLoop_supplied_source (records : List HiddenRecord)
    (before : World) (present : before.ambient.hidden=some records) :
    afterBatchRecordedLoop.run before=
      ((do
        let _ ← forIn (List.range' 0 (records.length+1)) () afterBatchRecordedTurn
        pure () : Leanux.M Unit).run before) := by
  have budget : (recordBudget : Leanux.M Nat).run before=.ok (records.length+1,before) := by
    change Except.ok ((match before.ambient.hidden with
      | some rs=>rs.length+1
      | none=>DOMAIN_FILTER_TURNS),before)=_
    rw [present]
  rw [afterBatchRecordedLoop_source,StateT.run_bind,budget]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  rfl

/-- Arbitrary appended turns cannot change the exact outcome or final World after the original captured budget. Original callback Stops are preserved. -/
theorem afterBatchRecordedLoop_extra_turns (records : List HiddenRecord) (extra : List Nat)
    (before : World) (present : before.ambient.hidden=some records) :
    afterBatchRecordedLoop.run before=
      ((do
        let _ ← forIn (List.range' 0 (records.length+1)++extra) () afterBatchRecordedTurn
        pure () : Leanux.M Unit).run before) := by
  rw [afterBatchRecordedLoop_supplied_source records before present,StateT.run_bind,StateT.run_bind]
  have equal:=forIn_record_budget_append afterBatchRecordedTurn
    (fun index state next rs initial final stored run=>by
      cases state
      cases next
      exact afterBatchRecordedTurn_yield_strict index rs initial final stored run)
    (List.range' 0 (records.length+1)) extra () records before present
      (by simp only [List.length_range']; omega)
  rw [equal]

end Leanux.Proofs.WG.Progress.RecordSuffix
