import Leanux.Proofs.WG.Progress.TimerLoopRecordFrames
import Leanux.Proofs.WG.TimerDiscipline.WheelDispatchSource

/-! Normal timer-unit dispatch strictly consumes supplied records through the
original guards, timer callback section and final pass-step reset. The proof
reuses one local continuation contract and leaves every Stop branch intact. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing
open Leanux.Proofs.WG.TimerDiscipline

theorem timerDispatchUnit_strict (records : List HiddenRecord) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) (step : Option UInt64) :
    Hoare (timerDispatchUnit_variant worker pid timer entry step)
      (fun w=>Tail records w.ambient.hidden) (fun _ w=>StrictTail records w.ambient.hidden) := by
  let finish : Leanux.M Unit := do
    delTimer pid timer
    modifyWG fun g=>{g with timerPassStep:=some entry.bucketExpiry}
    runTimerSection worker (WG.timerCallback pid timer)
    modifyWG fun g=>{g with timerPassStep:=none}
  have finished : Hoare finish (fun w=>Tail records w.ambient.hidden)
      (fun _ w=>StrictTail records w.ambient.hidden) := by
    unfold finish
    apply hoare_bind _ _ (native_product records _ (delTimer_retains records pid timer))
    intro _
    apply hoare_bind _ _ (native_product records _
      (native_modify records (fun g=>{g with timerPassStep:=some entry.bucketExpiry})))
    intro _
    apply hoare_bind _ _ (timerSection_strict records worker pid timer)
    intro _
    exact retain_strict _ (fun rs=>native_product rs _
      (native_modify rs (fun g=>{g with timerPassStep:=none}))) records
  have afterStep (prior : Option UInt64) :
      Hoare (do
        if let some b:=prior then
          if b != entry.bucketExpiry then requireStepComplete b
        finish)
        (fun w=>Tail records w.ambient.hidden) (fun _ w=>StrictTail records w.ambient.hidden) := by
    cases prior with
    | none => exact finished
    | some b =>
      dsimp only
      by_cases changed : (b != entry.bucketExpiry) = true
      · simp only [changed,ite_true]
        exact hoare_bind _ _ (requireStepComplete_retains records b) (fun _=>finished)
      · simp only [changed]
        exact finished
  unfold timerDispatchUnit_variant
  apply hoare_bind _ _ (timerWorker_retains records timer)
  intro expected
  by_cases wrong : (worker != expected) = true
  · simp only [wrong,ite_true]
    exact hoare_throw _
  · simp only [wrong]
    apply hoare_bind _ _ (peekUnit_retains records worker)
    intro unit
    cases unit with
    | none => exact afterStep step
    | some unit =>
      apply hoare_bind _ _ (stack_getWG_retains records)
      intro g
      cases found : g.timerUnits.find? (·.1 == unit) with
      | none =>
        dsimp only
        exact hoare_throw _
      | some target =>
        obtain ⟨unit',pid',timer'⟩:=target
        dsimp only
        by_cases different : (pid' != pid || timer' != timer) = true
        · simp only [different,ite_true]
          exact hoare_throw _
        · simp only [different]
          exact afterStep step

theorem timerDispatchUnit_retains (records : List HiddenRecord) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) (step : Option UInt64) :
    Preserves (fun w : World=>Tail records w.ambient.hidden)
      (timerDispatchUnit_variant worker pid timer entry step) :=
  hoare_consequence (timerDispatchUnit_strict records worker pid timer entry step)
    (fun _ h=>h) (fun _ _ h=>strict_tail h)

end Leanux.Proofs.WG.Progress.RecordSuffix
