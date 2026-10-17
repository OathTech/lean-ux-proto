import Leanux.Proofs.WG.TimerDiscipline.OuterAdjacentModel
import Leanux.Proofs.WG.TimerDiscipline.OuterAdjacentFrames
import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeSource
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- A normal actual send turn yields the actual worker run. Any step guard or
section failure is excluded by that normal turn, never assumed away at entry. -/
theorem timerOuterTurn_send_run (jPass : UInt64) (iteration : Nat) (control : TimerOuterControl)
    (initial final : World) (result : ForInStep TimerOuterControl) (d : Device)
    (device : initial.wg.dev = some d) (nonempty : d.sendWorkQueue.isEmpty = false)
    (fired : control.1 = true)
    (site : (initial.ambient.hidden.bind fun rs =>
      (rs.find? fun r => !HiddenSite.passive r.site).map (·.site)) =
        some (HiddenSite.sectionStart .sendWorker).info.id)
    (run : (timerOuterTurn jPass iteration control).run initial = .ok (result,final)) :
    Env.runOneSendWorker.run initial = .ok ((),final) := by
  have peek : peekNextSite.run initial = .ok (some (HiddenSite.sectionStart .sendWorker).info.id,initial) := by
    unfold peekNextSite
    rw [StateT.run_bind]
    change ((Except.ok (initial.ambient,initial) : Except Stop _) >>= _) = _
    dsimp only [Bind.bind,Except.bind]
    cases hidden : initial.ambient.hidden with
    | none => simp [hidden] at site
    | some rs =>
      change Except.ok ((rs.find? fun r => !HiddenSite.passive r.site).map (·.site),initial) = _
      simpa only [hidden,Option.bind_some] using congrArg (fun x => Except.ok (x,initial)) site
  have read : (getDev : Leanux.M Device).run initial = .ok (d,initial) := by
    change (((getDev).run initial.wg).run initial.ambient >>= fun ((value,g),a) =>
      Except.ok (value,{initial with wg := g,ambient := a})) = _
    simp [getDev,device]
  have notTimer : timerSectionOf (HiddenSite.sectionStart .sendWorker).info.id = none := by decide
  unfold timerOuterTurn at run
  rw [StateT.run_bind,peek] at run
  change ((getDev : Leanux.M Device).run initial >>= _) = _ at run
  rw [read] at run
  dsimp only [Bind.bind,Except.bind] at run
  simp only [notTimer,fired,Bool.not_true,Bool.false_eq_true,ite_false,
    BEq.rfl,nonempty,Bool.not_false,Bool.and_self,ite_true] at run
  have suffix (middle : World)
      (h : ((do Env.runOneSendWorker; pure (ForInStep.yield (true,none)) : Leanux.M _).run middle) =
        .ok (result,final)) : Env.runOneSendWorker.run middle = .ok ((),final) := by
    rw [StateT.run_bind] at h
    cases actual : Env.runOneSendWorker.run middle with
    | error stop => rw [actual] at h; cases h
    | ok out =>
      obtain ⟨value,last⟩ := out
      cases value
      rw [actual] at h
      have same : last = final := congrArg Prod.snd (Except.ok.inj h)
      rw [same]
  cases step : control.2 with
  | none =>
    simp only [step] at run
    exact suffix initial run
  | some bucket =>
    simp only [step] at run
    change ((requireStepComplete bucket).run initial >>= fun out =>
      ((do Env.runOneSendWorker; pure (ForInStep.yield (true,none)) : Leanux.M _).run out.2)) = _ at run
    cases checked : (requireStepComplete bucket).run initial with
    | error stop => rw [checked] at run; cases run
    | ok out =>
      obtain ⟨value,middle⟩ := out
      cases value
      have same := requireStepComplete_sameState bucket initial middle checked
      subst middle
      rw [checked] at run
      exact suffix initial run


/-- The pair's concrete runs are supplied by the actual observer, not recovered
from projected snapshot equality. The certificate's inspections use that same
concrete pre-timer state. -/
theorem observedTimerOuterTurns_pair (jPass : UInt64) (i k : Nat)
    (control next : TimerOuterControl) (step : ForInStep TimerOuterControl)
    (initial middle final : World) (left right : OuterTimerTurnReceipt)
    (first : (observedTimerOuterTurn jPass i control).run initial = .ok ((.yield next,left),middle))
    (second : (observedTimerOuterTurn jPass k next).run middle = .ok ((step,right),final)) :
    OuterAdjacentRetryPair jPass left right := by
  intro d after pid we device empty selected site afterDevice nonempty
  obtain ⟨_,before,controlEq,resultEq,afterEq,valid⟩ :=
    observedTimerOuterTurn_valid jPass i control initial middle (.yield next) left first
  obtain ⟨_,rightBefore,_,_,rightAfter,_⟩ :=
    observedTimerOuterTurn_valid jPass k next middle final step right second
  rw [before] at selected device
  rw [rightBefore] at site afterDevice
  have firstActual : (timerOuterTurn jPass i control).run initial = .ok (.yield next,middle) := by
    rw [← observedTimerOuterTurn_erase,StateT.run_bind,first]
    rfl
  have secondActual : (timerOuterTurn jPass k next).run middle = .ok (step,final) := by
    rw [← observedTimerOuterTurn_erase,StateT.run_bind,second]
    rfl
  have dispatchRun := firstActual
  rw [timerOuterTurn_selected_run jPass i control initial _ selected] at dispatchRun
  cases dispatched : (timerDispatchUnit_variant .timerRetransmit pid .retransmitHandshake we control.2).run initial with
  | error stop => rw [dispatched] at dispatchRun; cases dispatchRun
  | ok out =>
    obtain ⟨value,afterUnit⟩ := out
    cases value
    rw [dispatched] at dispatchRun
    have stateEq : afterUnit = middle := congrArg Prod.snd (Except.ok.inj dispatchRun)
    have nextEq : next = (true,some we.bucketExpiry) := by
      have eq := congrArg Prod.fst (Except.ok.inj dispatchRun)
      exact (ForInStep.yield.inj eq).symm
    subst afterUnit
    have workerRun := timerOuterTurn_send_run jPass k next middle final step after afterDevice nonempty
      (by rw [nextEq]) site secondActual
    let unit : RetryUnit := ⟨pid,we,control.2⟩
    let observation : RetryDispatchObservation := {
      timer := Campaign2.Product.observeResult
        ((timerExecutionPath .timerRetransmit pid .retransmitHandshake we control.2).run initial)
      afterTimer := Campaign2.Product.snapshot middle
      inspection := Campaign2.Product.observeResult ((retryInspectionPath unit).run initial)
      send := Campaign2.Product.observeResult (sendWorkerExecution.run middle) }
    have observedRun : (observedRetryDispatch unit).run initial = .ok (observation,final) := by
      rw [observedRetryDispatch_run]
      change ((timerDispatchUnit_variant .timerRetransmit pid .retransmitHandshake we control.2).run initial >>= _) = _
      rw [dispatched]
      change (Env.runOneSendWorker.run middle >>= _) = _
      rw [workerRun]; rfl
    have certificate := source_retry_dispatch d unit empty initial observation final device observedRun
    refine ⟨observation,?_,afterEq.symm,?_⟩
    · simpa only [controlEq,rightAfter] using certificate
    have recorded : left.unit = Campaign2.Product.observeResult ((timerOuterProbe jPass control).run initial) := by
      change (((timerOuterTurn jPass i control).run initial >>= fun out =>
        Except.ok ((Campaign2.Product.observeResult ((timerOuterProbe jPass control).run initial),out.1),out.2)) >>= fun out =>
        Except.ok ((out.1.2,(⟨i,Campaign2.Product.snapshot initial,control,out.1.2,out.1.1,
          Campaign2.Product.snapshot out.2⟩ : OuterTimerTurnReceipt)),out.2)) = _ at first
      rw [firstActual] at first
      exact (congrArg (fun out => out.1.2.unit) (Except.ok.inj first)).symm
    rw [recorded]
    change Campaign2.Product.observeResult ((timerOuterProbe jPass control).run initial) =
      (Campaign2.Product.observeResult ((timerExecutionPath .timerRetransmit pid .retransmitHandshake we control.2).run initial)).map _
    have probe : (timerOuterProbe jPass control).run initial =
        ((timerExecutionPath .timerRetransmit pid .retransmitHandshake we control.2).run initial >>= fun out =>
          Except.ok (some (⟨⟨.timerRetransmit,pid,.retransmitHandshake,we⟩,out.1.2.2⟩ : OuterTimerUnitReceipt),out.2)) := by
      change ((match outerTimerChoice jPass (Campaign2.Product.snapshot initial) with
        | none => pure none
        | some choice => do
          let value ← timerExecutionPath choice.worker choice.pid choice.timer choice.wheel control.2
          pure (some (⟨choice,value.2.2⟩ : OuterTimerUnitReceipt)) : Leanux.M (Option OuterTimerUnitReceipt)).run initial) = _
      rw [selected]; rfl
    rw [probe]
    cases path : (timerExecutionPath .timerRetransmit pid .retransmitHandshake we control.2).run initial <;> rfl

private theorem observedTimerOuterTurns_head (jPass : UInt64) (indices : List Nat)
    (control last : TimerOuterControl) (initial final : World)
    (receipt : OuterTimerTurnReceipt) (receipts : List OuterTimerTurnReceipt)
    (run : (observedTimerOuterTurns jPass indices control).run initial =
      .ok ((last,receipt :: receipts),final)) :
    ∃ i step middle, (observedTimerOuterTurn jPass i control).run initial = .ok ((step,receipt),middle) := by
  cases indices with
  | nil => cases run
  | cons i rest =>
    rw [observedTimerOuterTurns,StateT.run_bind] at run
    cases first : (observedTimerOuterTurn jPass i control).run initial with
    | error stop => rw [first] at run; cases run
    | ok out =>
      obtain ⟨⟨step,head⟩,middle⟩ := out
      rw [first] at run
      cases step with
      | done next =>
        change Except.ok ((next,[head]),middle) = _ at run
        have eq : head = receipt := by
          have listEq := congrArg (fun out => out.1.2.head?) (Except.ok.inj run)
          exact Option.some.inj listEq
        subst head
        exact ⟨i,.done next,middle,first⟩
      | yield next =>
        change ((observedTimerOuterTurns jPass rest next).run middle >>= fun out =>
          Except.ok ((out.1.1,head :: out.1.2),out.2)) = _ at run
        cases remaining : (observedTimerOuterTurns jPass rest next).run middle with
        | error stop => rw [remaining] at run; cases run
        | ok out =>
          rw [remaining] at run
          have eq : head = receipt := by
            have listEq := congrArg (fun out => out.1.2.head?) (Except.ok.inj run)
            exact Option.some.inj listEq
          subst head
          exact ⟨i,.yield next,middle,first⟩

/-- Adjacent receipts have consecutive concrete runs in this actual source
execution. No concrete state is reconstructed from their projected fields. -/
theorem observedTimerOuterTurns_adjacent_run (jPass : UInt64) (indices : List Nat)
    (control last : TimerOuterControl) (initial final : World)
    (receipts front suffix : List OuterTimerTurnReceipt) (left right : OuterTimerTurnReceipt)
    (run : (observedTimerOuterTurns jPass indices control).run initial = .ok ((last,receipts),final))
    (adjacent : receipts = front ++ left :: right :: suffix) :
    ∃ i k before next step start middle finish,
      (observedTimerOuterTurn jPass i before).run start = .ok ((.yield next,left),middle) ∧
      (observedTimerOuterTurn jPass k next).run middle = .ok ((step,right),finish) := by
  induction indices generalizing control initial final last receipts front with
  | nil =>
    cases run
    have count := congrArg List.length adjacent
    simp only [List.length_nil,List.length_append,List.length_cons] at count
    omega
  | cons i rest ih =>
    rw [observedTimerOuterTurns,StateT.run_bind] at run
    cases first : (observedTimerOuterTurn jPass i control).run initial with
    | error stop => rw [first] at run; cases run
    | ok out =>
      obtain ⟨⟨step,head⟩,middle⟩ := out
      rw [first] at run
      cases step with
      | done next =>
        change Except.ok ((next,[head]),middle) = _ at run
        have lists := congrArg (fun out => out.1.2) (Except.ok.inj run)
        dsimp only at lists
        rw [← lists] at adjacent
        have count := congrArg List.length adjacent
        simp only [List.length_nil,List.length_append,List.length_cons] at count
        omega
      | yield next =>
        change ((observedTimerOuterTurns jPass rest next).run middle >>= fun out =>
          Except.ok ((out.1.1,head :: out.1.2),out.2)) = _ at run
        cases tailRun : (observedTimerOuterTurns jPass rest next).run middle with
        | error stop => rw [tailRun] at run; cases run
        | ok out =>
          obtain ⟨⟨lastControl,tail⟩,lastState⟩ := out
          rw [tailRun] at run
          have lists := congrArg (fun out => out.1.2) (Except.ok.inj run)
          dsimp only at lists
          rw [← lists] at adjacent
          cases front with
          | nil =>
            simp only [List.nil_append,List.cons.injEq] at adjacent
            obtain ⟨sameHead,sameTail⟩ := adjacent
            subst head
            rw [sameTail] at tailRun
            obtain ⟨k,step,finish,second⟩ :=
              observedTimerOuterTurns_head jPass rest next lastControl middle lastState right suffix tailRun
            exact ⟨i,k,control,next,step,initial,middle,finish,first,second⟩
          | cons prior front =>
            simp only [List.cons_append,List.cons.injEq] at adjacent
            exact ih next lastControl middle lastState tail front tailRun adjacent.2


end Leanux.Proofs.WG.TimerDiscipline
