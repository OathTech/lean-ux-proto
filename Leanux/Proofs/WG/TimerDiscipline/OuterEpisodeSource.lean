import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeModel
import Leanux.Proofs.WG.TimerDiscipline.OuterFirstTurnSource
import Leanux.Proofs.WG.TimerDiscipline.ObservationBridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- The probe inspects the selected unit at the turn's actual entry. It never
changes the continuing state, including when its selected unit would stop. -/
def timerOuterProbe (jPass : UInt64) (control : TimerOuterControl) : Leanux.M (Option OuterTimerUnitReceipt) := do
  let entry ← Campaign2.Product.read
  match outerTimerChoice jPass entry with
  | none => return none
  | some choice =>
    let selected ← timerExecutionPath choice.worker choice.pid choice.timer choice.wheel control.2
    return some ⟨choice,selected.2.2⟩

def observedTimerOuterTurn (jPass : UInt64) (iteration : Nat) (control : TimerOuterControl) :
    Leanux.M (ForInStep TimerOuterControl × OuterTimerTurnReceipt) := fun initial =>
  (observed (timerOuterTurn jPass iteration control) (timerOuterProbe jPass control)).run initial >>= fun out =>
    .ok ((out.1.2,⟨iteration,Campaign2.Product.snapshot initial,control,out.1.2,out.1.1,
      Campaign2.Product.snapshot out.2⟩),out.2)

/-- Exact original turn when its own current record and wheel choose a timer. -/
private theorem timerOuterTurn_selected_run (jPass : UInt64) (iteration : Nat)
    (control : TimerOuterControl) (initial : World) (choice : OuterTimerChoice)
    (chosen : outerTimerChoice jPass (Campaign2.Product.snapshot initial) = some choice) :
    (timerOuterTurn jPass iteration control).run initial =
      ((timerDispatchUnit_variant choice.worker choice.pid choice.timer choice.wheel control.2).run initial
        >>= fun out => Except.ok (.yield (true,some choice.wheel.bucketExpiry),out.2)) := by
  cases site : initial.ambient.hidden.bind (fun rs => (rs.find? fun (r : HiddenRecord) => !HiddenSite.passive r.site).map HiddenRecord.site) with
  | none => simp [outerTimerChoice,Campaign2.Product.snapshot,Campaign2.snapshot,site] at chosen
  | some siteValue =>
    cases worker : timerSectionOf siteValue with
    | none => simp [outerTimerChoice,Campaign2.Product.snapshot,Campaign2.snapshot,site,worker] at chosen
    | some w =>
      by_cases clear : (w == .clearPeerWorker) = true
      · simp [outerTimerChoice,Campaign2.Product.snapshot,Campaign2.snapshot,site,worker,clear] at chosen
      · cases device : initial.wg.dev with
        | none => simp [outerTimerChoice,Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core,site,device] at chosen
        | some d =>
          cases wheel : TimerWheel.nextDue d jPass with
          | none => simp [outerTimerChoice,Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core,site,device,wheel] at chosen
          | some tuple =>
            obtain ⟨pid,timer,we⟩ := tuple
            simp [outerTimerChoice,Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core,site,worker,clear,device,wheel] at chosen
            cases chosen
            have peek : peekNextSite.run initial = .ok (some siteValue,initial) := by
              unfold peekNextSite
              rw [StateT.run_bind]
              change ((Except.ok (initial.ambient,initial) : Except Stop _) >>= _) = _
              dsimp only [Bind.bind,Except.bind]
              cases hidden : initial.ambient.hidden with
              | none => simp [hidden] at site
              | some rs =>
                change Except.ok ((rs.find? fun r => !HiddenSite.passive r.site).map (·.site),initial) = _
                simpa only [hidden,Option.bind_some] using congrArg (fun x => Except.ok (x,initial)) site
            have getDevice : (getDev : Leanux.M Device).run initial = .ok (d,initial) := by
              change (((getDev).run initial.wg).run initial.ambient >>= fun ((value,g),a) =>
                Except.ok (value,{initial with wg := g,ambient := a})) = _
              simp [getDev,device]
            unfold timerOuterTurn
            rw [StateT.run_bind,peek]
            change ((getDev : Leanux.M Device).run initial >>= _) = _
            rw [getDevice]
            dsimp only [Bind.bind,Except.bind]
            simp only [worker,clear,wheel]
            rfl

/-- Exact state and error erasure for one observed actual turn. -/
theorem observedTimerOuterTurn_erase (jPass : UInt64) (iteration : Nat) (control : TimerOuterControl) :
    (do let result ← observedTimerOuterTurn jPass iteration control; pure result.1) =
      timerOuterTurn jPass iteration control := by
  funext initial
  change (((((observed (timerOuterTurn jPass iteration control) (timerOuterProbe jPass control)).run initial) >>= fun out =>
    Except.ok ((out.1.2,(⟨iteration,Campaign2.Product.snapshot initial,control,out.1.2,out.1.1,
      Campaign2.Product.snapshot out.2⟩ : OuterTimerTurnReceipt)),out.2)) >>= fun out => Except.ok (out.1.1,out.2))) = _
  change ((((timerOuterTurn jPass iteration control).run initial >>= fun out =>
    Except.ok ((Campaign2.Product.observeResult ((timerOuterProbe jPass control).run initial),out.1),out.2)) >>= _) >>= _) = _
  change _ = (timerOuterTurn jPass iteration control).run initial
  cases run : (timerOuterTurn jPass iteration control).run initial <;> rfl

/-- Every normal turn records its actual entry and exit. A selected timer
receipt is the actual unit's immediate exit, before later outer turns. -/
theorem observedTimerOuterTurn_valid (jPass : UInt64) (iteration : Nat) (control : TimerOuterControl)
    (initial final : World) (step : ForInStep TimerOuterControl) (receipt : OuterTimerTurnReceipt)
    (run : (observedTimerOuterTurn jPass iteration control).run initial = .ok ((step,receipt),final)) :
    receipt.iteration = iteration ∧ receipt.before = Campaign2.Product.snapshot initial ∧
    receipt.control = control ∧ receipt.result = step ∧ receipt.after = Campaign2.Product.snapshot final ∧
    OuterTimerTurnValid jPass receipt := by
  change (((timerOuterTurn jPass iteration control).run initial >>= fun out =>
    Except.ok ((Campaign2.Product.observeResult ((timerOuterProbe jPass control).run initial),out.1),out.2)) >>= fun out =>
    Except.ok ((out.1.2,(⟨iteration,Campaign2.Product.snapshot initial,control,out.1.2,out.1.1,
      Campaign2.Product.snapshot out.2⟩ : OuterTimerTurnReceipt)),out.2)) = _ at run
  cases actual : (timerOuterTurn jPass iteration control).run initial with
  | error stop => rw [actual] at run; cases run
  | ok pair =>
    obtain ⟨out,next⟩ := pair
    rw [actual] at run
    cases run
    refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
    cases choice : outerTimerChoice jPass (Campaign2.Product.snapshot initial) with
    | none =>
      unfold OuterTimerTurnValid
      rw [choice]
      change Campaign2.Product.observeResult ((timerOuterProbe jPass control).run initial) = _
      have probe : (timerOuterProbe jPass control).run initial = .ok (none,initial) := by
        change ((match outerTimerChoice jPass (Campaign2.Product.snapshot initial) with
          | none => pure none
          | some c => do
            let selected ← timerExecutionPath c.worker c.pid c.timer c.wheel control.2
            pure (some (⟨c,selected.2.2⟩ : OuterTimerUnitReceipt)) : Leanux.M (Option OuterTimerUnitReceipt)).run initial) = _
        rw [choice]; rfl
      exact observe_ok probe
    | some unit =>
      have unitRun := actual
      rw [timerOuterTurn_selected_run jPass iteration control initial unit choice] at unitRun
      cases dispatch : (timerDispatchUnit_variant unit.worker unit.pid unit.timer unit.wheel control.2).run initial with
      | error stop => rw [dispatch] at unitRun; cases unitRun
      | ok pair =>
        obtain ⟨value,afterUnit⟩ := pair
        cases value
        rw [dispatch] at unitRun
        cases unitRun
        have resident : ∃d, initial.wg.dev = some d := by
          cases device : initial.wg.dev with
          | none => simp [outerTimerChoice,Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core,device] at choice
          | some d => exact ⟨d,rfl⟩
        obtain ⟨d,device⟩ := resident
        obtain ⟨selected,prefixRun,callback,kind,sameDevice⟩ :=
          fireTimer_execution unit.worker unit.pid unit.timer unit.wheel control.2 initial afterUnit d device dispatch
        have path : (timerExecutionPath unit.worker unit.pid unit.timer unit.wheel control.2).run initial =
            .ok ((unit.pid,unit.timer,Campaign2.Product.snapshot selected),afterUnit) := by
          simp only [timerExecutionPath,StateT.run_bind,prefixRun]
          change ((fireWheelSelected unit.worker unit.pid unit.timer unit.wheel).run selected >>= fun out =>
            Except.ok ((unit.pid,unit.timer,Campaign2.Product.snapshot selected),out.2)) = _
          rw [callback]; rfl
        have probe : (timerOuterProbe jPass control).run initial =
            .ok (some ⟨unit,Campaign2.Product.snapshot selected⟩,afterUnit) := by
          change ((match outerTimerChoice jPass (Campaign2.Product.snapshot initial) with
            | none => pure none
            | some c => do
              let selected ← timerExecutionPath c.worker c.pid c.timer c.wheel control.2
              pure (some (⟨c,selected.2.2⟩ : OuterTimerUnitReceipt)) : Leanux.M (Option OuterTimerUnitReceipt)).run initial) = _
          rw [choice,StateT.run_bind,path]; rfl
        change OuterTimerTurnValid jPass _
        unfold OuterTimerTurnValid
        simp only [choice]
        refine ⟨Campaign2.Product.snapshot selected,observe_ok probe,True.intro,kind,sameDevice.trans device.symm,?_⟩
        intro identity attempts expiry retransmit before
        have worker : unit.worker = .timerRetransmit := by
          rw [retransmit] at kind
          cases h : unit.worker <;> simp_all [Worker.timer?]
        have effect := fireSelected_retransmit unit.pid unit.wheel identity attempts expiry
          selected () afterUnit before (by simpa only [worker,retransmit] using callback)
        exact effect

/-- Source-specific finite loop with the original break/continue behavior. -/
def observedTimerOuterTurns (jPass : UInt64) : List Nat → TimerOuterControl →
    Leanux.M (TimerOuterControl × List OuterTimerTurnReceipt)
  | [], control => pure (control,[])
  | iteration :: rest, control => do
      let (step,receipt) ← observedTimerOuterTurn jPass iteration control
      match step with
      | .done next => pure (next,[receipt])
      | .yield next =>
          let (final,receipts) ← observedTimerOuterTurns jPass rest next
          pure (final,receipt :: receipts)

/-- All original errors and every concrete Product state are retained. -/
theorem observedTimerOuterTurns_erase (jPass : UInt64) (indices : List Nat) (control : TimerOuterControl) :
    (do let result ← observedTimerOuterTurns jPass indices control; pure result.1) =
      forIn indices control (timerOuterTurn jPass) := by
  induction indices generalizing control with
  | nil => rfl
  | cons iteration rest ih =>
    simp only [observedTimerOuterTurns,List.forIn_cons,bind_assoc]
    have erase := observedTimerOuterTurn_erase jPass iteration control
    rw [← erase]
    simp only [bind_assoc,pure_bind]
    apply bind_congr
    intro result
    rcases result with ⟨step,receipt⟩
    cases step with
    | done next => rfl
    | yield next =>
      simpa only [bind_assoc,pure_bind] using ih next

/-- A successful loop yields the actual intermediate chain; failures do not
manufacture a partial history. -/
theorem observedTimerOuterTurns_chain (jPass : UInt64) (indices : List Nat) (control : TimerOuterControl)
    (initial final : World) (finalControl : TimerOuterControl) (receipts : List OuterTimerTurnReceipt)
    (run : (observedTimerOuterTurns jPass indices control).run initial = .ok ((finalControl,receipts),final)) :
    OuterTimerChain jPass (Campaign2.Product.snapshot initial) control indices receipts
      (Campaign2.Product.snapshot final) finalControl := by
  induction indices generalizing control initial final finalControl receipts with
  | nil =>
    change Except.ok ((control,[]),initial) = _ at run
    cases run
    exact .nil _ _
  | cons iteration rest ih =>
    rw [observedTimerOuterTurns,StateT.run_bind] at run
    cases turn : (observedTimerOuterTurn jPass iteration control).run initial with
    | error stop => rw [turn] at run; cases run
    | ok out =>
      obtain ⟨⟨step,receipt⟩,middle⟩ := out
      obtain ⟨indexEq,before,controlEq,resultEq,after,valid⟩ :=
        observedTimerOuterTurn_valid jPass iteration control initial middle step receipt turn
      rw [turn] at run
      cases step with
      | done next =>
        change Except.ok ((next,[receipt]),middle) = _ at run
        cases run
        simpa only [indexEq,before,controlEq,after] using
          (OuterTimerChain.done (jPass := jPass) receipt rest _ resultEq valid)
      | yield next =>
        change ((observedTimerOuterTurns jPass rest next).run middle >>= fun out =>
          Except.ok ((out.1.1,receipt :: out.1.2),out.2)) = _ at run
        cases tailRun : (observedTimerOuterTurns jPass rest next).run middle with
        | error stop => rw [tailRun] at run; cases run
        | ok out =>
          obtain ⟨⟨last,tail⟩,lastState⟩ := out
          rw [tailRun] at run
          cases run
          have chain := ih next middle lastState last tail tailRun
          rw [← after] at chain
          simpa only [indexEq,before,controlEq] using
            (OuterTimerChain.yield (jPass := jPass) receipt rest next last tail
              (Campaign2.Product.snapshot lastState) resultEq valid chain)

/-- Observe the exact original finite episode. The reset occurs once, outside
all turn probes. The continuing execution uses the original finish verbatim. -/
def observedRunTimersEpisode (jPass : UInt64) : Leanux.M (OuterTimerEpisodeReceipt × Bool) := fun initial => do
  let start : World := {initial with wg := {initial.wg with queuedThisCall := []}}
  let entry := Campaign2.Product.snapshot start
  if start.wg.dev.isNone then
    return ((⟨entry,none,[],entry,(false,none),none⟩,false),start)
  let (budget,afterBudget) ← (recordBudget : Leanux.M Nat).run start
  let ((control,turns),beforeFinish) ←
    (observedTimerOuterTurns jPass (List.range' 0 budget) (false,none)).run afterBudget
  let (result,final) ← (timerOuterFinish control).run beforeFinish
  return ((⟨entry,some budget,turns,Campaign2.Product.snapshot beforeFinish,control,
    some (.ok (result,Campaign2.Product.snapshot final))⟩,result),final)

/-- Exact erasure of the complete original call, including all Stop outcomes. -/
theorem observedRunTimersEpisode_erase (jPass : UInt64) :
    (do let result ← observedRunTimersEpisode jPass; pure result.2) = Env.runTimers jPass := by
  rw [← runTimers_loop_source]
  funext initial
  let start : World := {initial with wg := {initial.wg with queuedThisCall := []}}
  let budget : Nat := match initial.ambient.hidden with
    | some records => records.length + 1
    | none => DOMAIN_FILTER_TURNS
  have budgetRun : (recordBudget : Leanux.M Nat).run start = .ok (budget,start) := rfl
  change ((observedRunTimersEpisode jPass).run initial >>= fun out => Except.ok (out.1.2,out.2)) = _
  unfold observedRunTimersEpisode
  change ((if start.wg.dev.isNone then Except.ok ((_,false),start) else _) >>= _) =
    ((do if start.wg.dev.isNone then return false
         let result ← forIn [0:(← recordBudget)] (false,none) (timerOuterTurn jPass)
         timerOuterFinish result).run start)
  by_cases absent : start.wg.dev.isNone = true
  · simp only [absent,ite_true]
    rfl
  · simp only [absent,Bool.false_eq_true,ite_false]
    rw [StateT.run_bind,budgetRun]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    have erased := congrArg (fun (action : Leanux.M TimerOuterControl) => action.run start)
      (observedTimerOuterTurns_erase jPass (List.range' 0 budget) (false,none))
    rw [StateT.run_bind] at erased
    change _ = ((forIn (List.range' 0 budget) (false,none) (timerOuterTurn jPass)).run start >>=
      fun out => (timerOuterFinish out.1).run out.2)
    rw [← erased]
    change (((observedTimerOuterTurns jPass (List.range' 0 budget) (false,none)).run start >>= fun out =>
      (timerOuterFinish out.1.1).run out.2 >>= fun tail =>
        Except.ok ((_,tail.1),tail.2)) >>= _) = _
    cases turns : (observedTimerOuterTurns jPass (List.range' 0 budget) (false,none)).run start with
    | error stop => rfl
    | ok out =>
      obtain ⟨⟨control,receipts⟩,middle⟩ := out
      change (((timerOuterFinish control).run middle >>= _) >>= _) = (timerOuterFinish control).run middle
      cases finish : (timerOuterFinish control).run middle <;> rfl


end Leanux.Proofs.WG.TimerDiscipline
