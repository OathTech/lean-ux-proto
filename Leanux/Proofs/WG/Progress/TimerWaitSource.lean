import Leanux.Proofs.WG.Progress.TimerWaitModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- The actual recorded wait suffix checks the wheel at its pass bound,
consumes the named end read, checks agreement, and stores that read. -/
def timerWaitFinish (jPass jEnd : UInt64) : Leanux.M Unit := do
  requireNothingDue jPass
  let j ← hiddenJiffies .jiffiesEnd
  if j != jEnd then invariant "the end-of-wait jiffies record changed between the peek and the read"
  modifyWG fun w => {w with jiffiesLast := some j}

/-- Successful completion of the original guard rules out its own due-timer test. -/
theorem requireNothingDue_checks (j : UInt64) :
    Campaign2.Product.Ensures (requireNothingDue j) (fun _ => True)
      (fun _ s => NoTimerDue j s) := by
  intro initial result final _ run
  unfold requireNothingDue at run
  rw [StateT.run_bind] at run
  change (Except.ok (initial.wg,initial) >>= _) = _ at run
  dsimp only [Bind.bind,Except.bind] at run
  cases device : initial.wg.dev with
  | none =>
    rw [device] at run
    change Except.ok ((),initial) = Except.ok (result,final) at run
    cases run
    intro d present
    change initial.wg.dev = some d at present
    rw [device] at present
    cases present
  | some d =>
    rw [device] at run
    dsimp only at run
    cases due : TimerWheel.nextDue d j with
    | none =>
      rw [due] at run
      change Except.ok ((),initial) = Except.ok (result,final) at run
      cases run
      intro other present
      change initial.wg.dev = some other at present
      rw [device] at present
      cases present
      exact due
    | some item =>
      obtain ⟨pid,t,we⟩ := item
      rw [due] at run
      dsimp only at run
      change ((timerWorker t).run initial >>= _) = _ at run
      cases workerRun : (timerWorker t).run initial with
      | error stop => rw [workerRun] at run; cases run
      | ok pair =>
        obtain ⟨worker,middle⟩ := pair
        rw [workerRun] at run
        dsimp only [Bind.bind,Except.bind] at run
        change ((getWG : Leanux.M WGWorld).run middle >>= _) = _ at run
        change (Except.ok (middle.wg,middle) >>= _) = _ at run
        dsimp only [Bind.bind,Except.bind] at run
        change ((sectionAppearsLater worker
          (((middle.wg.timerUnits.find? fun e => e.2.1 == pid && e.2.2 == t).map (·.1)).getD 0)).run middle >>= _) = _ at run
        cases laterRun : (sectionAppearsLater worker
          (((middle.wg.timerUnits.find? fun e => e.2.1 == pid && e.2.2 == t).map (·.1)).getD 0)).run middle with
        | error stop => rw [laterRun] at run; cases run
        | ok pair =>
          obtain ⟨later,after⟩ := pair
          rw [laterRun] at run
          cases later <;> cases run

/-- On normal return the original wait suffix records its named end read
and still satisfies the wheel check; ambient input reads cannot change WG. -/
theorem timerWaitFinish_checks (jPass jEnd : UInt64) :
    Campaign2.Product.Ensures (timerWaitFinish jPass jEnd) (fun _ => True)
      (fun _ s => s.wg.jiffiesLast = some jEnd ∧ NoTimerDue jPass s) := by
  intro initial result final _ run
  unfold timerWaitFinish at run
  rw [StateT.run_bind] at run
  cases checked : (requireNothingDue jPass).run initial with
  | error stop => rw [checked] at run; cases run
  | ok pair =>
    obtain ⟨value,middle⟩ := pair
    have clean := requireNothingDue_checks jPass initial value middle True.intro checked
    rw [checked] at run
    dsimp only [Bind.bind,Except.bind] at run
    change ((hiddenJiffies .jiffiesEnd : Leanux.M UInt64).run middle >>= _) = _ at run
    cases clock : (AmbientM.hiddenJiffies .jiffiesEnd).run middle.ambient with
    | error stop =>
      have read : (hiddenJiffies .jiffiesEnd : Leanux.M UInt64).run middle = .error stop := by
        change ((AmbientM.hiddenJiffies .jiffiesEnd).run middle.ambient >>= _) = _
        rw [clock]; rfl
      rw [read] at run; cases run
    | ok pair =>
      obtain ⟨j,inputs⟩ := pair
      have read : (hiddenJiffies .jiffiesEnd : Leanux.M UInt64).run middle =
          .ok (j,{middle with ambient := inputs}) := by
        change ((AmbientM.hiddenJiffies .jiffiesEnd).run middle.ambient >>= _) = _
        rw [clock]; rfl
      rw [read] at run
      dsimp only [Bind.bind,Except.bind] at run
      by_cases same : j = jEnd
      · subst j
        simp only [bne_self_eq_false,Bool.false_eq_true,ite_false] at run
        change Except.ok ((),{middle with ambient := inputs, wg := {middle.wg with jiffiesLast := some jEnd}}) = Except.ok (result,final) at run
        cases run
        exact ⟨rfl,clean⟩
      · have different : (j != jEnd) = true := by simp [same]
        rw [different] at run
        cases run

/-- Exact recorded branch of the original idle wait, with all errors retained. -/
theorem idleTimers_recorded_source (initial : World)
    (recorded : initial.ambient.hidden.isSome = true) :
    idleTimers.run initial = ((do
      let some jEnd ← peekSiteU64 .jiffiesEnd
        | throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation")
      discard <| runTimers jEnd
      timerWaitFinish jEnd jEnd : Leanux.M Unit).run initial) := by
  have present : initial.ambient.hidden.isNone = false := by
    cases hidden : initial.ambient.hidden <;> simp_all
  unfold idleTimers
  change ((do
    if initial.ambient.hidden.isNone then
      let jHi := initial.wg.jiffiesLast.getD 0 + initial.ambient.timing.traceBound.toUInt64 +
        initial.ambient.timing.advanceWait.toUInt64
      if initial.ambient.hiddenPlaceholders then runTimersPlaceholder jHi else discard <| runTimers jHi
      return
    let some jEnd ← peekSiteU64 .jiffiesEnd
      | throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation")
    discard <| runTimers jEnd
    timerWaitFinish jEnd jEnd : Leanux.M Unit).run initial) = _
  rw [present]
  rfl


end Leanux.Proofs.WG.Progress
