import Leanux.Proofs.WG.Progress.AdvanceOperationSource
import Leanux.Proofs.WG.Progress.AdvanceWaitClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Every normal decorated syscall certifies its actual successful advance.
When the actual wait returns a recorded receipt, its bounds are that advance's
bounds, and its own wrapped pass test holds at return. No entry-mode transport
through arbitrary file/task work is assumed. -/
theorem observedAdvanceOperation_checks (ticks : Nat) :
    Campaign2.Product.Ensures (observedAdvanceOperation ticks) (fun _ => True)
      (fun out final => out.1 = 0 ∧ ∃ j0 j1,
        out.2.1 = some (j0,j1) ∧ j1 - j0 = ticks.toUInt64 ∧
        ∀ receipt, out.2.2 = some receipt → receipt.j0 = j0 ∧ receipt.j1 = j1 ∧
          final.wg.jiffiesLast = some receipt.jEnd ∧ NoTimerDue receipt.pass final) := by
  have fsFixture {α : Type} (action : FS.M α) (initial final : World) (result : α)
      (run : (liftFS action).run initial = .ok (result,final)) :
      final.fixture = initial.fixture := by
    change (((action.run initial.fs).run initial.tasks).run initial.ambient >>= _) = _ at run
    cases actual : ((action.run initial.fs).run initial.tasks).run initial.ambient with
    | error stop => rw [actual] at run; cases run
    | ok out =>
      obtain ⟨⟨⟨value,fs⟩,tasks⟩,ambient⟩ := out
      rw [actual] at run
      cases run
      rfl
  have dispatchBounds (initial final : World) (result : Int)
      (run : (dispatch (.wgAdvance ticks)).run initial = .ok (result,final)) :
      result = 0 ∧ ∃ j0 j1, final.fixture.lastAdvance = some (j0,j1) ∧
        j1-j0 = ticks.toUInt64 := by
    unfold dispatch at run
    rw [StateT.run_bind] at run
    change ((liftFS (fdget KCOV_FD)).run initial >>= _) = _ at run
    cases obtained : (liftFS (fdget KCOV_FD)).run initial with
    | error stop => rw [obtained] at run; cases run
    | ok pair =>
      obtain ⟨f,middle⟩ := pair
      rw [obtained] at run
      change ((do
        if f.file.isNone then unsupported "wg_advance after the trace closed the KCOV descriptor"
        let ret ← advance ticks
        fdput f
        pure ret : Leanux.M Int).run middle) = _ at run
      cases file : f.file with
      | none => simp [file,unsupported,AmbientM.unsupported] at run; cases run
      | some fid =>
        simp only [file,Option.isNone_some,Bool.false_eq_true,ite_false] at run
        rw [StateT.run_bind] at run
        cases advanced : (advance ticks).run middle with
        | error stop => rw [advanced] at run; cases run
        | ok pair =>
          obtain ⟨ret,afterAdvance⟩ := pair
          obtain ⟨zero,j0,j1,bounds,delta,_⟩ := advance_normal_bounds ticks middle afterAdvance ret advanced
          rw [advanced] at run
          change ((liftFS (fdput f)).run afterAdvance >>= _) = _ at run
          cases put : (liftFS (fdput f)).run afterAdvance with
          | error stop => rw [put] at run; cases run
          | ok pair =>
            obtain ⟨ignored,afterPut⟩ := pair
            rw [put] at run
            cases run
            exact ⟨zero,j0,j1,by rw [fsFixture _ _ _ _ put]; exact bounds,delta⟩
  have prefixBounds (initial final : World) (result : Int)
      (run : (advanceOperationPrefix ticks).run initial = .ok (result,final)) :
      result = 0 ∧ ∃ j0 j1, final.fixture.lastAdvance = some (j0,j1) ∧
        j1-j0 = ticks.toUInt64 := by
    unfold advanceOperationPrefix at run
    rw [StateT.run_bind] at run
    cases entered : advanceOperationEntry.run initial with
    | error stop => rw [entered] at run; cases run
    | ok pair =>
      obtain ⟨ignored,middle⟩ := pair
      rw [entered] at run
      change ((dispatch (.wgAdvance ticks)).run middle >>= _) = _ at run
      cases dispatched : (dispatch (.wgAdvance ticks)).run middle with
      | error stop => rw [dispatched] at run; cases run
      | ok pair =>
        obtain ⟨ret,afterDispatch⟩ := pair
        obtain ⟨zero,j0,j1,bounds,delta⟩ := dispatchBounds middle afterDispatch ret dispatched
        rw [dispatched] at run
        simp only [windowTailCalls,List.forIn_nil,pure_bind] at run
        change ((liftFS taskWorkRun).run afterDispatch >>= _) = _ at run
        cases worked : (liftFS taskWorkRun).run afterDispatch with
        | error stop => rw [worked] at run; cases run
        | ok pair =>
          obtain ⟨ignored,afterWork⟩ := pair
          rw [worked] at run
          cases run
          exact ⟨zero,j0,j1,by rw [fsFixture _ _ _ _ worked]; exact bounds,delta⟩
  have prefixRecorded (initial final : World) (receipt : AdvanceWaitReceipt)
      (run : afterAdvancePrefix.run initial = .ok (some receipt,final)) :
      initial.ambient.hidden.isSome = true := by
    cases hidden : initial.ambient.hidden with
    | some records => rfl
    | none =>
      dsimp only [afterAdvancePrefix,getWG,getAmbient,monadLift,MonadLift.monadLift,liftM,
        liftWG,liftAmbient,StateT.run,Bind.bind,StateT.bind,Pure.pure,StateT.pure,
        Except.pure,Except.bind,get,getThe,MonadStateOf.get,StateT.get] at run
      simp only [hidden,Option.isNone_none,ite_true] at run
      cases placeholders : initial.ambient.hiddenPlaceholders with
      | false =>
        simp only [placeholders,Bool.false_eq_true,ite_false] at run
        change ((discard (runTimers (initial.wg.jiffiesLast.getD 0 + initial.ambient.timing.advanceWait.toUInt64)) : Leanux.M Unit).run initial >>= _) = _ at run
        cases waited : (discard (runTimers (initial.wg.jiffiesLast.getD 0 + initial.ambient.timing.advanceWait.toUInt64)) : Leanux.M Unit).run initial with
        | error stop => rw [waited] at run; cases run
        | ok pair => rw [waited] at run; cases run
      | true =>
        simp only [placeholders,ite_true] at run
        change ((runTimersPlaceholder (initial.wg.jiffiesLast.getD 0 + initial.ambient.timing.advanceWait.toUInt64)).run initial >>= _) = _ at run
        cases waited : (runTimersPlaceholder (initial.wg.jiffiesLast.getD 0 + initial.ambient.timing.advanceWait.toUInt64)).run initial with
        | error stop => rw [waited] at run; cases run
        | ok pair => rw [waited] at run; cases run
  intro initial result final _ run
  unfold observedAdvanceOperation at run
  rw [StateT.run_bind] at run
  cases preRun : (advanceOperationPrefix ticks).run initial with
  | error stop => rw [preRun] at run; cases run
  | ok pair =>
    obtain ⟨ret,atWait⟩ := pair
    obtain ⟨zero,j0,j1,bounds,delta⟩ := prefixBounds initial atWait ret preRun
    rw [preRun] at run
    change (observedAfterAdvance.run atWait >>= fun (receipt,last) =>
      .ok ((ret,atWait.fixture.lastAdvance,receipt),last)) = _ at run
    cases waiting : observedAfterAdvance.run atWait with
    | error stop => rw [waiting] at run; cases run
    | ok pair =>
      obtain ⟨seen,last⟩ := pair
      rw [waiting] at run
      cases run
      refine ⟨zero,j0,j1,bounds,delta,?_⟩
      intro receipt same
      change seen = some receipt at same
      subst seen
      have whole := waiting
      unfold observedAfterAdvance at waiting
      rw [StateT.run_bind] at waiting
      cases captured : afterAdvancePrefix.run atWait with
      | error stop => rw [captured] at waiting; cases waiting
      | ok pair =>
        obtain ⟨candidate,atPass⟩ := pair
        rw [captured] at waiting
        change ((afterAdvanceSuffix candidate).run atPass >>= _) = _ at waiting
        cases finished : (afterAdvanceSuffix candidate).run atPass with
        | error stop => rw [finished] at waiting; cases waiting
        | ok pair =>
          obtain ⟨ignored,afterWait⟩ := pair
          rw [finished] at waiting
          cases waiting
          have recorded := prefixRecorded atWait atPass receipt captured
          obtain ⟨r,equal,original,_,_⟩ :=
            afterAdvancePrefix_recorded_provenance atWait atPass (some receipt) recorded captured
          cases equal
          have pairEqual : (receipt.j0,receipt.j1) = (j0,j1) :=
            Option.some.inj (original.symm.trans bounds)
          obtain ⟨_,seenSame,lastClock,noDue⟩ :=
            observedAfterAdvance_recorded_checks atWait (some receipt) final recorded whole
          cases seenSame
          exact ⟨congrArg Prod.fst pairEqual,congrArg Prod.snd pairEqual,lastClock,noDue⟩

end Leanux.Proofs.WG.Progress
