import Leanux.Proofs.WG.Progress.TimerCompletionModel
import Leanux.Proofs.WG.TimerDiscipline.OuterFirstTurnSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.TimerDiscipline

/-- The actual unchanged timer finish establishes its own final tests whenever
it returns true. No condition is asserted for a false return. -/
theorem timerOuterFinish_completion (control : Bool × Option UInt64) :
    Campaign2.Product.Ensures (timerOuterFinish control) (fun _ => True)
      (fun result final => result = true → TimerCompletionGuard final) := by
  intro initial result final _ run fired
  subst result
  let step : Leanux.M Unit := match control.2 with
    | none => pure ()
    | some bucket => requireStepComplete bucket
  let tail : Leanux.M Bool := do
    if control.1 then
      deliverSent
      let d ← getDev
      if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty ||
          !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
        unsupported "work a timer queued outlived the guest's wait"
    return control.1
  have factor : timerOuterFinish control = (do step; tail) := by
    unfold timerOuterFinish step tail
    cases control.2 <;> simp only [pure_bind]
  rw [factor,StateT.run_bind] at run
  change (step.run initial >>= fun out => tail.run out.2) = _ at run
  cases prefixRun : step.run initial with
  | error stop => rw [prefixRun] at run; cases run
  | ok out =>
    obtain ⟨value,middle⟩ := out
    rw [prefixRun] at run
    change tail.run middle = _ at run
    cases flag : control.1 with
    | false =>
      simp only [tail,flag,Bool.false_eq_true,ite_false] at run
      cases run
    | true =>
      simp only [tail,flag,ite_true] at run
      rw [StateT.run_bind] at run
      cases delivery : deliverSent.run middle with
      | error stop => rw [delivery] at run; cases run
      | ok out =>
        obtain ⟨value,afterDelivery⟩ := out
        rw [delivery] at run
        change ((liftWG getDev).run afterDelivery >>= _) = _ at run
        cases device : afterDelivery.wg.dev with
        | none =>
          have absent : (liftWG getDev).run afterDelivery =
              .error (.invariant "no WireGuard device in this trace's fixture") := by
            dsimp only [liftWG,getDev,StateT.run,StateT.bind,get,getThe,MonadStateOf.get,
              StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure]
            rw [device]; rfl
          rw [absent] at run
          cases run
        | some d =>
          have read : (liftWG getDev).run afterDelivery = .ok (d,afterDelivery) := by
            dsimp only [liftWG,getDev,StateT.run,StateT.bind,get,getThe,MonadStateOf.get,
              StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure]
            rw [device]; rfl
          rw [read] at run
          let dirty := !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty ||
            !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
          have clean : dirty = false := by
            cases test : dirty with
            | false => rfl
            | true =>
              change ((do
                if dirty then unsupported "work a timer queued outlived the guest's wait"
                pure true : Leanux.M Bool).run afterDelivery) = _ at run
              rw [test] at run
              change Except.error _ = Except.ok _ at run
              cases run
          change ((do
            if dirty then unsupported "work a timer queued outlived the guest's wait"
            pure true : Leanux.M Bool).run afterDelivery) = _ at run
          rw [clean] at run
          change Except.ok (true,afterDelivery) = Except.ok (true,final) at run
          have same : afterDelivery = final := congrArg Prod.snd (Except.ok.inj run)
          rw [← same]
          refine ⟨d,device,?_⟩
          simpa [dirty,Bool.or_eq_false_iff,and_assoc] using clean


end Leanux.Proofs.WG.Progress
