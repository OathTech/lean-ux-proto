import Leanux.Proofs.WG.Progress.TimerTurnRecordEffects
import Leanux.Proofs.WG.Progress.TimerTurnRecordFrames
import Leanux.Proofs.WG.Progress.TimerLoopRecordSource
import Leanux.Proofs.WG.TimerDiscipline.OuterAdjacentFrames
import Leanux.Proofs.WG.Roaming.HandshakeOverlayStepSource

/-! Strict record decrease for a normally yielding original timer turn.
Clear, timer and send branches use their actual section contracts. The crypt
branch yields only when its unchanged next-site read differs from entry.
No enclosing completion check or successful callback premise is supplied. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.WG.TimerDiscipline

theorem cryptTurn_changed_strict (records : List HiddenRecord) (site : Nat)
    (before after : World) (present : before.ambient.hidden=some records)
    (first : (Env.peekNextSite.run before).map Prod.fst = .ok (some site))
    (run : Env.runCryptWorkers.run before=.ok ((),after))
    (changed : (after.ambient.hidden.bind (fun rs=>(rs.find? (fun r=>!HiddenSite.passive r.site)).map (·.site))) ≠ some site) :
    StrictTail records after.ambient.hidden := by
  apply tail_strict_of_changed
  · exact (hoare_iff_run _ _ _).mp (runCryptWorkers_retains records)
      before () after (present ▸ tail_self records) run
  · intro same
    rw [peekNextSite_exact] at first
    change Except.ok _ = Except.ok (some site) at first
    apply changed
    rw [same,←present]
    exact Except.ok.inj first

private theorem stepGuard_suffix_run {α : Type} (step : Option UInt64)
    (action : Leanux.M α) (before after : World) (value : α)
    (run : ((match step with
      | some b => do requireStepComplete b; action
      | _ => action).run before)=.ok (value,after)) :
    action.run before=.ok (value,after) := by
  cases step with
  | none => exact run
  | some b =>
    change ((requireStepComplete b).run before >>= fun out=>action.run out.2)=_ at run
    cases checked : (requireStepComplete b).run before with
    | error stop=>rw [checked] at run; cases run
    | ok out=>
      obtain ⟨u,middle⟩:=out
      cases u
      have same:=requireStepComplete_sameState b before middle checked
      subst middle
      rw [checked] at run
      exact run

private theorem unit_yield_run {β : Type} (action : Leanux.M Unit)
    (control next : β) (before after : World)
    (run : ((do action; pure (ForInStep.yield next) : Leanux.M (ForInStep β)).run before)
      =.ok (.yield control,after)) :
    action.run before=.ok ((),after) := by
  rw [StateT.run_bind] at run
  cases actual : action.run before with
  | error stop=>rw [actual] at run; cases run
  | ok out=>
    obtain ⟨u,middle⟩:=out
    cases u
    rw [actual] at run
    have same := congrArg Prod.snd (Except.ok.inj run)
    cases same
    rfl

theorem timerOuterTurn_yield_strict
    (jPass : UInt64) (iteration : Nat) (control nextControl : Bool × Option UInt64)
    (records : List HiddenRecord) (before after : World)
    (present : before.ambient.hidden=some records)
    (run : (timerOuterTurn jPass iteration control).run before=.ok (.yield nextControl,after)) :
    StrictTail records after.ambient.hidden := by
  have pre : Tail records before.ambient.hidden := present ▸ tail_self records
  have hok {α β : Type} (x : α) (f : α→Except Stop β) : (Except.ok x >>= f)=f x := rfl
  unfold timerOuterTurn at run
  rw [StateT.run_bind,peekNextSite_exact] at run
  simp only [hok] at run
  cases first : before.ambient.hidden.bind
      (fun rs=>(rs.find? (fun r=>!HiddenSite.passive r.site)).map (·.site)) with
  | none=>rw [first] at run; cases run
  | some site=>
    rw [first] at run
    change ((liftWG getDev).run before >>= _) = _ at run
    rw [Leanux.Proofs.WG.Roaming.HandshakeOverlay.getDev_run] at run
    cases device : before.wg.dev with
    | none=>rw [device] at run; cases run
    | some d=>
      rw [device] at run
      simp only [hok] at run
      cases timer : timerSectionOf site with
      | some worker=>
        rw [timer] at run
        by_cases clear : (worker==.clearPeerWorker)=true
        · simp only [clear,ite_true] at run
          let action : Leanux.M (ForInStep (Bool × Option UInt64)) :=
            if d.clearWorkQueue.isEmpty then pure (.done (control.1,none))
            else do Env.runOneClearWorker; pure (.yield (control.1,none))
          have suffix:=stepGuard_suffix_run control.2 action before after (ForInStep.yield nextControl) run
          dsimp only [action] at suffix
          by_cases empty : d.clearWorkQueue.isEmpty=true
          · simp only [empty,ite_true] at suffix
            cases suffix
          · simp only [empty] at suffix
            have actual:=unit_yield_run Env.runOneClearWorker nextControl (control.1,none) before after suffix
            exact (hoare_iff_run _ _ _).mp (clearWorker_strict records) before () after pre actual
        · simp only [clear] at run
          cases due : TimerWheel.nextDue d jPass with
          | none=>rw [due] at run; cases run
          | some chosen=>
            obtain ⟨pid,t,wheel⟩:=chosen
            rw [due] at run
            have actual:=unit_yield_run
              (timerDispatchUnit_variant worker pid t wheel control.2)
              nextControl (true,some wheel.bucketExpiry) before after run
            exact (hoare_iff_run _ _ _).mp (timerDispatchUnit_strict records worker pid t wheel control.2)
              before () after pre actual
      | none=>
        rw [timer] at run
        let action : Leanux.M (ForInStep (Bool × Option UInt64)) := do
          if !control.1 then return .done (control.1,none)
          if site==(HiddenSite.sectionStart .sendWorker).info.id && !d.sendWorkQueue.isEmpty then
            Env.runOneSendWorker
            return .yield (control.1,none)
          Env.runCryptWorkers
          if (← Env.peekNextSite)==some site then return .done (control.1,none)
          return .yield (control.1,none)
        have suffix:=stepGuard_suffix_run control.2 action before after (ForInStep.yield nextControl) run
        dsimp only [action] at suffix
        by_cases notFired : (!control.1)=true
        · simp only [notFired,ite_true] at suffix
          cases suffix
        · simp only [notFired] at suffix
          by_cases sending : (site==(HiddenSite.sectionStart .sendWorker).info.id &&
              !d.sendWorkQueue.isEmpty)=true
          · simp only [sending,ite_true] at suffix
            have actual:=unit_yield_run Env.runOneSendWorker nextControl (control.1,none) before after suffix
            exact (hoare_iff_run _ _ _).mp (sendWorker_strict records) before () after pre actual
          · simp only [sending] at suffix
            change (Env.runCryptWorkers.run before >>= _) = _ at suffix
            cases crypt : Env.runCryptWorkers.run before with
            | error stop=>rw [crypt] at suffix; cases suffix
            | ok out=>
              obtain ⟨u,middle⟩:=out
              cases u
              rw [crypt] at suffix
              simp only [hok] at suffix
              change ((do let next ← Env.peekNextSite
                          if next==some site then pure (ForInStep.done (control.1,none))
                          else pure (ForInStep.yield (control.1,none)) : Leanux.M _).run middle)=_ at suffix
              rw [StateT.run_bind,peekNextSite_exact] at suffix
              simp only [hok] at suffix
              split at suffix
              · cases suffix
              · rename_i changed
                have same : middle=after := congrArg Prod.snd (Except.ok.inj suffix)
                subst after
                refine cryptTurn_changed_strict records site before middle present ?_ crypt ?_
                · rw [peekNextSite_exact]
                  change Except.ok _ = Except.ok _
                  exact congrArg Except.ok first
                · simpa only [beq_iff_eq] using changed


end Leanux.Proofs.WG.Progress.RecordSuffix
