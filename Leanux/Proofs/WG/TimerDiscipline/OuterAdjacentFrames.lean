import Leanux.Proofs.WG.TimerDiscipline.OuterFirstTurnSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- Successful step completion only reads the actual device and wheel. -/
theorem requireStepComplete_sameState (bucket : UInt64) (initial final : World)
    (run : (requireStepComplete bucket).run initial = .ok ((),final)) : final = initial := by
  cases device : initial.wg.dev with
  | none =>
    have read : (liftWG getDev).run initial =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      dsimp only [liftWG,getDev,StateT.run,StateT.bind,get,getThe,MonadStateOf.get,
        StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure]
      rw [device]; rfl
    unfold requireStepComplete at run
    rw [StateT.run_bind] at run
    change ((liftWG getDev).run initial >>= _) = _ at run
    rw [read] at run
    cases run
  | some d =>
    have read : (liftWG getDev).run initial = .ok (d,initial) := by
      dsimp only [liftWG,getDev,StateT.run,StateT.bind,get,getThe,MonadStateOf.get,
        StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure]
      rw [device]; rfl
    unfold requireStepComplete at run
    rw [StateT.run_bind] at run
    change ((liftWG getDev).run initial >>= _) = _ at run
    rw [read] at run
    dsimp only [Bind.bind,Except.bind] at run
    cases due : TimerWheel.anotherAtStep d bucket with
    | none =>
      simp only [due] at run
      exact (congrArg Prod.snd (Except.ok.inj run)).symm
    | some pair =>
      obtain ⟨pid,timer⟩ := pair
      simp only [due] at run
      cases run


end Leanux.Proofs.WG.TimerDiscipline
