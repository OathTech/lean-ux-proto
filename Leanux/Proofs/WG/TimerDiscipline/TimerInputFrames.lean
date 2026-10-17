import Leanux.Proofs.WG.Noise.InitiationReadyFrames
import Leanux.Proofs.WG.TimerDiscipline.ArmingBaseSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem callerJiffies_input_effect (site : HiddenSite) (entry final : WGWorld)
    (ambient after : Ambient) (caller : Option UInt64)
    (run : ((callerJiffies site).run entry).run ambient = .ok ((caller, final), after)) :
    final = entry ∧ after.armRecords = ambient.armRecords ∧ caller.isSome = ambient.armRecords := by
  have ambientLift {α : Type} (a : AmbientM α) : (monadLift a : WG.M α) = StateT.lift a := rfl
  have source : ((callerJiffies site).run entry).run ambient =
      if ambient.armRecords then
        ((AmbientM.hidden site).run ambient >>= fun (bytes, next) =>
          .ok ((some (bytes.foldr (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0).toUInt64, entry), next))
      else .ok ((none, entry), ambient) := by
    change ((if ambient.armRecords then
      (some <$> hiddenJiffies site : WG.M (Option UInt64)) else pure none).run entry).run ambient = _
    cases mode : ambient.armRecords
    · simp only [Bool.false_eq_true, ite_false]
      rfl
    · simp only [ite_true]
      simp only [hiddenJiffies, AmbientM.hiddenJiffies, ambientLift, map_eq_pure_bind,
        StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
      all_goals rfl
  rw [source] at run
  cases mode : ambient.armRecords with
  | false =>
    simp only [mode, Bool.false_eq_true, ite_false] at run
    cases run
    exact ⟨rfl, mode, rfl⟩
  | true =>
    simp only [mode, ite_true] at run
    cases read : (AmbientM.hidden site).run ambient with
    | error err => rw [read] at run; cases run
    | ok out =>
      obtain ⟨bytes, next⟩ := out
      have preserved :=
        Noise.InitiationReady.hidden_mode
          ambient.armRecords site ambient bytes next rfl read
      rw [read] at run
      cases run
      exact ⟨rfl, preserved.trans mode, rfl⟩

theorem modPeerTimerGuard_input_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry final : WGWorld) (ambient after : Ambient)
    (allowed : Bool) (device : entry.dev = some d)
    (run : ((modPeerTimerGuard pid).run entry).run ambient = .ok ((allowed, final), after)) :
    allowed = (d.running && !p.isDead) ∧ final = entry ∧ after.armRecords = ambient.armRecords := by
  cases running : d.running <;> cases dead : p.isDead
  all_goals simp [modPeerTimerGuard, Leanux.WG.andM, branch, AmbientM.branch,
    getDev, getPeer, device, resident, running, dead] at run
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact ⟨rfl, rfl, rfl⟩

end Leanux.Proofs.WG.TimerDiscipline
