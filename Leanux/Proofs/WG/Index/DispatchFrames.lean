import Leanux.Proofs.WG.Index.SendFrames
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

set_option maxHeartbeats 800000

theorem sendWorkerSelection_tables :
    ⦃fun w => ⌜TablesSafeWG w.wg⌝⦄ TimerDiscipline.sendWorkerSelection
      ⦃⇓? _ w => ⌜TablesSafeWG w.wg⌝⦄ := by
  apply (Noise.Product.ensures_iff _ _ _).mp
  intro w result final pre run
  cases device : w.wg.dev with
  | none =>
    have missing : (liftWG getDev).run w =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      change (((getDev.run w.wg).run w.ambient) >>= _) = _
      simp [getDev, device, invariant, AmbientM.invariant]
      rfl
    change ((liftWG getDev).run w >>= _) = _ at run
    rw [missing] at run
    cases run
  | some d =>
    have effect := TimerDiscipline.sendWorkerSelection_effect d w.ambient.unitPeers
      w result final ⟨device, rfl⟩ run
    intro next current
    rw [effect.1] at current
    cases current
    exact pre d device

theorem sendWorkerDequeue_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeWG w.wg⌝⦄ TimerDiscipline.sendWorkerDequeue pid
      ⦃⇓? _ w => ⌜TablesSafeWG w.wg⌝⦄ := by
  apply (Noise.Product.ensures_iff _ _ _).mp
  intro w result final pre run
  cases device : w.wg.dev with
  | none =>
    have unchanged : (liftWG (modifyDev fun d =>
        {d with sendWorkQueue := d.sendWorkQueue.erase pid})).run w = .ok ((), w) := by
      change Except.ok ((), {w with wg := {w.wg with dev := w.wg.dev.map _}}) = _
      have restored : {w.wg with dev := none} = w.wg := by
        have same : {w.wg with dev := w.wg.dev} = w.wg := rfl
        rw [device] at same
        exact same
      simp only [device, Option.map_none, restored]
    have missing : (liftWG (getPeer pid)).run w =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      change ((((getPeer pid).run w.wg).run w.ambient) >>= _) = _
      simp [getPeer, getDev, device, invariant, AmbientM.invariant]
      rfl
    unfold TimerDiscipline.sendWorkerDequeue at run
    simp only [StateT.run_bind] at run
    change ((liftWG (modifyDev fun d =>
      {d with sendWorkQueue := d.sendWorkQueue.erase pid})).run w >>= _) = _ at run
    rw [unchanged] at run
    change ((liftWG (getPeer pid)).run w >>= _) = _ at run
    rw [missing] at run
    cases run
  | some d =>
    obtain ⟨p, _, _, effect⟩ :=
      TimerDiscipline.sendWorkerDequeue_effect pid d w result final device run
    intro next current
    rw [effect] at current
    cases current
    exact pre d device

end Leanux.Proofs.WG.Index
