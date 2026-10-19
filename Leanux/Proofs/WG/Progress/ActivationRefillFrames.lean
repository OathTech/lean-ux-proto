import Leanux.Proofs.Framing.Batch
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing
theorem activationRefills_run (w : World) (d : Device) (device : w.wg.dev = some d) :
    Activation.refills.run w =
      .ok ((w.ambient.hidden.map List.length).getD 0 +
        d.peers.toList.countP (·.2.napiScheduled) * WG.NAPI_POLL_WEIGHT,w) := by
  unfold Activation.refills
  rw [StateT.run_bind]
  have read : (liftWG getDev).run w = .ok (d,w) := by
    rw [liftWG_run]
    simp [getDev,device]
    rfl
  change ((liftWG getDev).run w >>= _) = _
  rw [read]
  rfl
theorem activationRefills_sameState :
    SameView (fun w : World => w) Activation.refills := by
  apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
  intro w value v run
  cases device : w.wg.dev with
  | none =>
    unfold Activation.refills at run
    rw [StateT.run_bind] at run
    change ((liftWG getDev).run w >>= _) = _ at run
    have read : (liftWG getDev).run w = .error
        (.invariant "no WireGuard device in this trace's fixture") := by
      rw [liftWG_run]
      simp [getDev,device]
      rfl
    rw [read] at run
    cases run
  | some d =>
    rw [activationRefills_run w d device] at run
    cases run
    rfl
end Leanux.Proofs.WG.Progress.RecordSuffix
