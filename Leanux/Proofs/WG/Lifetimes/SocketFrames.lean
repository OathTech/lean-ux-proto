import Leanux.Proofs.Framing.WGKernel
import Leanux.Proofs.Framing.Lift

/-! Seven-field WG-store frames for socket selection and pending NET_RX.
The original device and duplicate-raise guards remain part of the actions. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

theorem socketPort_sameStore (family : Nat) : SameWGStore (socketPort family) := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v a' hp hr
  cases hd : w.dev with
  | none =>
    simp [socketPort, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hs : (if family = AF_INET then d.sock4 else d.sock6) with
    | none =>
      simp [socketPort, getDev, hd, hs, unsupported, AmbientM.unsupported] at hr
      cases hr
    | some port =>
      simp [socketPort, getDev, hd, hs] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hp

theorem raiseLoopbackRx_sameStore : SameWGStore raiseLoopbackRx := by
  intro initial
  let P := fun w : WGWorld => wgStoreView w = initial
  change Preserves P raiseLoopbackRx
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have raised : Preserves P (modify (fun w : WGWorld => {w with netRxRaised := true}) : WG.M Unit) :=
    hoare_modify _ (fun _ h => h)
  unfold raiseLoopbackRx
  apply preserves_bind read
  intro w
  cases w.netRxRaised with
  | false => exact raised
  | true =>
    exact preserves_bind (hoare_liftAmbient
      (AmbientM.invariant "a loopback NET_RX raised while one is pending") P) (fun _ => raised)

end Leanux.Proofs.WG.Lifetimes
