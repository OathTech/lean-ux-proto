import Leanux.Proofs.WG.Config.RequestOrderFrames

/-! Physical WireGuard-state preservation adapted to a history-indexed observer predicate. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

open Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes in
theorem Internal.frame_predicate {α : Type} (P : List Receipt → WGWorld → Prop)
    (a : WG.M α) (frame : SameView (id : WGWorld → WGWorld) a) :
    StatePrefixPreserves (fun h w _ => P h w) (fun _ => True) (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift a (fun _ _ _ _ => trivial)
  intro h w ambient value v after point run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w ambient value v after run
  change v = w at same
  rw [same]
  exact point

end Leanux.Proofs.WG.Config.RequestOrder
