import Leanux.Proofs.WG.Config.RequestMetadataEffects
import Leanux.Proofs.WG.Config.GetterPeerCommandClaims
import Leanux.Proofs.WG.Config.RequestInputClaims

/-! Lift actual native getter-metadata frames into the existing request observer invariant. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Leanux.Proofs.WG.Configuration

theorem metadata_lift {α : Type} (action : WG.M α)
    (frame : SameView getterMetadata action) :
    StatePrefixPreserves (fun h w _=>MetadataAll h (getterMetadata w))
      MetadataConsistent (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift action (fun _ w _ point=>⟨getterMetadata w,point⟩)
  intro h w ambient ret v after point run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w ambient ret v after run
  change getterMetadata v=getterMetadata w at same
  simpa only [same] using point

theorem metadata_branch (site : Decision) (value : Bool) :
    StatePrefixPreserves (fun h w _=>MetadataAll h (getterMetadata w))
      MetadataConsistent (liftWGPrefix (branch site value)) := by
  apply metadata_lift
  exact GetterCleanup.ambient (AmbientM.branch site value)

end Leanux.Proofs.WG.Config.RequestOrder
