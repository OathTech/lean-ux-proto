import Leanux.Proofs.WG.Progress.RecordSuffixModel
import Leanux.Proofs.Framing.WGData

/-! Ambient-sensitive frames for checksum and decision/error primitives. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem checksum_retains (records : List HiddenRecord) (pkt : Packet) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.checksumHelp pkt) :=
  (checksumHelp_sameWorld pkt).wp (fun w : World=>Tail records w.ambient.hidden)

theorem product_branch_retains (records : List HiddenRecord) (site : Decision) (value : Bool) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (branch site value : Leanux.M Bool) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  cases run
  exact pre

theorem product_invariant_retains {α : Type} (records : List HiddenRecord) (message : String) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (invariant message : Leanux.M α) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  cases run

end Leanux.Proofs.WG.Progress.RecordSuffix
