import Leanux.Proofs.WG.Progress.RecordSuffixModel
import Leanux.Proofs.Framing.Product

/-! Physical product-state reads and fixture writes retain the hidden-record predicate. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing
theorem stack_getWG_retains (records : List HiddenRecord) :
    Preserves (fun w:World=>Tail records w.ambient.hidden) (getWG : Leanux.M WGWorld) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  cases run
  exact pre

theorem stack_modifyEnv_retains (records : List HiddenRecord) (f : EnvWorld→EnvWorld) :
    Preserves (fun w:World=>Tail records w.ambient.hidden) (modifyEnv f : Leanux.M Unit) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  cases run
  exact pre

end Leanux.Proofs.WG.Progress.RecordSuffix
