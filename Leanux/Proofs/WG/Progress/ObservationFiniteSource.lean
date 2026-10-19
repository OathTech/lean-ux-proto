import Leanux.Proofs.WG.Progress.DeferredFiniteOuterSource
import Leanux.Proofs.WG.Environment.ObservationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.ObservationFinite
open Leanux

/-- The actual idle wait followed by the native bounded delivery and JSON tail. -/
def observe : Leanux.M (Int × Lean.Json) := do
  DeferredFinite.nativeIdle
  Environment.observeTail

theorem observe_source : Env.observe = observe := by
  rw [Environment.observe_eq, DeferredFinite.nativeIdle_source]
  rfl

end Leanux.Proofs.WG.Progress.ObservationFinite
