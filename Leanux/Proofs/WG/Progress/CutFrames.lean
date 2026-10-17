import Leanux.Proofs.WG.Progress.CutModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress
open Leanux

/-- The section ordinal update leaves both records and the error-location
decisions untouched. -/
theorem noteNetRxStart_records (site : Nat) (w : Ambient) :
    ∃ final, (AmbientM.noteNetRxStart site).run w = .ok ((), final) ∧
      final.hidden = w.hidden ∧ final.steps = w.steps := by
  unfold AmbientM.noteNetRxStart
  split <;> exact ⟨_, rfl, rfl, rfl⟩

end Leanux.Proofs.WG.Progress
