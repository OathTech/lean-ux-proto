import Leanux.Proofs.WG.Config.GetterScalarModel
import Leanux.Proofs.WG.Config.Model

/-! Source-cache clearing leaves serialized getter fields unchanged. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG TimerDiscipline

theorem cleared_cell (p : Peer) (reset : UInt64) :
    cell (clearedSource p reset)=cell p := by
  cases endpoint:p.endpoint <;> simp [cell,clearedSource,endpoint,socketEndpoint]
end Leanux.Proofs.WG.Config.GetterScalar
