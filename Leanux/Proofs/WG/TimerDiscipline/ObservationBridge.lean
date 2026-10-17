import Leanux.Proofs.WG.TimerDiscipline.HookObservationPaths
import Leanux.Proofs.WG.TimerDiscipline.ObservationPathsSource
import Leanux.Proofs.WG.TimerDiscipline.ObservationProductSource
import Leanux.Proofs.WG.TimerDiscipline.SourceClaims
import Leanux.Proofs.WG.TimerDiscipline.View

/-! Current selected wheel-unit contracts. The outer nextDue branch and complete runTimers loop are separate obligations. -/

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Noise Std.Do

/-- Actual selected-unit prefix snapshot and detached suffix. Every snapshot field comes from the full product; no state is reconstructed. -/
def timerExecutionPath (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) : Leanux.M (PeerId × PeerTimer × Campaign2.Product.Snapshot) := do
  timerDispatchPrefix_variant worker pid timer we step
  let selected ← Campaign2.Product.read
  fireWheelSelected worker pid timer we
  return (pid, timer, selected)

end Leanux.Proofs.WG.TimerDiscipline
