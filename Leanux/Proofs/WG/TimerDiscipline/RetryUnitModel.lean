import Leanux.WG.State

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- Explicit input to one current retransmit dispatch unit. This carries no
claim that the outer wheel scheduler selects the unit. -/
structure RetryUnit where
  pid : PeerId
  wheel : WheelEntry
  step : Option UInt64

end Leanux.Proofs.WG.TimerDiscipline
