import Leanux.Proofs.WG.Config.DevicePorts
import Leanux.Proofs.WG.Config.RequestModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Pure expected result and non-peer Device fields of a nonzero port request.
The original same-port branch only increments configuration generation. -/
def nonzeroPortRequestOutcome (d : Device) (port : Nat) (bound : Nat → Bool) : Int × Device :=
  if d.incomingPort = port then (0,requestGeneration d)
  else portOutcome (requestGeneration d) port bound

end Leanux.Proofs.WG.Config
