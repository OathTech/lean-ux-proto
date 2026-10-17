import Leanux.Proofs.WG.Config.RequestModel
import Leanux.WG.Socket

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Scalar Device outcome of a zero-port request. Only the changed running
branch uses the chosen ephemeral port; the same-port branch does no clearing. -/
def zeroPortRequestDevice (d : Device) (chosen : Nat) : Device :=
  if d.incomingPort = 0 then requestGeneration d
  else if d.running then
    {requestGeneration d with sock4 := some chosen, sock6 := some chosen, incomingPort := chosen}
  else {requestGeneration d with incomingPort := 0}

/-- The normal changed-running outcome carries the actual chosen-port range.
The unused choice is normalized to zero for same-port and stopped branches. -/
def ZeroPortRequestChoice (d : Device) (chosen : Nat) : Prop :=
  if d.incomingPort = 0 then chosen = 0
  else if d.running then LOCAL_PORT_LOW ≤ chosen ∧ chosen ≤ LOCAL_PORT_HIGH
  else chosen = 0

end Leanux.Proofs.WG.Config
