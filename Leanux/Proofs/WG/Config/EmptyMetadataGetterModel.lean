import Leanux.Proofs.WG.Config.GetterMetadataModel
import Leanux.Proofs.WG.Config.MultiPeerGetterModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG TimerDiscipline

/-- Empty configured peer output, with the ordinary device header retained. -/
def emptyPeersJson (d : Device) : Lean.Json :=
  Lean.Json.mkObj (deviceFixedAttrs d ++ [("peers", .arr #[])])


end Leanux.Proofs.WG.Config

