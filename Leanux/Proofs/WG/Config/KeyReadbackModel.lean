import Leanux.Proofs.WG.Config.KeyInstall
import Leanux.Proofs.WG.Config.RequestModel

/-! Effective installed identity and exact quiet one-peer rotation state. -/

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

def keyReadbackBase (d : Device) (key : Key) : Device :=
  installedDevice (requestGeneration d) key

def keyReadbackDevice (d : Device) (key : Key) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  peerUpdatedDevice (keyReadbackBase d key) pid p now

end Leanux.Proofs.WG.Config
