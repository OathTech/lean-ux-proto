import Leanux.Proofs.WG.Config.QuietTimers

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem quietCleanup_resident (d : Device) (pid : PeerId) (p : Peer) :
    (quietCleanupDevice d pid p).peers[pid]? = some (quietCleanupPeer p) :=
  deleteTimers_resident _ _ _ _ (by simp [emptyKeysDevice, withPeer])

end Leanux.Proofs.WG.Config
