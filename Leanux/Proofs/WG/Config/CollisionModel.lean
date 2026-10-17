import Leanux.Proofs.WG.Config.CollisionRemovalModel
import Leanux.Proofs.WG.Config.KeyInstallEffects

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Historical predicted peer-loop effect, retained for the pending terminal carry.
Current request contracts use ObservedCollisionKeyEffect and actual installation
observations. Both relations start at the post-removal baseline. -/
def CollisionKeyEffect (pid : PeerId) (d : Device) (p : Peer) (key : Key)
    (final : Device) : Prop :=
  ∃ baseline,
    CollisionRemovalEffect pid (collisionLookupDevice d pid p) p baseline ∧
    KeyPeerRun (requestsStagedSend baseline key) (installedDevice baseline key)
      baseline.peerList final

end Leanux.Proofs.WG.Config
