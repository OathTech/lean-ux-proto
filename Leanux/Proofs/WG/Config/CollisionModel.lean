import Leanux.Proofs.WG.Config.CollisionRemovalModel
import Leanux.Proofs.WG.Config.KeyInstallEffects

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Installation starts at the actual post-removal baseline. In particular its
peer list and staged-send test are not taken from the request-entry device. -/
def CollisionKeyEffect (pid : PeerId) (d : Device) (p : Peer) (key : Key)
    (final : Device) : Prop :=
  ∃ baseline,
    CollisionRemovalEffect pid (collisionLookupDevice d pid p) p baseline ∧
    KeyPeerRun (requestsStagedSend baseline key) (installedDevice baseline key)
      baseline.peerList final

end Leanux.Proofs.WG.Config
