import Leanux.Proofs.WG.Config.CollisionRemovalModel
import Leanux.Proofs.WG.Config.KeyInstallEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Installation uses the actual post-removal baseline and the observations
of its actual ordered peer loop, including queued-work choices. -/
def ObservedCollisionKeyEffect (pid : PeerId) (d : Device) (p : Peer) (key : Key)
    (final : Device) : Prop :=
  ∃ baseline observations,
    CollisionRemovalEffect pid (collisionLookupDevice d pid p) p baseline ∧
    ObservedKeyPeerRun (requestsStagedSend baseline key) (installedDevice baseline key)
      baseline.peerList observations final

end Leanux.Proofs.WG.Config
