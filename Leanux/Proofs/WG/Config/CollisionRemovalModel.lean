import Leanux.Proofs.WG.Config.LiveRemovalModel

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- The lookup acquisition and caller put are two ordered store writes.
The peer reference count returns to its original value; no structural map equality with
the initial device is asserted. -/
def collisionLookupDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  withPeer (withPeer d pid { p with refcount := p.refcount + 1 }) pid p

/-- The actual removal first unlists the peer and removes its allowed IPs,
then clears keys, stops timers and performs the final peer release. -/
def CollisionRemovalEffect (pid : PeerId) (d : Device) (p : Peer) (final : Device) : Prop :=
  ∃ removed, RemovalEffect (unlistPeer d pid) p.allowedipsList removed ∧
    LiveRemovalEffect pid (deadPeerDevice removed pid p)
      { erasePeerList p.allowedipsList p with isDead := true } final

end Leanux.Proofs.WG.Config
