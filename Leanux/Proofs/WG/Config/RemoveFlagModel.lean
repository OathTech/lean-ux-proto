import Leanux.Proofs.WG.Config.CollisionModel

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- The configuration lookup acquires a reference before removal. Removal's
own put leaves the original count; the caller then performs its final put. -/
def RemoveFlagEffect (pid : PeerId) (d : Device) (p : Peer) (final : Device) : Prop :=
  ∃ removed q,
    CollisionRemovalEffect pid (withPeer d pid { p with refcount := p.refcount + 1 })
      { p with refcount := p.refcount + 1 } removed ∧
    removed.peers[pid]? = some q ∧ q.refcount = p.refcount ∧
    final = Index.releasedPeerDevice removed pid q

end Leanux.Proofs.WG.Config
