import Leanux.Proofs.WG.Noise.SessionModel
import Leanux.Proofs.WG.Index.LifecycleModel

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- The original role-dependent rotation does not release the allocation ID.
This constrains only actual put occurrences, not all slots or reference counts.
It is a static premise here, not a proved reachable-state invariant. -/
def SessionRotationFresh (p : Peer) (id : KeypairId) : Prop :=
  some id ∉ rotationReleases
    (rotationPlan p (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) id)

/-- Successful publication connects the new resident key, the caller's selected
slot and the original handshake index. The final table identifies this row
uniquely by either its numeric index or its embedded owner. -/
def SessionInstalled (pid : PeerId) (initial : Device) (p : Peer) (final : Device) : Prop :=
  ∃ key caller index,
    final.keypairs[initial.nextKeypairId]? = some key ∧
    key.peer = some pid ∧ key.refcount = 1 ∧
    final.peers[pid]? = some caller ∧
    (if p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE then caller.keypairCurrent
      else caller.keypairNext) = some initial.nextKeypairId ∧
    { index, owner := IndexOwner.handshake pid } ∈ initial.indexTable ∧
    { index, owner := IndexOwner.keypair initial.nextKeypairId } ∈ final.indexTable ∧
    (∀ entry ∈ final.indexTable,
      entry.index = index ↔ entry.owner = .keypair initial.nextKeypairId)

end Leanux.Proofs.WG.Index
