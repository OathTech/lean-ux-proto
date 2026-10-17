import Leanux.Proofs.WG.Index.OwnerCoherenceQuietRemovalModel
import Leanux.Proofs.WG.Noise.ClearModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- At a last peer reference, every hashed owner naming the peer is its own
handshake entry or a keypair in one of its three original slots. This states
coverage, not freshness, reference multiplicity or execution readiness. -/
def LastOwnerCovered (d : Device) (pid : PeerId) (p : Peer) : Prop :=
  p.refcount = 1 → ∀ e ∈ d.indexTable, ownerWord d e.owner = some (some pid) →
    e.owner = .handshake pid ∨ ∃ id, e.owner = .keypair id ∧ some id ∈ clearKeys p

end Leanux.Proofs.WG.Index
