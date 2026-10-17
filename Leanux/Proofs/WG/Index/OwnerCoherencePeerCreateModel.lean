import Leanux.Proofs.WG.Index.OwnerCoherenceModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Initialization changes only the target peer among the owner-bearing
stores. The target may already exist; no allocation freshness is assumed. -/
def PeerCreateFootprint (before after : Device) (pid : PeerId) : Prop :=
  after.indexTable = before.indexTable ∧ after.keypairs = before.keypairs ∧
    ∀ other, other ≠ pid → after.peers[other]? = before.peers[other]?

end Leanux.Proofs.WG.Index
