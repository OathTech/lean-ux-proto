import Leanux.Proofs.WG.Peers.Affiliation
import Leanux.Proofs.WG.Index.OwnerCoherenceModel
import Leanux.Proofs.WG.Index.LifecycleModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Local session invariant: compatible bounded references, both table
uniqueness properties, and resident positive hashed owners. It is not a
claim that driver initialization and every operation establish these facts. -/
structure SessionIndexInvariant (d : Device) : Prop where
  affiliation : Affiliation.State.Inv (Affiliation.state d)
  indices : UniqueIndices d.indexTable
  owners : UniqueOwners d.indexTable
  coherent : HashedOwnersCoherent d

namespace View
def SessionIndexSafe (s : Campaign2.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → SessionIndexInvariant d
end View

end Leanux.Proofs.WG.Index
