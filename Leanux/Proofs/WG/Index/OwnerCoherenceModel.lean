import Leanux.Proofs.WG.Index.OwnerWordModel
import Leanux.Proofs.WG.Campaign2.View

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- A resident embedded owner refers to a positively referenced resident peer.
Handshake entries refer to their containing peer; keypair owners also have a
positive reference count. This is a local state predicate, not reachability. -/
def OwnerCoherent (d : Device) (owner : IndexOwner) : Prop :=
  ∃ pid p, ownerWord d owner = some (some pid) ∧ d.peers[pid]? = some p ∧
    0 < p.refcount ∧ match owner with
    | .handshake own => pid = own
    | .keypair id => ∃ k, d.keypairs[id]? = some k ∧ 0 < k.refcount

/-- Every currently hashed owner satisfies the resident-owner relation.
Unhashed objects and their stale numeric indices are outside this predicate. -/
def HashedOwnersCoherent (d : Device) : Prop :=
  ∀ e ∈ d.indexTable, OwnerCoherent d e.owner

namespace View
/-- Local owner coherence for every device present in the native observation. -/
def OwnerCoherentSafe (s : Campaign2.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → HashedOwnersCoherent d
end View

end Leanux.Proofs.WG.Index
