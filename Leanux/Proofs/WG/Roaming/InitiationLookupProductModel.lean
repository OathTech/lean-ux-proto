import Leanux.Proofs.WG.Roaming.InitiationModel
import Leanux.Proofs.WG.Campaign2.ProductView

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

/-- Product lookup observations retain the eight original fixture fields. -/
structure InitiationLookup where
  before : Campaign2.Product.Snapshot
  observed : Campaign2.Product.Outcome (Option PeerId)
  result : Option PeerId
  after : Campaign2.Product.Snapshot

def InitiationLookupFacts (key : Key) (pid : PeerId) (out : InitiationLookup) : Prop :=
  out.result = some pid ∧ out.observed = .ok (some pid, out.after) ∧
  ∃ d p, out.before.wg.device = some d ∧
    d.peerHashtable.find? (·.1 == key) = some (key, pid) ∧
    d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2^31 ∧
    out.after.wg.device = some { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } }

end Leanux.Proofs.WG.Roaming.Product
