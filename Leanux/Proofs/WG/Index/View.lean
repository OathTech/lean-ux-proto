import Leanux.Proofs.WG.Campaign2.View
import Leanux.Proofs.WG.Index.AllocationModel

namespace Leanux.Proofs.WG.Index.View
open Leanux Leanux.WG

def tableAt (s : Campaign2.Snapshot) : Option (List IndexEntry) :=
  s.wg.device.map Device.indexTable

def IndicesSafe (s : Campaign2.Snapshot) : Prop :=
  ∃ d, s.wg.device = some d ∧ UniqueIndices d.indexTable

def OwnersBoundedSafe (s : Campaign2.Snapshot) : Prop :=
  ∃ d, s.wg.device = some d ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d

end Leanux.Proofs.WG.Index.View
