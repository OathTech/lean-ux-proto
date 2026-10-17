import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Only the allowed-IP list is hidden; peer identity, reference count, owner
word, slots and every other peer field remain observable pointwise. -/
def aipOwnerPeer (p : Peer) : Peer := {p with allowedipsList := []}

/-- Fields needed to carry owner coherence and slot coverage through trie
removal. The peer map is observed by lookup, not representation equality. -/
def aipOwnerView (d : Device) :=
  (d.indexTable, d.keypairs, (fun pid : PeerId => d.peers[pid]?.map aipOwnerPeer),
    d.numPeers, d.sendWorkQueue, d.clearWorkQueue)

end Leanux.Proofs.WG.Index
