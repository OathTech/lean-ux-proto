import Leanux.Proofs.WG.Config.AllowedInsertModel
import Leanux.Proofs.WG.Config.AllowedListView

/-! Ordered data effects reuse the existing exact list-delete transformer. -/
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

def transferredPeer (id : NodeId) (p : Peer) : Peer :=
  { p with allowedipsList := listRemove p.allowedipsList id ++ [id] }

def transferRootDevice (d : Device) (id : NodeId) (n : AipNode)
    (target : PeerId) (p : Peer) : Device :=
  let owned := { d with nodes := d.nodes.insert id { n with peer := some target } }
  let unlisted := deleteListedNodes id owned owned.peers.toList
  { unlisted with peers := unlisted.peers.insert target (transferredPeer id p) }

def transferRequestDevice (d : Device) (id : NodeId) (n : AipNode)
    (target : PeerId) (p : Peer) : Device :=
  transferRootDevice (insertSequenceDevice d) id n target p

theorem transferRootDevice_peers (d : Device) (id : NodeId) (n : AipNode)
    (target q : PeerId) (p : Peer) :
    (transferRootDevice d id n target p).peers[q]? =
      if q = target then some (transferredPeer id p)
      else d.peers[q]?.map (eraseListedPeer id) := by
  by_cases same : q = target
  · subst q; simp [transferRootDevice]
  · simp [transferRootDevice, Std.TreeMap.getElem?_insert, same, Ne.symm same,
      deleteListedNodes_lookup]

end Leanux.Proofs.WG.Config
