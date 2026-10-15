import Leanux.Proofs.WG.Config.AllowedStructural

/-! Pure state observations and transformations shared by removal effects and frames. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Fields outside the node store and the two allowed-IP roots; sequence is retained. -/
def withoutTrie (d : Device) : Device :=
  { d with nodes := {}, peerAllowedips := { d.peerAllowedips with root4 := none, root6 := none } }

def erasePeerList : List NodeId → Peer → Peer
  | [], p => p
  | id :: rest, p => erasePeerList rest (eraseListedPeer id p)

/-- Missing nodes and resident nodes with no peer both have no owner. -/
def nodeOwner (d : Device) (id : NodeId) : Option PeerId :=
  d.nodes[id]?.bind AipNode.peer

theorem writeNode_owner (d : Device) (id tracked : NodeId) (n : AipNode) :
    nodeOwner (writeNode d id n) tracked = if tracked = id then n.peer else nodeOwner d tracked := by
  by_cases same : tracked = id <;> simp [nodeOwner, writeNode, Std.TreeMap.getElem?_insert, same, Ne.symm]

/-- Device membership metadata unchanged by allowed-IP removal. -/
def removalMetadata (d : Device) := (d.peerList, d.peerHashtable, d.indexTable, d.numPeers)

def removalQueues (d : Device) := (d.sendWorkQueue, d.clearWorkQueue)

end Leanux.Proofs.WG.Config
