import Leanux.Proofs.WG.Config.AllowedRemovalSource

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def rootSlot (v4 : Bool) : Slot := if v4 then .root4 else .root6

def bumpAllowedips (d : Device) : Device :=
  { d with peerAllowedips := { d.peerAllowedips with seq := d.peerAllowedips.seq + 1 } }

def rootNodeRemoved (v4 : Bool) (d : Device) (id : NodeId) (n : AipNode) : Device :=
  let unowned := { d with nodes := d.nodes.insert id { n with peer := none } }
  let unrooted := { unowned with peerAllowedips := if v4 then
    { unowned.peerAllowedips with root4 := none } else { unowned.peerAllowedips with root6 := none } }
  { unrooted with nodes := unrooted.nodes.erase id }

def rootLeafRemoved (v4 : Bool) (d : Device) (id : NodeId) (n : AipNode) : Device :=
  let bumped := bumpAllowedips d
  rootNodeRemoved v4 (deleteListedNodes id bumped bumped.peers.toList) id n

theorem removeNodeSource_root (v4 : Bool) (d : Device) (id : NodeId) (n : AipNode)
    (leaf : n.bit = #[none, none]) (parent : n.parent = rootSlot v4) :
    Returns (removeNodeSource id n) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ w.k.wg = some (rootNodeRemoved v4 d id n)) := by
  rw [returns_iff]
  cases v4
  all_goals simp [removeNodeSource, AipNode.bitAt, leaf, parent, rootSlot, branch, bind_assoc]
  all_goals mvcgen [setNode, slotSet, modifyDev, modifyK, freeNode, getNode, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [rootNodeRemoved]
  all_goals subst_vars
  all_goals simp_all [rootSlot]

theorem removeByPeerSource_root (v4 : Bool) (d : Device) (p : Peer) (id : NodeId) (n : AipNode)
    (listed : p.allowedipsList = [id]) (resident : d.nodes[id]? = some n)
    (leaf : n.bit = #[none, none]) (parent : n.parent = rootSlot v4) :
    Returns (removeByPeerSource p) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (rootLeafRemoved v4 d id n)) := by
  let bumped := bumpAllowedips d
  let unlisted := deleteListedNodes id bumped bumped.peers.toList
  have hl := (returns_iff _ _ _).mp (listDel_returns id bumped)
  have hg : ⦃fun w => ⌜w.k.wg = some unlisted⌝⦄ getNode id
      ⦃⇓ result w => ⌜result = n ∧ w.k.wg = some unlisted⌝⦄ := by
    mvcgen [getNode, getDev, getK, invariant]
    all_goals simp_all [unlisted, bumped, bumpAllowedips, deleteListedNodes_nodes]
  have hn := (returns_iff _ _ _).mp (removeNodeSource_root v4 unlisted id n leaf parent)
  rw [removeByPeer_factor, returns_iff]
  simp [removeByPeerFactored, listed, List.forIn_cons, List.forIn_nil, branch, bind_assoc]
  mvcgen [modifyDev, modifyK, hl, hg, hn]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [bumped, bumpAllowedips, rootLeafRemoved, unlisted]
  all_goals subst_vars
  all_goals mvcgen [hg, hn]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [bumpAllowedips, rootLeafRemoved]
  all_goals grind only

theorem removeByPeer_root (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (id : NodeId) (n : AipNode) (peer : d.peers[pid]? = some p)
    (listed : p.allowedipsList = [id]) (resident : d.nodes[id]? = some n)
    (leaf : n.bit = #[none, none]) (parent : n.parent = rootSlot v4) :
    Returns (removeByPeer pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (rootLeafRemoved v4 d id n)) := by
  have hg : Returns (getPeer pid) (fun w => w.k.wg = some d)
      (fun result w => result = p ∧ w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [getPeer, getDev, getK, invariant]
    all_goals simp_all
  rw [removeByPeer_source]
  apply returns_bind _ _ hg
  intro result w h
  obtain ⟨heq, hd⟩ := h
  subst result
  exact removeByPeerSource_root v4 d p id n listed resident leaf parent w hd

theorem rootLeafRemoved_peer (v4 : Bool) (d : Device) (id : NodeId) (n : AipNode) (q : PeerId) :
    (rootLeafRemoved v4 d id n).peers[q]? = d.peers[q]?.map (eraseListedPeer id) := by
  simpa [rootLeafRemoved, rootNodeRemoved, bumpAllowedips] using
    deleteListedNodes_lookup id (bumpAllowedips d) q

theorem rootLeafRemoved_node (v4 : Bool) (d : Device) (id : NodeId) (n : AipNode) (q : NodeId) :
    (rootLeafRemoved v4 d id n).nodes[q]? = if q = id then none else d.nodes[q]? := by
  by_cases same : q = id
  · subst q
    simp [rootLeafRemoved, rootNodeRemoved]
  · simp [rootLeafRemoved, rootNodeRemoved, Std.TreeMap.getElem?_erase,
      Std.TreeMap.getElem?_insert, Ne.symm same, same, deleteListedNodes_nodes, bumpAllowedips]

theorem rootLeafRemoved_table (v4 : Bool) (d : Device) (id : NodeId) (n : AipNode) :
    (rootLeafRemoved v4 d id n).peerAllowedips =
      if v4 then { d.peerAllowedips with root4 := none, seq := d.peerAllowedips.seq + 1 }
      else { d.peerAllowedips with root6 := none, seq := d.peerAllowedips.seq + 1 } := by
  cases v4 <;> simp [rootLeafRemoved, rootNodeRemoved, deleteListedNodes_allowedips, bumpAllowedips]

theorem rootLeafRemoved_running (v4 : Bool) (d : Device) (id : NodeId) (n : AipNode) :
    (rootLeafRemoved v4 d id n).running = d.running := by
  simpa [rootLeafRemoved, rootNodeRemoved, withoutPeers, bumpAllowedips] using
    congrArg Device.running (deleteListedNodes_withoutPeers id (bumpAllowedips d) (bumpAllowedips d).peers.toList)

end Leanux.Proofs.WG.Config
