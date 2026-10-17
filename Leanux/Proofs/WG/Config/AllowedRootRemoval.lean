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
    Returns (removeNodeSource id n) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ w.dev = some (rootNodeRemoved v4 d id n)) := by
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let after := mark (mark (mark (mark (mark (mark (mark ambient
    .removeHasBit0 false) .removeChildExists false) .removeLeafBit0 true)
    .removeLeafBit1 true) .removeParentIsNode false) .removeFreeParent false)
    .removeNotFreeParent true
  refine ⟨.yield (), {g with dev := some (rootNodeRemoved v4 d id n)}, after, ?_, rfl, rfl⟩
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases v4
  all_goals
    simp [removeNodeSource, aipLift, liftAip, setNode, slotSet, freeNode, getNode,
      getDev, modifyDev, device, AipNode.bitAt, leaf, parent, rootSlot, branch,
      AmbientM.branch, rootNodeRemoved, after, mark]
    rfl

theorem removeByPeerSource_root (v4 : Bool) (d : Device) (p : Peer) (id : NodeId) (n : AipNode)
    (listed : p.allowedipsList = [id]) (resident : d.nodes[id]? = some n)
    (leaf : n.bit = #[none, none]) (parent : n.parent = rootSlot v4) :
    Returns (removeByPeerSource p) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (rootLeafRemoved v4 d id n)) := by
  intro g ambient device
  let bumped := bumpAllowedips d
  let unlisted := deleteListedNodes id bumped bumped.peers.toList
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let before := mark (mark ambient .removeListEmpty false) .removeListIter true
  let g1 := {g with dev := some bumped}
  obtain ⟨done, g2, a2, listRun, dev2⟩ := listDel_returns id bumped g1 before rfl
  cases done
  let g3 := {g2 with dev := some unlisted}
  have node : unlisted.nodes[id]? = some n := by
    simpa [unlisted, deleteListedNodes_nodes, bumped, bumpAllowedips] using resident
  have getRun : ((liftAip (getNode id)).run g2).run a2 = .ok ((n, g3), a2) := by
    simp [liftAip, getNode, getDev, modifyDev, dev2, node, g3, unlisted]
    rfl
  obtain ⟨result, final, after, removeRun, value, dev3⟩ :=
    removeNodeSource_root v4 unlisted id n leaf parent g3 a2 rfl
  subst result
  let finished := mark after .removeListIter false
  refine ⟨(), final, finished, ?_, dev3⟩
  rw [removeByPeer_factor]
  have getLift (nid : NodeId) : (monadLift (getNode nid) : WG.M AipNode) =
      liftAip (getNode nid) := rfl
  simp only [removeByPeerFactored, getLift]
  simp [listed, List.forIn_cons, List.forIn_nil, branch, AmbientM.branch,
    modifyDev, device, mark, before, g1, bumped, bumpAllowedips] at listRun ⊢
  rw [listRun]
  dsimp only [bind, Except.bind]
  rw [getRun]
  dsimp only [bind, Except.bind]
  rw [removeRun]
  rfl

theorem removeByPeer_root (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (id : NodeId) (n : AipNode) (peer : d.peers[pid]? = some p)
    (listed : p.allowedipsList = [id]) (resident : d.nodes[id]? = some n)
    (leaf : n.bit = #[none, none]) (parent : n.parent = rootSlot v4) :
    Returns (removeByPeer pid) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (rootLeafRemoved v4 d id n)) := by
  have hg : Returns (getPeer pid) (fun g => g.dev = some d)
      (fun result g => result = p ∧ g.dev = some d) := by
    intro g ambient device
    refine ⟨p, g, ambient, ?_, rfl, device⟩
    simp [getPeer, getDev, device, peer]
    rfl
  rw [removeByPeer_source]
  apply returns_bind _ _ hg
  intro result g ambient h
  obtain ⟨heq, hd⟩ := h
  subst result
  exact removeByPeerSource_root v4 d p id n listed resident leaf parent g ambient hd
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

end Leanux.Proofs.WG.Config
