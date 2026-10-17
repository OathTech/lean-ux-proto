import Leanux.Proofs.WG.Config.AllowedListView

set_option pp.structureInstances false
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Exact original continuation after the peer read. -/
def removeByPeerSource (p : Peer) : WG.M Unit := do
  if ← branch .removeListEmpty p.allowedipsList.isEmpty then return
  modifyDev fun d => { d with peerAllowedips := { d.peerAllowedips with seq := d.peerAllowedips.seq + 1 } }
  for id in p.allowedipsList do   -- list_for_each_entry_safe over the peer's list
    _ ← branch .removeListIter true
    listDel id                    -- list_del_init(&node->peer_list)
    let n ← getNode id
    setNode id { n with peer := none }
    -- `if (node->bit[0] && node->bit[1]) continue;`
    if ← branch .removeHasBit0 (← n.bitAt 0).isSome then
      if ← branch .removeHasBit1 (← n.bitAt 1).isSome then continue
    let child ← if (← n.bitAt 0).isNone then n.bitAt 1 else n.bitAt 0   -- bit[!bit[0]]
    if ← branch .removeChildExists child.isSome then
      if let some c := child then setNode c { (← getNode c) with parent := n.parent }
    slotSet n.parent child   -- *parent_bit = child
    -- free_parent = !bit[0] && !bit[1] && (parent_bit_packed & 3) <= 1 && !parent->peer
    let freeParent ← do
      if !(← branch .removeLeafBit0 (← n.bitAt 0).isNone) then pure false
      else if !(← branch .removeLeafBit1 (← n.bitAt 1).isNone) then pure false
      else match n.parent with
        | .child parent _ => do
          _ ← branch .removeParentIsNode true
          branch .removeParentNoPeer (← getNode parent).peer.isNone
        | _ => do
          _ ← branch .removeParentIsNode false
          pure false
    let mut sibling := child
    if ← branch .removeFreeParent freeParent then
      let .child parent bit := n.parent | invariant "free_parent without a parent node"
      sibling ← (← getNode parent).bitAt (1 - bit)   -- parent->bit[!(parent_bit_packed & 1)]
    freeNode id   -- call_rcu(&node->rcu, node_free_rcu)
    if ← branch .removeNotFreeParent !freeParent then continue
    let .child parent _ := n.parent | invariant "free_parent without a parent node"
    let pn ← getNode parent
    if ← branch .removeSiblingExists sibling.isSome then
      if let some c := sibling then setNode c { (← getNode c) with parent := pn.parent }
    slotSet pn.parent sibling
    freeNode parent   -- call_rcu(&parent->rcu, node_free_rcu)
  _ ← branch .removeListIter false

theorem removeByPeer_source (pid : PeerId) :
    removeByPeer pid = (do let p ← getPeer pid; removeByPeerSource p) := rfl

/-- Exact original loop continuation after the node read. -/
def removeNodeSource (id : NodeId) (n : AipNode) : WG.M (ForInStep Unit) := do
  setNode id { n with peer := none }
  -- `if (node->bit[0] && node->bit[1]) continue;`
  if ← branch .removeHasBit0 (← n.bitAt 0).isSome then
    if ← branch .removeHasBit1 (← n.bitAt 1).isSome then return .yield ()
  let child ← if (← n.bitAt 0).isNone then n.bitAt 1 else n.bitAt 0   -- bit[!bit[0]]
  if ← branch .removeChildExists child.isSome then
    if let some c := child then setNode c { (← getNode c) with parent := n.parent }
  slotSet n.parent child   -- *parent_bit = child
  -- free_parent = !bit[0] && !bit[1] && (parent_bit_packed & 3) <= 1 && !parent->peer
  let freeParent ← do
    if !(← branch .removeLeafBit0 (← n.bitAt 0).isNone) then pure false
    else if !(← branch .removeLeafBit1 (← n.bitAt 1).isNone) then pure false
    else match n.parent with
      | .child parent _ => do
        _ ← branch .removeParentIsNode true
        branch .removeParentNoPeer (← getNode parent).peer.isNone
      | _ => do
        _ ← branch .removeParentIsNode false
        pure false
  let mut sibling := child
  if ← branch .removeFreeParent freeParent then
    let .child parent bit := n.parent | do
      invariant "free_parent without a parent node"
      return .yield ()
    sibling ← (← getNode parent).bitAt (1 - bit)   -- parent->bit[!(parent_bit_packed & 1)]
  freeNode id   -- call_rcu(&node->rcu, node_free_rcu)
  if ← branch .removeNotFreeParent !freeParent then return .yield ()
  let .child parent _ := n.parent | do
    invariant "free_parent without a parent node"
    return .yield ()
  let pn ← getNode parent
  if ← branch .removeSiblingExists sibling.isSome then
    if let some c := sibling then setNode c { (← getNode c) with parent := pn.parent }
  slotSet pn.parent sibling
  freeNode parent   -- call_rcu(&parent->rcu, node_free_rcu)
  return .yield ()

def removeByPeerFactored (p : Peer) : WG.M Unit := do
  if ← branch .removeListEmpty p.allowedipsList.isEmpty then return
  modifyDev fun d => { d with peerAllowedips := { d.peerAllowedips with seq := d.peerAllowedips.seq + 1 } }
  let _ ← forIn p.allowedipsList () fun id _ => do
    _ ← branch .removeListIter true
    listDel id
    let n ← getNode id
    removeNodeSource id n
  _ ← branch .removeListIter false

theorem removeByPeer_factor (p : Peer) : removeByPeerSource p = removeByPeerFactored p := rfl

end Leanux.Proofs.WG.Config
