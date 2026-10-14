import Leanux.WG.AllowedIps

/-! Exact removal source factors. This layer depends only on the executable
mirror, so resident-access observers can reuse it without a framing cycle. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG

/-- The node-only suffix, after list deletion. Both source continues yield
to the next saved identifier; neither ends the outer peer-removal loop. -/
def removeNodeBody (id : NodeId) : M (ForInStep Unit) := do
  let n ← getNode id
  setNode id { n with peer := none }
  if ← branch .removeHasBit0 (← n.bitAt 0).isSome then
    if ← branch .removeHasBit1 (← n.bitAt 1).isSome then return .yield ()
  let child ← if (← n.bitAt 0).isNone then n.bitAt 1 else n.bitAt 0
  if ← branch .removeChildExists child.isSome then
    if let some c := child then setNode c { (← getNode c) with parent := n.parent }
  slotSet n.parent child
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
    sibling ← (← getNode parent).bitAt (1 - bit)
  freeNode id
  if ← branch .removeNotFreeParent !freeParent then return .yield ()
  let .child parent _ := n.parent | invariant "free_parent without a parent node"
  let pn ← getNode parent
  if ← branch .removeSiblingExists sibling.isSome then
    if let some c := sibling then setNode c { (← getNode c) with parent := pn.parent }
  slotSet pn.parent sibling
  freeNode parent
  return .yield ()

def removeStep (id : NodeId) : M (ForInStep Unit) := do
  _ ← branch .removeListIter true
  listDel id
  removeNodeBody id

def removeByPeerWithStep (pid : PeerId) : M Unit := do
  let p ← getPeer pid
  if ← branch .removeListEmpty p.allowedipsList.isEmpty then return
  modifyDev fun d => { d with peerAllowedips := { d.peerAllowedips with seq := d.peerAllowedips.seq + 1 } }
  let _ ← forIn p.allowedipsList () (fun id _ => removeStep id)
  _ ← branch .removeListIter false

/-- All-input source equality preserves every choice, complete successful
World and exact Stop. It supplies no World or event journal on failure. -/
theorem removeByPeerWithStep_eq (pid : PeerId) :
    removeByPeerWithStep pid = WG.removeByPeer pid := by
  rfl

end Leanux.Proofs.WG.AllowedIps
