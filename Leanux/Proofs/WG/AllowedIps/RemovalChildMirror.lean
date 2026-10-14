import Leanux.Proofs.WG.AllowedIps.RemovalMirror

/-! Exact nonroot removal endpoints. Parent slots retain source `set!`
behavior; raw input snapshots do not assert a represented tree or resident
owner labels. Collapse is split at the post-target-free parent reread. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def removalChildUnary (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (child : Nat) (cn : WG.AipNode) : WG.Device :=
  let linked := connectedChild (removalCleared d id n) parent side child pn cn
  { linked with nodes := linked.nodes.erase id }

/-- This intermediate state retains the actual clear, detach, and free order. -/
def removalLeafDetached (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) : WG.Device :=
  let cleared := removalCleared d id n
  let detached := { cleared with nodes := (cleared.nodes.insert parent
    { pn with bit := pn.bit.set! side none }) }
  { detached with nodes := detached.nodes.erase id }

theorem removeNodeBody_child_unary_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (left : Bool) (id parent side child : Nat) (n pn cn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hc : d.nodes[child]? = some cn) (hip : id ≠ parent) (hic : id ≠ child)
    (hcp : child ≠ parent) (hb : side ≤ 1)
    (hbits : n.bit = if left then #[some child, none] else #[none, some child])
    (hparent : n.parent = .child parent side) :
    ⦃fun w => ⌜w.k = k⌝⦄ removeNodeBody id
    ⦃⇓ result w => ⌜result = .yield () ∧ w.k = { k with wg := some (removalChildUnary d id n parent side pn child cn) }⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  let events : List (Decision × Bool) := if left then
    [(.removeHasBit0, true), (.removeHasBit1, false), (.removeChildExists, true),
      (.removeLeafBit0, false), (.removeFreeParent, false), (.removeNotFreeParent, true)] else
    [(.removeHasBit0, false), (.removeChildExists, true), (.removeLeafBit0, true),
      (.removeLeafBit1, false), (.removeFreeParent, false), (.removeNotFreeParent, true)]
  refine ⟨.yield (), { removalRecords w events with k := { k with wg := some (removalChildUnary d id n parent side pn child cn) } }, ?_, rfl, rfl⟩
  cases left <;> simp [removeNodeBody, WG.getNode, WG.getDev, getK, WG.setNode,
    WG.modifyDev, modifyK, WG.AipNode.bitAt, WG.slotSet, WG.freeNode, branch,
    hkw, hd, hn, hp, hc, hbits, hparent, removalChildUnary, connectedChild,
    removalCleared, removalRecords, record, events, show ¬ side > 1 from by omega,
    Std.TreeMap.getElem?_insert, hip, Ne.symm hip, hic, Ne.symm hic, hcp, Ne.symm hcp]
  all_goals rfl

theorem removeNodeBody_child_leaf_owned_wp (k : Kernel) (d : WG.Device)
    (hd : k.wg = some d) (id parent side : Nat) (n pn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hip : id ≠ parent) (hb : side ≤ 1) (howner : pn.peer.isSome)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side) :
    ⦃fun w => ⌜w.k = k⌝⦄ removeNodeBody id
    ⦃⇓ result w => ⌜result = .yield () ∧ w.k = { k with wg := some (removalLeafDetached d id n parent side pn) }⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  refine ⟨.yield (), { removalRecords w [(.removeHasBit0, false), (.removeChildExists, false),
    (.removeLeafBit0, true), (.removeLeafBit1, true), (.removeParentIsNode, true),
    (.removeParentNoPeer, false), (.removeFreeParent, false), (.removeNotFreeParent, true)] with
    k := { k with wg := some (removalLeafDetached d id n parent side pn) } }, ?_, rfl, rfl⟩
  have ho : pn.peer.isNone = false := by cases h : pn.peer <;> simp_all
  have hnone : pn.peer ≠ none := by cases h : pn.peer <;> simp_all
  simp [removeNodeBody, WG.getNode, WG.getDev, getK, WG.setNode, WG.modifyDev,
    modifyK, WG.AipNode.bitAt, WG.slotSet, WG.freeNode, branch, hkw, hd, hn, hp,
    hbits, hparent, ho, hnone, howner, removalLeafDetached, removalCleared, removalRecords, record,
    show ¬ side > 1 from by omega, Std.TreeMap.getElem?_insert, hip, Ne.symm hip]
  rfl

end Leanux.Proofs.WG.AllowedIps
