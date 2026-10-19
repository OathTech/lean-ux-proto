import Leanux.Proofs.WG.AllowedIps.RemovalChildMirror

/-! The original collapse continuation and its exact endpoints. Optional
sibling snapshots describe input records, including the absent-sibling path;
they do not replace any source getter or require owner residency. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def removalSibling (d : WG.Device) (sibling : Option (Nat × WG.AipNode))
    (base : WG.Slot) : WG.Device :=
  match sibling with
  | none => d
  | some (id, n) => { d with nodes := d.nodes.insert id { n with parent := base } }

def removalParentRoot (d : WG.Device) (parent : Nat) (v4 : Bool)
    (sibling : Option (Nat × WG.AipNode)) : WG.Device :=
  let linked := rootWrite (removalSibling d sibling (rootSlot v4)) v4 (sibling.map Prod.fst)
  { linked with nodes := linked.nodes.erase parent }

def removalParentChild (d : WG.Device) (parent grand side : Nat) (gn : WG.AipNode)
    (sibling : Option (Nat × WG.AipNode)) : WG.Device :=
  let reparented := removalSibling d sibling (.child grand side)
  let linked := { reparented with nodes := (reparented.nodes.insert grand
    { gn with bit := gn.bit.set! side (sibling.map Prod.fst) }) }
  { linked with nodes := linked.nodes.erase parent }

theorem removeParentTail_root_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (parent : Nat) (pn : WG.AipNode) (v4 : Bool) (sibling : Option (Nat × WG.AipNode))
    (hp : d.nodes[parent]? = some pn) (hbase : pn.parent = rootSlot v4)
    (hs : ∀ c cn, sibling = some (c, cn) → d.nodes[c]? = some cn ∧ c ≠ parent) :
    ⦃fun w => ⌜w = k⌝⦄ removeParentTail parent (sibling.map Prod.fst)
    ⦃⇓ result w => ⌜result = .yield () ∧
      w = { k with dev := some (removalParentRoot d parent v4 sibling) }⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  subst w
  refine ⟨.yield (), { k with dev := some (removalParentRoot d parent v4 sibling) },
    removalRecords ambient [(.removeSiblingExists, sibling.isSome)], ?_, rfl, rfl⟩
  cases sibling with
  | none =>
    cases v4 <;> simp [removeParentTail, liftM, MonadLiftT.monadLift, MonadLift.monadLift, WG.liftAip, WG.getNode, WG.getDev, WG.setNode,
      WG.modifyDev, WG.slotSet, WG.freeNode, branch, AmbientM.branch, hd, hp, hbase,
      removalParentRoot, removalSibling, rootWrite, rootSlot, removalRecords, record]
    all_goals rfl
  | some sibling =>
    rcases sibling with ⟨c, cn⟩
    obtain ⟨hc, hcp⟩ := hs c cn rfl
    cases v4 <;> simp [removeParentTail, liftM, MonadLiftT.monadLift, MonadLift.monadLift, WG.liftAip, WG.getNode, WG.getDev, WG.setNode,
      WG.modifyDev, WG.slotSet, WG.freeNode, branch, AmbientM.branch, hd, hp, hc, hbase,
      removalParentRoot, removalSibling, rootWrite, rootSlot, removalRecords, record,
      Std.TreeMap.getElem?_insert, hcp]
    all_goals rfl

theorem removeParentTail_child_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (parent grand side : Nat) (pn gn : WG.AipNode) (sibling : Option (Nat × WG.AipNode))
    (hp : d.nodes[parent]? = some pn) (hg : d.nodes[grand]? = some gn)
    (hbase : pn.parent = .child grand side) (hpg : parent ≠ grand) (hb : side ≤ 1)
    (hs : ∀ c cn, sibling = some (c, cn) →
      d.nodes[c]? = some cn ∧ c ≠ parent ∧ c ≠ grand) :
    ⦃fun w => ⌜w = k⌝⦄ removeParentTail parent (sibling.map Prod.fst)
    ⦃⇓ result w => ⌜result = .yield () ∧
      w = { k with dev := some (removalParentChild d parent grand side gn sibling) }⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  subst w
  refine ⟨.yield (), { k with dev := some (removalParentChild d parent grand side gn sibling) },
    removalRecords ambient [(.removeSiblingExists, sibling.isSome)], ?_, rfl, rfl⟩
  cases sibling with
  | none =>
    simp [removeParentTail, liftM, MonadLiftT.monadLift, MonadLift.monadLift, WG.liftAip, WG.getNode, WG.getDev, WG.setNode, WG.modifyDev,
      WG.slotSet, WG.freeNode, branch, AmbientM.branch, hd, hp, hg, hbase,
      removalParentChild, removalSibling, removalRecords, record,
      show ¬ side > 1 from by omega, Std.TreeMap.getElem?_insert, Ne.symm hpg]
    rfl
  | some sibling =>
    rcases sibling with ⟨c, cn⟩
    obtain ⟨hc, hcp, hcg⟩ := hs c cn rfl
    simp [removeParentTail, liftM, MonadLiftT.monadLift, MonadLift.monadLift, WG.liftAip, WG.getNode, WG.getDev, WG.setNode, WG.modifyDev,
      WG.slotSet, WG.freeNode, branch, AmbientM.branch, hd, hp, hg, hc, hbase,
      removalParentChild, removalSibling, removalRecords, record,
      show ¬ side > 1 from by omega, Std.TreeMap.getElem?_insert, hcp, hcg, Ne.symm hpg]
    rfl

def removalCollapseRecords : List (Decision × Bool) :=
  [(.removeHasBit0, false), (.removeChildExists, false), (.removeLeafBit0, true),
    (.removeLeafBit1, true), (.removeParentIsNode, true), (.removeParentNoPeer, true),
    (.removeFreeParent, true), (.removeNotFreeParent, false)]

/-- Only the completed prefix needs to be well formed. Missing sibling or
grandparent records remain exact Stops of the original continuation. -/
theorem removeNodeBody_leaf_collapse_run (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (id parent side : Nat) (n pn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hip : id ≠ parent) (hb : side ≤ 1) (howner : pn.peer = none)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side)
    (sibling : Option Nat) (hs : pn.bit[1-side]? = some sibling) :
    ((removeNodeBody id).run w).run ambient =
      ((removeParentTail parent sibling).run
        { w with dev := some (removalLeafDetached d id n parent side pn) }).run
          (removalRecords ambient removalCollapseRecords) := by
  have hside : side = 0 ∨ side = 1 := by omega
  have hs' : (pn.bit.set! side none)[1-side]? = some sibling := by
    rcases hside with rfl | rfl <;>
      simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] using hs
  have hs'' : (pn.bit.setIfInBounds side none)[1-side]? = some sibling := by
    simpa only [Array.set!_eq_setIfInBounds] using hs'
  simp [removeNodeBody, liftM, MonadLiftT.monadLift, MonadLift.monadLift, WG.liftAip, WG.getNode, WG.getDev, WG.setNode, WG.modifyDev,
    WG.AipNode.bitAt, WG.slotSet, WG.freeNode, branch, AmbientM.branch, hd, hn, hp,
    hbits, hparent, howner, hs'', removalLeafDetached, removalCleared,
    removalRecords, removalCollapseRecords, record, show ¬ side > 1 from by omega,
    Std.TreeMap.getElem?_insert, hip, Ne.symm hip]

end Leanux.Proofs.WG.AllowedIps
