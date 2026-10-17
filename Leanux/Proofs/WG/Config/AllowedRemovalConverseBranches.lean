import Leanux.Proofs.WG.Config.AllowedRemovalConverseLeaves
import Leanux.Proofs.WG.Config.AllowedPairsEffects
import Leanux.Proofs.WG.Config.PeerDead

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem removeNodeSource_unary_effect (d : Device) (id : NodeId) (n : AipNode)
    (child : NodeId) (side : Bool) (pairs : NodePairs d)
    (shape : n.bit = if side then #[some child, none] else #[none, some child]) :
    Ensures (removeNodeSource id n) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ ∃ final, w.dev = some final ∧ NodeRemoval d id n final) := by
  let cleared := writeNode d id { n with peer := none }
  have cp : NodePairs cleared := nodePairs_write d id _ pairs (by cases side <;> simp [shape])
  rw [unary_source side id n child shape]
  refine ensures_bind _ _ (removal_returns_ensures_native (unaryBeforeChild_returns side d id n)) ?_
  intro u
  refine ensures_bind _ _ (reparentNode_effect cleared child n.parent) ?_
  intro u w ambient result final after pre run
  obtain ⟨c, read, device⟩ := pre
  let promoted := writeNode cleared child { c with parent := n.parent }
  have pp : NodePairs promoted := nodePairs_write cleared child _ cp (cp child c read)
  have suffix : Ensures (do slotSet n.parent (some child); unaryAfterLink side id : WG.M (ForInStep Unit))
      (fun w => w.dev = some promoted)
      (fun result w => result = .yield () ∧ ∃ final, w.dev = some final ∧ NodeRemoval d id n final) := by
    refine ensures_bind _ _ (slotSet_effect_pairs promoted n.parent (some child) pp) ?_
    intro u w ambient result final after pre run
    obtain ⟨linked, device, write⟩ := pre
    obtain ⟨value, ⟨remaining, resident⟩, output⟩ := unaryAfterLink_effect side linked id w ambient result final after device run
    exact ⟨value, _, output, .unary child c side shape read linked write remaining resident⟩
  exact suffix w ambient result final after device run

theorem leafBeforeParent_effect (d : Device) (id : NodeId) (n : AipNode)
    (pairs : NodePairs d) (shape : n.bit = #[none, none]) :
    Ensures (leafBeforeParent id n) (fun w => w.dev = some d)
      (fun _ w => ∃ linked, w.dev = some linked ∧
        SlotWrite (writeNode d id { n with peer := none }) n.parent none linked) := by
  have hbranch (site : Decision) (value : Bool) (P : WGWorld → Prop) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  unfold leafBeforeParent
  refine ensures_bind _ _ (removal_returns_ensures_native (setNode_returns d id {n with peer := none})) ?_
  intro _
  refine ensures_bind _ _ (hbranch .removeHasBit0 false _) ?_
  intro _
  refine ensures_bind _ _ (hbranch .removeChildExists false _) ?_
  intro _
  refine ensures_bind _ _ (slotSet_effect_pairs
    (writeNode d id {n with peer := none}) n.parent none
    (nodePairs_write d id _ pairs (by simp [shape]))) ?_
  intro _
  refine ensures_bind _ _ (hbranch .removeLeafBit0 true _) ?_
  intro _
  refine ensures_bind _ _ (hbranch .removeLeafBit1 true _) ?_
  intro _ g ambient result final after pre run
  cases run
  exact pre

theorem leafAfterDecision_false_effect (d : Device) (id : NodeId) (n : AipNode) :
    Ensures (leafAfterDecision id n false) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ (∃ remaining, d.nodes[id]? = some remaining) ∧
        w.dev = some { d with nodes := d.nodes.erase id }) := by
  intro g ambient result final after device run
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases resident : d.nodes[id]? with
  | none =>
    simp [leafAfterDecision, branch, AmbientM.branch, aipLift, liftAip, freeNode,
      getNode, getDev, device, resident, invariant, AmbientM.invariant] at run
    cases run
  | some remaining =>
    simp [leafAfterDecision, branch, AmbientM.branch, aipLift, liftAip, freeNode,
      getNode, getDev, modifyDev, device, resident] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, ⟨remaining, rfl⟩, rfl⟩

theorem collapseReadSibling_effect (d : Device) (parent : NodeId) (bit : Nat) :
    Ensures (collapseReadSibling parent bit) (fun w => w.dev = some d)
      (fun sibling w => w.dev = some d ∧ ∃ pn,
        d.nodes[parent]? = some pn ∧ pn.bit[1 - bit]? = some sibling) := by
  intro g ambient result final after device run
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases resident : d.nodes[parent]? with
  | none =>
    simp [collapseReadSibling, branch, AmbientM.branch, aipLift, liftAip, getNode,
      getDev, device, resident, invariant, AmbientM.invariant] at run
    cases run
  | some pn =>
    cases read : pn.bit[1 - bit]? with
    | none =>
      simp [collapseReadSibling, branch, AmbientM.branch, aipLift, liftAip, getNode,
        getDev, modifyDev, device, resident, AipNode.bitAt, read, invariant, AmbientM.invariant] at run
      cases run
    | some sibling =>
      simp [collapseReadSibling, branch, AmbientM.branch, aipLift, liftAip, getNode,
        getDev, modifyDev, device, resident, AipNode.bitAt, read] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, pn, rfl, read⟩

theorem collapseDeleteLeaf_effect (d : Device) (id parent : NodeId) :
    Ensures (collapseDeleteLeaf id parent) (fun w => w.dev = some d)
      (fun pn w => (∃ leaf, d.nodes[id]? = some leaf) ∧
        (d.nodes.erase id)[parent]? = some pn ∧
        w.dev = some { d with nodes := d.nodes.erase id }) := by
  intro g ambient result final after device run
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases resident : d.nodes[id]? with
  | none =>
    simp [collapseDeleteLeaf, branch, AmbientM.branch, aipLift, liftAip, freeNode,
      getNode, getDev, device, resident, invariant, AmbientM.invariant] at run
    cases run
  | some leaf =>
    cases read : (d.nodes.erase id)[parent]? with
    | none =>
      simp [collapseDeleteLeaf, branch, AmbientM.branch, aipLift, liftAip, freeNode,
        getNode, getDev, modifyDev, device, resident, read, invariant, AmbientM.invariant] at run
      cases run
    | some pn =>
      simp [collapseDeleteLeaf, branch, AmbientM.branch, aipLift, liftAip, freeNode,
        getNode, getDev, modifyDev, device, resident, read] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨⟨leaf, rfl⟩, rfl, rfl⟩

theorem collapseFinish_effect (d : Device) (sibling : Option NodeId) (parent : NodeId)
    (pn : AipNode) (pairs : NodePairs d) :
    Ensures (collapseFinish sibling parent pn) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ ∃ promoted linked remaining,
        ChildReparent d sibling pn.parent promoted ∧ SlotWrite promoted pn.parent sibling linked ∧
        linked.nodes[parent]? = some remaining ∧
        w.dev = some { linked with nodes := linked.nodes.erase parent }) := by
  unfold collapseFinish
  refine ensures_bind _ _ (reparentSibling_effect d sibling pn.parent) ?_
  intro u w ambient result final after pre run
  obtain ⟨promoted, device, reparent⟩ := pre
  have suffix : Ensures (do slotSet pn.parent sibling; freeNode parent; pure (ForInStep.yield ()) : WG.M (ForInStep Unit))
      (fun w => w.dev = some promoted)
      (fun result w => result = .yield () ∧ ∃ promoted linked remaining,
        ChildReparent d sibling pn.parent promoted ∧ SlotWrite promoted pn.parent sibling linked ∧
        linked.nodes[parent]? = some remaining ∧
        w.dev = some { linked with nodes := linked.nodes.erase parent }) := by
    refine ensures_bind _ _ (slotSet_effect_pairs promoted pn.parent sibling
      (childReparent_nodePairs reparent pairs)) ?_
    intro u w ambient result final after pre run
    obtain ⟨linked, device, write⟩ := pre
    have tail : Ensures (do freeNode parent; pure (ForInStep.yield ()) : WG.M (ForInStep Unit)) (fun w => w.dev = some linked)
        (fun result w => result = .yield () ∧ ∃ remaining, linked.nodes[parent]? = some remaining ∧
          w.dev = some { linked with nodes := linked.nodes.erase parent }) := by
      refine ensures_bind _ _ (freeNode_effect linked parent) ?_
      intro _ g ambient result final after pre run
      cases run
      obtain ⟨⟨remaining, read⟩, device⟩ := pre
      exact ⟨rfl, remaining, read, device⟩
    obtain ⟨value, remaining, resident, output⟩ := tail w ambient result final after device run
    exact ⟨value, promoted, linked, remaining, reparent, write, resident, output⟩
  exact suffix w ambient result final after device run

theorem leafCollapse_node_effect (d detached : Device) (id : NodeId) (n : AipNode)
    (pairs : NodePairs detached) (shape : n.bit = #[none, none])
    (unlink : SlotWrite (writeNode d id { n with peer := none }) n.parent none detached)
    (choice : ParentChoice detached n.parent true) :
    Ensures (leafAfterDecision id n true) (fun w => w.dev = some detached)
      (fun result w => result = .yield () ∧ ∃ final, w.dev = some final ∧ NodeRemoval d id n final) := by
  have loc : ∃ parent bit, n.parent = .child parent bit := by
    have locate (slot : Slot) (b : Bool) (h : ParentChoice detached slot b) (yes : b = true) :
        ∃ parent bit, slot = .child parent bit := by
      cases h with
      | root4 => cases yes
      | root6 => cases yes
      | child parent bit pn resident => exact ⟨parent, bit, rfl⟩
    exact locate n.parent true choice rfl
  obtain ⟨parent, bit, location⟩ := loc
  rw [collapse_source id n parent bit location]
  refine ensures_bind _ _ (collapseReadSibling_effect detached parent bit) ?_
  intro sibling w ambient result final after pre run
  obtain ⟨device, pn, parentRead, siblingRead⟩ := pre
  have suffix : Ensures (do let after ← collapseDeleteLeaf id parent; collapseFinish sibling parent after)
      (fun w => w.dev = some detached)
      (fun result w => result = .yield () ∧ ∃ final, w.dev = some final ∧ NodeRemoval d id n final) := by
    refine ensures_bind _ _ (collapseDeleteLeaf_effect detached id parent) ?_
    intro pnAfter w ambient result final after pre run
    obtain ⟨⟨leaf, leafRead⟩, parentAfter, device⟩ := pre
    obtain ⟨value, promoted, linked, remaining, reparent, write, resident, output⟩ :=
      collapseFinish_effect { detached with nodes := detached.nodes.erase id } sibling parent pnAfter
        (nodePairs_erase detached id pairs) w ambient result final after device run
    exact ⟨value, _, output, .collapse detached promoted linked parent bit pn leaf pnAfter remaining sibling
      shape location unlink choice parentRead siblingRead leafRead parentAfter reparent write resident⟩
  exact suffix w ambient result final after device run

end Leanux.Proofs.WG.Config
