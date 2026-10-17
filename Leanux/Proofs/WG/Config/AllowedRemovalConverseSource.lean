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
    Ensures (removeNodeSource id n) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ ∃ final, w.k.wg = some final ∧ NodeRemoval d id n final) := by
  let cleared := writeNode d id { n with peer := none }
  have cp : NodePairs cleared := nodePairs_write d id _ pairs (by cases side <;> simp [shape])
  rw [unary_source side id n child shape]
  refine ensures_bind _ _ (removal_returns_ensures (unaryBeforeChild_returns side d id n)) ?_
  intro u
  refine ensures_bind _ _ (reparentNode_effect cleared child n.parent) ?_
  intro u w result final pre run
  obtain ⟨c, read, device⟩ := pre
  let promoted := writeNode cleared child { c with parent := n.parent }
  have pp : NodePairs promoted := nodePairs_write cleared child _ cp (cp child c read)
  have suffix : Ensures (do slotSet n.parent (some child); unaryAfterLink side id)
      (fun w => w.k.wg = some promoted)
      (fun result w => result = .yield () ∧ ∃ final, w.k.wg = some final ∧ NodeRemoval d id n final) := by
    refine ensures_bind _ _ (slotSet_effect_pairs promoted n.parent (some child) pp) ?_
    intro u w result final pre run
    obtain ⟨linked, device, write⟩ := pre
    obtain ⟨value, ⟨remaining, resident⟩, output⟩ := unaryAfterLink_effect side linked id w result final device run
    exact ⟨value, _, output, .unary child c side shape read linked write remaining resident⟩
  exact suffix w result final device run

theorem leafBeforeParent_effect (d : Device) (id : NodeId) (n : AipNode)
    (pairs : NodePairs d) (shape : n.bit = #[none, none]) :
    Ensures (leafBeforeParent id n) (fun w => w.k.wg = some d)
      (fun _ w => ∃ linked, w.k.wg = some linked ∧
        SlotWrite (writeNode d id { n with peer := none }) n.parent none linked) := by
  have hs := (ensures_iff _ _ _).mp (slotSet_effect_pairs
    (writeNode d id { n with peer := none }) n.parent none
    (nodePairs_write d id _ pairs (by simp [shape])))
  rw [ensures_iff]
  mvcgen [leafBeforeParent, branch, setNode, modifyDev, modifyK, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [writeNode]

theorem leafAfterDecision_false_effect (d : Device) (id : NodeId) (n : AipNode) :
    Ensures (leafAfterDecision id n false) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ (∃ remaining, d.nodes[id]? = some remaining) ∧
        w.k.wg = some { d with nodes := d.nodes.erase id }) := by
  have hf := (ensures_iff _ _ _).mp (freeNode_effect d id)
  rw [ensures_iff]
  simp only [leafAfterDecision]
  mvcgen [branch, hf]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem collapseReadSibling_effect (d : Device) (parent : NodeId) (bit : Nat) :
    Ensures (collapseReadSibling parent bit) (fun w => w.k.wg = some d)
      (fun sibling w => w.k.wg = some d ∧ ∃ pn,
        d.nodes[parent]? = some pn ∧ pn.bit[1 - bit]? = some sibling) := by
  rw [ensures_iff]
  mvcgen [collapseReadSibling, branch, getNode, getDev, getK, AipNode.bitAt, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem collapseDeleteLeaf_effect (d : Device) (id parent : NodeId) :
    Ensures (collapseDeleteLeaf id parent) (fun w => w.k.wg = some d)
      (fun pn w => (∃ leaf, d.nodes[id]? = some leaf) ∧
        (d.nodes.erase id)[parent]? = some pn ∧
        w.k.wg = some { d with nodes := d.nodes.erase id }) := by
  have hf := (ensures_iff _ _ _).mp (freeNode_effect d id)
  rw [ensures_iff]
  mvcgen [collapseDeleteLeaf, branch, getNode, getDev, getK, invariant, hf]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem collapseFinish_effect (d : Device) (sibling : Option NodeId) (parent : NodeId)
    (pn : AipNode) (pairs : NodePairs d) :
    Ensures (collapseFinish sibling parent pn) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ ∃ promoted linked remaining,
        ChildReparent d sibling pn.parent promoted ∧ SlotWrite promoted pn.parent sibling linked ∧
        linked.nodes[parent]? = some remaining ∧
        w.k.wg = some { linked with nodes := linked.nodes.erase parent }) := by
  unfold collapseFinish
  refine ensures_bind _ _ (reparentSibling_effect d sibling pn.parent) ?_
  intro u w result final pre run
  obtain ⟨promoted, device, reparent⟩ := pre
  have suffix : Ensures (do slotSet pn.parent sibling; freeNode parent; pure (ForInStep.yield ()))
      (fun w => w.k.wg = some promoted)
      (fun result w => result = .yield () ∧ ∃ promoted linked remaining,
        ChildReparent d sibling pn.parent promoted ∧ SlotWrite promoted pn.parent sibling linked ∧
        linked.nodes[parent]? = some remaining ∧
        w.k.wg = some { linked with nodes := linked.nodes.erase parent }) := by
    refine ensures_bind _ _ (slotSet_effect_pairs promoted pn.parent sibling
      (childReparent_nodePairs reparent pairs)) ?_
    intro u w result final pre run
    obtain ⟨linked, device, write⟩ := pre
    have hf := (ensures_iff _ _ _).mp (freeNode_effect linked parent)
    have tail : Ensures (do freeNode parent; pure (ForInStep.yield ())) (fun w => w.k.wg = some linked)
        (fun result w => result = .yield () ∧ ∃ remaining, linked.nodes[parent]? = some remaining ∧
          w.k.wg = some { linked with nodes := linked.nodes.erase parent }) := by
      rw [ensures_iff]
      mvcgen [hf]
      all_goals try dsimp +zetaDelta only at *
      all_goals grind
    obtain ⟨value, remaining, resident, output⟩ := tail w result final device run
    exact ⟨value, promoted, linked, remaining, reparent, write, resident, output⟩
  exact suffix w result final device run

theorem leafCollapse_node_effect (d detached : Device) (id : NodeId) (n : AipNode)
    (pairs : NodePairs detached) (shape : n.bit = #[none, none])
    (unlink : SlotWrite (writeNode d id { n with peer := none }) n.parent none detached)
    (choice : ParentChoice detached n.parent true) :
    Ensures (leafAfterDecision id n true) (fun w => w.k.wg = some detached)
      (fun result w => result = .yield () ∧ ∃ final, w.k.wg = some final ∧ NodeRemoval d id n final) := by
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
  intro sibling w result final pre run
  obtain ⟨device, pn, parentRead, siblingRead⟩ := pre
  have suffix : Ensures (do let after ← collapseDeleteLeaf id parent; collapseFinish sibling parent after)
      (fun w => w.k.wg = some detached)
      (fun result w => result = .yield () ∧ ∃ final, w.k.wg = some final ∧ NodeRemoval d id n final) := by
    refine ensures_bind _ _ (collapseDeleteLeaf_effect detached id parent) ?_
    intro pnAfter w result final pre run
    obtain ⟨⟨leaf, leafRead⟩, parentAfter, device⟩ := pre
    obtain ⟨value, promoted, linked, remaining, reparent, write, resident, output⟩ :=
      collapseFinish_effect { detached with nodes := detached.nodes.erase id } sibling parent pnAfter
        (nodePairs_erase detached id pairs) w result final device run
    exact ⟨value, _, output, .collapse detached promoted linked parent bit pn leaf pnAfter remaining sibling
      shape location unlink choice parentRead siblingRead leafRead parentAfter reparent write resident⟩
  exact suffix w result final device run

theorem removeNodeSource_leaf_effect (d : Device) (id : NodeId) (n : AipNode)
    (pairs : NodePairs d) (shape : n.bit = #[none, none]) :
    Ensures (removeNodeSource id n) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ ∃ final, w.k.wg = some final ∧ NodeRemoval d id n final) := by
  rw [leaf_source id n shape]
  refine ensures_bind _ _ (leafBeforeParent_effect d id n pairs shape) ?_
  intro u w result final pre run
  obtain ⟨linked, device, write⟩ := pre
  have lp : NodePairs linked := slotWrite_nodePairs write (nodePairs_write d id _ pairs (by simp [shape]))
  have suffix : Ensures (do let choice ← leafParentDecision n.parent; leafAfterDecision id n choice)
      (fun w => w.k.wg = some linked)
      (fun result w => result = .yield () ∧ ∃ final, w.k.wg = some final ∧ NodeRemoval d id n final) := by
    refine ensures_bind _ _ (leafParentDecision_effect linked n.parent) ?_
    intro collapse w result final pre run
    obtain ⟨device, choice⟩ := pre
    cases collapse with
    | false =>
      obtain ⟨value, ⟨remaining, resident⟩, output⟩ :=
        leafAfterDecision_false_effect linked id n w result final device run
      exact ⟨value, _, output, .leaf linked shape write choice remaining resident⟩
    | true => exact leafCollapse_node_effect d linked id n lp shape write choice w result final device run
  exact suffix w result final device run

/-- Shape chooses the existing structural cases; every other readiness fact
comes from the actual successive reads of a normally returning original body. -/
theorem removeNodeSource_effect_pairs (d : Device) (id : NodeId) (n : AipNode)
    (pairs : NodePairs d) (shape : n.bit.size = 2) :
    Ensures (removeNodeSource id n) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ ∃ final, w.k.wg = some final ∧ NodeRemoval d id n final) := by
  obtain ⟨left, right, bits⟩ := array_pair_shape n.bit shape
  cases left with
  | none =>
    cases right with
    | none => exact removeNodeSource_leaf_effect d id n pairs bits
    | some child => exact removeNodeSource_unary_effect d id n child false pairs bits
  | some left =>
    cases right with
    | none => exact removeNodeSource_unary_effect d id n left true pairs bits
    | some right =>
      intro w result final pre run
      obtain ⟨value, output⟩ := removal_returns_ensures
        (removeNodeSource_branching d id n left right bits) w result final pre run
      exact ⟨value, _, output, .branching left right bits⟩

theorem removeEntry_effect_pairs (d : Device) (id : NodeId) (pairs : NodePairs d) :
    Ensures (removeEntry id) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ ∃ n next,
        (deleteListedNodes id d d.peers.toList).nodes[id]? = some n ∧
        NodeRemoval (deleteListedNodes id d d.peers.toList) id n next ∧ w.k.wg = some next) := by
  let unlisted := deleteListedNodes id d d.peers.toList
  have up : NodePairs unlisted := deleteListedNodes_nodePairs id d pairs
  have hl := (returns_iff _ _ _).mp (listDel_returns id d)
  have hn := fun n shape => (ensures_iff _ _ _).mp (removeNodeSource_effect_pairs unlisted id n up shape)
  rw [ensures_iff]
  mvcgen [removeEntry, branch, getNode, getDev, getK, invariant, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all only [Option.some.injEq]
  all_goals subst_vars
  all_goals rename_i n hdevice resident
  all_goals have shape := up id n resident
  all_goals have spec := hn n shape
  all_goals mvcgen [spec]
  all_goals try dsimp +zetaDelta only at *
  all_goals grind

theorem removeEntries_effect_pairs (d : Device) (ids : List NodeId) (pairs : NodePairs d) :
    Ensures (removeEntries ids) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ RemovalRun d ids final) := by
  induction ids generalizing d with
  | nil =>
    intro w result final pre run
    change Except.ok ((), w) = .ok (result, final) at run
    cases run
    exact ⟨d, pre, .nil d⟩
  | cons id rest ih =>
    rw [removeEntries_cons]
    refine ensures_bind _ _ (removeEntry_effect_pairs d id pairs) ?_
    intro result w u final pre run
    obtain ⟨rfl, n, next, read, step, device⟩ := pre
    obtain ⟨output, actual, tail⟩ := ih next
      (nodeRemoval_nodePairs step (deleteListedNodes_nodePairs id d pairs)) w u final device run
    exact ⟨output, actual, .cons d id rest n next output read step tail⟩

theorem removeByPeerSource_effect_pairs (d : Device) (p : Peer) (pairs : NodePairs d) :
    Ensures (removeByPeerSource p) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ RemovalEffect d p.allowedipsList final) := by
  rw [removeByPeerSource_entries]
  cases ids : p.allowedipsList with
  | nil =>
    rw [ensures_iff]
    simp only [ids]
    mvcgen [branch]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [RemovalEffect]
  | cons id rest =>
    have hr := (ensures_iff _ _ _).mp (removeEntries_effect_pairs (bumpAllowedips d) (id :: rest) pairs)
    rw [ensures_iff]
    simp only [ids]
    mvcgen [branch, modifyDev, modifyK, hr]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [RemovalEffect, bumpAllowedips]

theorem removeByPeer_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Ensures (removeByPeer pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ RemovalEffect d p.allowedipsList final) := by
  have hr := (ensures_iff _ _ _).mp (removeByPeerSource_effect_pairs d p pairs)
  rw [removeByPeer_source, ensures_iff]
  mvcgen [getPeer, getDev, getK, invariant, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals subst_vars
  all_goals mvcgen [hr]

theorem peerMakeDead_removal_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Ensures (peerMakeDead pid) (fun w => w.k.wg = some d)
      (fun _ _ => ∃ removed, RemovalEffect (unlistPeer d pid) p.allowedipsList removed) := by
  have hu : Ensures (modifyDev (unlistPeer · pid)) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (unlistPeer d pid)) := by
    rw [ensures_iff]
    mvcgen [modifyDev, modifyK]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
  rw [peerMakeDead_source]
  refine ensures_bind _ _ hu ?_
  intro u
  refine ensures_bind _ _ (removeByPeer_effect_pairs pid (unlistPeer d pid) p resident pairs) ?_
  intro u w result final pre run
  obtain ⟨removed, device, steps⟩ := pre
  exact ⟨removed, steps⟩

/-- Recover the witness from the actual successful prefix, then identify the
same original run using the established exact witness-based execution theorem. -/
theorem peerMakeDead_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Ensures (peerMakeDead pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ removed, RemovalEffect (unlistPeer d pid) p.allowedipsList removed ∧
        w.k.wg = some (deadPeerDevice removed pid p)) := by
  intro w result final pre run
  obtain ⟨removed, steps⟩ := peerMakeDead_removal_effect_pairs pid d p resident pairs w result final pre run
  have output := removal_returns_ensures (peerMakeDead_returns pid p d removed resident steps)
    w result final pre run
  exact ⟨removed, steps, output⟩

end Leanux.Proofs.WG.Config
