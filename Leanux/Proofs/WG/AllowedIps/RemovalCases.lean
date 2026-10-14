import Leanux.Proofs.WG.AllowedIps.RemovalTransport

/-! Represented source cases. The endpoint is the original source mutation,
including listDel. Context transport then identifies its pure eraseId tree. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.Proofs.Framing

structure RemovedTree (d out : WG.Device) (v4 : Bool) (t : Tree) (id : Nat) : Prop where
  root : rootValue out v4 = (t.eraseId id).root
  rep : RepAt out.nodes (rootWidth v4) (rootSlot v4) (t.eraseId id)
  metadata : RemovalMetadata d out id
  otherRoot : rootValue out (!v4) = rootValue d (!v4)
  outside : RemovalOutside d out t
  retired : ∀ q ∈ t.nodeIds, q ∉ (t.eraseId id).nodeIds → out.nodes[q]? = none
  frame : out = { d with nodes := out.nodes, peers := out.peers, peerAllowedips := out.peerAllowedips }

theorem removedTree_context (d out : WG.Device) (v4 : Bool) (id : Nat)
    (c : Context) (before after : Tree)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug before))
    (hn : (c.plug before).nodeIds.Nodup)
    (he : (c.plug before).eraseId id = c.plug after)
    (hl : RepAt out.nodes (rootWidth v4) (c.slot (rootSlot v4)) after)
    (hs : c = .here ∨ after.root = before.root)
    (hf : RemovalOutside d out before)
    (hroot : rootValue out v4 = (c.plug after).root)
    (hm : RemovalMetadata d out id)
    (ho : rootValue out (!v4) = rootValue d (!v4))
    (hret : ∀ q ∈ before.nodeIds, q ∉ after.nodeIds → out.nodes[q]? = none)
    (hframe : out = { d with nodes := out.nodes, peers := out.peers, peerAllowedips := out.peerAllowedips }) :
    RemovedTree d out v4 (c.plug before) id := by
  refine ⟨he ▸ hroot, ?_, hm, ho, ?_, ?_, hframe⟩
  · rw [he]
    rcases hs with rfl | hs
    · exact hl
    · apply c.rep_replace_sameRoot before after _ hr hl hs
      intro q hq
      exact hf q (fun hi => c.focus_disjoint before hn q hi hq)
  · intro q hq
    exact hf q (fun hi => hq ((c.mem_plug_nodeIds before q).mpr (.inr hi)))
  · intro q hq hgone
    rw [he] at hgone
    rcases (c.mem_plug_nodeIds before q).mp hq with hctx | hlocal
    · exact False.elim (hgone ((c.mem_plug_nodeIds after q).mpr (.inl hctx)))
    · exact hret q hlocal (fun h => hgone ((c.mem_plug_nodeIds after q).mpr (.inr h)))

theorem case_remove_binary (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (c : Context) (n a b : NodeData) (al ar bl br : Tree)
    (hroot : rootValue d v4 = (c.plug (.node n (.node a al ar) (.node b bl br))).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4)
      (c.plug (.node n (.node a al ar) (.node b bl br))))
    (hn : (c.plug (.node n (.node a al ar) (.node b bl br))).nodeIds.Nodup)
    (hc : (c.plug (.node n (.node a al ar) (.node b bl br))).Compressed) :
    let old := encode (rootWidth v4) (c.slot (rootSlot v4)) n (.node a al ar) (.node b bl br)
    let out := removalCleared (unlisted d n.id) n.id old
    ∃ w', (removeStep n.id).run w = .ok (.yield (), w') ∧
      w'.k = { w.k with wg := some out } ∧
      RemovedTree d out v4 (c.plug (.node n (.node a al ar) (.node b bl br))) n.id := by
  dsimp only
  have hfocus := c.focus_rep _ _ hr
  obtain ⟨result, w', hrun, rfl, hk⟩ := (total_iff_run _ _ _).mp
    (removeStep_binary_wp w.k d hd n.id a.id b.id _ hfocus.1 rfl) w rfl
  refine ⟨w', hrun, hk, ?_⟩
  apply removedTree_context d _ v4 n.id c _ (.node {n with peer := none} (.node a al ar) (.node b bl br)) hr hn
  · simpa [Tree.compact] using c.eraseId_nonleaf n (.node a al ar) (.node b bl br) hc hn (.inl rfl)
  · exact removalCleared_rep (unlisted d n.id) _ _ n _ _ hfocus (c.focus_nodup _ hn)
  · exact .inr rfl
  · intro q hq
    have hne : n.id ≠ q := fun he => hq (by simp [Tree.nodeIds, he])
    simp [removalCleared_node, hne, unlisted]
  · exact hroot.trans (c.root_congr (before := .node n (.node a al ar) (.node b bl br))
      (after := .node {n with peer := none} (.node a al ar) (.node b bl br)) rfl).symm
  · exact ⟨rfl, rfl, unlisted_get d n.id⟩
  · rfl
  · intro q hq hgone; exact False.elim (hgone hq)
  · rfl

theorem case_remove_root_leaf (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (n : NodeData)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n .empty .empty)) :
    let old := encode (rootWidth v4) (rootSlot v4) n .empty .empty
    let out := removalRootLeaf (unlisted d n.id) v4 n.id old
    ∃ w', (removeStep n.id).run w = .ok (.yield (), w') ∧
      w'.k = { w.k with wg := some out } ∧ RemovedTree d out v4 (.node n .empty .empty) n.id := by
  dsimp only
  obtain ⟨result, w', hrun, rfl, hk⟩ := (total_iff_run _ _ _).mp
    (removeStep_root_leaf_wp w.k d hd v4 n.id _ hr.1 rfl rfl) w rfl
  have hm := removalRootLeaf_metadata d v4 n.id (encode (rootWidth v4) (rootSlot v4) n .empty .empty)
  refine ⟨w', hrun, hk, ⟨?_, ?_, ⟨hm.1, hm.2.2.2.1, hm.2.2.2.2⟩, hm.2.2.1, ?_, ?_, ?_⟩⟩
  · simpa [Tree.root] using hm.2.1
  · rw [Tree.eraseId_leaf]; trivial
  · intro q hq
    have hne : n.id ≠ q := fun he => hq (by simp [Tree.nodeIds, he])
    simp [removalRootLeaf_node, hne, unlisted]
  · intro q hq _
    have he : q = n.id := by simpa [Tree.nodeIds] using hq
    subst q; simp [removalRootLeaf_node]
  · cases v4 <;> rfl

theorem case_remove_root_unary (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 left : Bool) (n a : NodeData) (l r : Tree)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4)
      (if left then .node n (.node a l r) .empty else .node n .empty (.node a l r)))
    (hn : (if left then Tree.node n (.node a l r) .empty else .node n .empty (.node a l r)).nodeIds.Nodup)
    (hc : (if left then Tree.node n (.node a l r) .empty else .node n .empty (.node a l r)).Compressed) :
    let t := Tree.node a l r
    let old := encode (rootWidth v4) (rootSlot v4) n (if left then t else .empty) (if left then .empty else t)
    let child := encode (rootWidth v4) (.child n.id (if left then 0 else 1)) a l r
    let out := removalRootUnary (unlisted d n.id) v4 n.id old a.id child
    ∃ w', (removeStep n.id).run w = .ok (.yield (), w') ∧
      w'.k = { w.k with wg := some out } ∧
      RemovedTree d out v4 (if left then .node n t .empty else .node n .empty t) n.id := by
  dsimp only
  have hne : n.id ≠ a.id := by
    cases left <;> simp only [Bool.false_eq_true, ↓reduceIte, Tree.nodeIds, List.append_nil, List.nil_append] at hn
    all_goals exact fun he => (List.nodup_cons.mp hn).1 (by simp [he])
  have ht : d.nodes[n.id]? = some (encode (rootWidth v4) (rootSlot v4) n
      (if left then .node a l r else .empty) (if left then .empty else .node a l r)) := by
    cases left <;> exact hr.1
  have ha : d.nodes[a.id]? = some (encode (rootWidth v4) (.child n.id (if left then 0 else 1)) a l r) := by
    cases left
    · exact hr.2.2.1
    · exact hr.2.1.1
  have he : (if left then Tree.node n (.node a l r) .empty else .node n .empty (.node a l r)).eraseId n.id = .node a l r := by
    cases left
    · exact Tree.eraseId_unary_right hc hn
    · exact Tree.eraseId_unary_left hc hn
  obtain ⟨result, w', hrun, rfl, hk⟩ := (total_iff_run _ _ _).mp
    (removeStep_root_unary_wp w.k d hd v4 left n.id a.id _ _ ht ha hne (by cases left <;> rfl) rfl) w rfl
  have hm := removalRootUnary_metadata d v4 n.id
    (encode (rootWidth v4) (rootSlot v4) n (if left then .node a l r else .empty)
      (if left then .empty else .node a l r)) a.id
    (encode (rootWidth v4) (.child n.id (if left then 0 else 1)) a l r)
  refine ⟨w', hrun, hk, ⟨?_, ?_, ⟨hm.1, hm.2.2.2.1, hm.2.2.2.2⟩, hm.2.2.1, ?_, ?_, ?_⟩⟩
  · rw [he]; exact hm.2.1
  · rw [he]; exact removalRootUnary_rep (unlisted d n.id) v4 n a l r left hr hn
  · intro q hq
    have hneq : n.id ≠ q := by
      intro heq; apply hq; cases left <;> simp [Tree.nodeIds, heq]
    have haq : a.id ≠ q := by
      intro heq; apply hq; cases left <;> simp [Tree.nodeIds, heq]
    simp [removalRootUnary_node, hneq, haq, unlisted]
  · intro q hq hgone
    rw [he] at hgone
    have hqn : q = n.id := by
      cases left <;> simp only [Bool.false_eq_true, ↓reduceIte, Tree.nodeIds,
        List.nil_append, List.append_nil, List.mem_cons] at hq hgone <;> grind only
    subst q; simp [removalRootUnary_node]
  · cases v4 <;> rfl

theorem case_remove_child_unary (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (outer : Context) (p n a : NodeData) (side childSide : Nat) (l r sibling : Tree)
    (hb : side < 2) (hab : childSide < 2)
    (hroot : rootValue d v4 = (outer.plug
      (Tree.fork p side (Tree.fork n childSide (.node a l r) .empty) sibling)).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (outer.plug
      (Tree.fork p side (Tree.fork n childSide (.node a l r) .empty) sibling)))
    (hn : (outer.plug (Tree.fork p side (Tree.fork n childSide (.node a l r) .empty) sibling)).nodeIds.Nodup)
    (hc : (outer.plug (Tree.fork p side (Tree.fork n childSide (.node a l r) .empty) sibling)).Compressed) :
    let target := Tree.fork n childSide (.node a l r) .empty
    let old := forkNode (rootWidth v4) (.child p.id side) n childSide (.node a l r) .empty
    let parent := forkNode (rootWidth v4) (outer.slot (rootSlot v4)) p side target sibling
    let child := encode (rootWidth v4) (.child n.id childSide) a l r
    let out := removalChildUnary (unlisted d n.id) n.id old p.id side parent a.id child
    ∃ w', (removeStep n.id).run w = .ok (.yield (), w') ∧
      w'.k = { w.k with wg := some out } ∧
      RemovedTree d out v4 (outer.plug (Tree.fork p side target sibling)) n.id := by
  dsimp only
  have hfocus := outer.focus_rep _ _ hr
  have hnf := outer.focus_nodup _ hn
  obtain ⟨hp, ht, hs⟩ := fork_rep_parts hb hfocus
  obtain ⟨htn, ha, _⟩ := fork_rep_parts hab ht
  obtain ⟨hpt, hps, hnt, _, hts⟩ := (Tree.fork_nodup_iff ..).mp hnf
  obtain ⟨hna, _, _, _, _⟩ := (Tree.fork_nodup_iff ..).mp hnt
  have hnp : n.id ≠ p.id := fun he => hpt (by simp [Tree.mem_fork_nodeIds, he])
  have hna' : n.id ≠ a.id := fun he => hna (by simp [Tree.nodeIds, he])
  have hap : a.id ≠ p.id := fun he => hpt (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
  have bits : (forkNode (rootWidth v4) (.child p.id side) n childSide (.node a l r) .empty).bit =
      if decide (childSide = 0) then #[some a.id, none] else #[none, some a.id] := by
    by_cases he : childSide = 0 <;> simp [forkNode, he, encode, Tree.root]
  obtain ⟨result, w', hrun, rfl, hk⟩ := (total_iff_run _ _ _).mp
    (removeStep_child_unary_wp w.k d hd (decide (childSide = 0)) n.id p.id side a.id _ _ _
      htn hp ha.1 hnp hna' hap (by omega) bits (forkNode_parent)) w rfl
  refine ⟨w', hrun, hk, ?_⟩
  let old := forkNode (rootWidth v4) (.child p.id side) n childSide (.node a l r) .empty
  let parent := forkNode (rootWidth v4) (outer.slot (rootSlot v4)) p side
    (Tree.fork n childSide (.node a l r) .empty) sibling
  let child := encode (rootWidth v4) (.child n.id childSide) a l r
  have hm := removalChildUnary_metadata d n.id old p.id side parent a.id child
  apply removedTree_context d _ v4 n.id outer _ (Tree.fork p side (.node a l r) sibling) hr hn
  · have he := (outer.append (gapContext p side sibling)).eraseId_unary n a childSide l r
      (by simpa [gapContext_plug] using hc) (by simpa [gapContext_plug] using hn)
    simpa [gapContext_plug] using he
  · exact removalChildUnary_rep (unlisted d n.id) _ _ p n a side childSide l r sibling hb hab hfocus hnf
  · exact .inr ((Tree.fork_root ..).trans (Tree.fork_root ..).symm)
  · intro q hq
    have hnq : n.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, he])
    have hpq : p.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, he])
    have haq : a.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
    simp [removalChildUnary_node, hnq, hpq, haq, unlisted]
  · exact (hm.2 v4).trans (hroot.trans (outer.root_congr
      (before := Tree.fork p side (Tree.fork n childSide (.node a l r) .empty) sibling)
      (after := Tree.fork p side (.node a l r) sibling) (by simp)).symm)
  · exact hm.1
  · exact hm.2 _
  · intro q hq hgone
    have hqn : q = n.id := by
      simp only [Tree.mem_fork_nodeIds, Tree.nodeIds, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false] at hq hgone
      grind only
    subst q; simp [removalChildUnary_node]
  · rfl

theorem case_remove_child_leaf_owned (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (outer : Context) (p n : NodeData) (side : Nat) (sibling : Tree)
    (hb : side < 2) (hpowner : p.peer.isSome)
    (hroot : rootValue d v4 = (outer.plug (Tree.fork p side (.node n .empty .empty) sibling)).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4)
      (outer.plug (Tree.fork p side (.node n .empty .empty) sibling)))
    (hn : (outer.plug (Tree.fork p side (.node n .empty .empty) sibling)).nodeIds.Nodup)
    (hc : (outer.plug (Tree.fork p side (.node n .empty .empty) sibling)).Compressed) :
    let old := encode (rootWidth v4) (.child p.id side) n .empty .empty
    let parent := forkNode (rootWidth v4) (outer.slot (rootSlot v4)) p side (.node n .empty .empty) sibling
    let out := removalLeafDetached (unlisted d n.id) n.id old p.id side parent
    ∃ w', (removeStep n.id).run w = .ok (.yield (), w') ∧
      w'.k = { w.k with wg := some out } ∧
      RemovedTree d out v4 (outer.plug (Tree.fork p side (.node n .empty .empty) sibling)) n.id := by
  dsimp only
  have hfocus := outer.focus_rep _ _ hr
  have hnf := outer.focus_nodup _ hn
  obtain ⟨hp, ht, hs⟩ := fork_rep_parts hb hfocus
  have hpt := ((Tree.fork_nodup_iff ..).mp hnf).1
  have hnp : n.id ≠ p.id := fun he => hpt (by simp [Tree.nodeIds, he])
  obtain ⟨result, w', hrun, rfl, hk⟩ := (total_iff_run _ _ _).mp
    (removeStep_child_leaf_owned_wp w.k d hd n.id p.id side _ _ ht.1 hp hnp (by omega)
      (by simpa using hpowner) rfl rfl) w rfl
  refine ⟨w', hrun, hk, ?_⟩
  let old := encode (rootWidth v4) (.child p.id side) n .empty .empty
  let parent := forkNode (rootWidth v4) (outer.slot (rootSlot v4)) p side (.node n .empty .empty) sibling
  have hm := removalLeafDetached_metadata d n.id old p.id side parent
  apply removedTree_context d _ v4 n.id outer _ (Tree.fork p side .empty sibling) hr hn
  · have hne : p.peer ≠ none := by intro he; simp [he] at hpowner
    simpa [hne] using outer.eraseId_leaf_parent p n side sibling hc hn
  · exact removalLeafDetached_rep (unlisted d n.id) _ _ p n side sibling hb hfocus hnf
  · exact .inr (by simp)
  · intro q hq
    have hnq : n.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
    have hpq : p.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, he])
    simp [removalLeafDetached_node, hnq, hpq, unlisted]
  · exact (hm.2 v4).trans (hroot.trans (outer.root_congr
      (before := Tree.fork p side (.node n .empty .empty) sibling)
      (after := Tree.fork p side .empty sibling) (by simp)).symm)
  · exact hm.1
  · exact hm.2 _
  · intro q hq hgone
    have hqn : q = n.id := by
      simp only [Tree.mem_fork_nodeIds, Tree.nodeIds, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false, false_or] at hq hgone
      grind only
    subst q; simp [removalLeafDetached_node]
  · rfl

theorem case_remove_collapse_root (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (p n a : NodeData) (side : Nat) (l r : Tree)
    (hb : side < 2) (hpowner : p.peer = none)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4)
      (Tree.fork p side (.node n .empty .empty) (.node a l r)))
    (hn : (Tree.fork p side (.node n .empty .empty) (.node a l r)).nodeIds.Nodup)
    (hc : (Tree.fork p side (.node n .empty .empty) (.node a l r)).Compressed) :
    let old := encode (rootWidth v4) (.child p.id side) n .empty .empty
    let parent := forkNode (rootWidth v4) (rootSlot v4) p side (.node n .empty .empty) (.node a l r)
    let sibling := some (a.id, encode (rootWidth v4) (.child p.id (1-side)) a l r)
    let out := removalCollapseRoot (unlisted d n.id) n.id old p.id side parent v4 sibling
    ∃ w', (removeStep n.id).run w = .ok (.yield (), w') ∧
      w'.k = { w.k with wg := some out } ∧
      RemovedTree d out v4 (Tree.fork p side (.node n .empty .empty) (.node a l r)) n.id := by
  dsimp only
  obtain ⟨hp, ht, hs⟩ := fork_rep_parts hb hr
  obtain ⟨hpt, hps, _, _, hts⟩ := (Tree.fork_nodup_iff ..).mp hn
  have hnp : n.id ≠ p.id := fun he => hpt (by simp [Tree.nodeIds, he])
  have hap : a.id ≠ p.id := fun he => hps (by simp [Tree.nodeIds, he])
  have han : a.id ≠ n.id := fun he => hts n.id (by simp [Tree.nodeIds]) (by simp [Tree.nodeIds, ← he])
  obtain ⟨result, w', hrun, rfl, hk⟩ := (total_iff_run _ _ _).mp
    (removeStep_leaf_collapse_root_wp w.k d hd n.id p.id side _ _ ht.1 hp hnp (by omega)
      (by simpa using hpowner) rfl rfl v4 forkNode_parent
      (some (a.id, encode (rootWidth v4) (.child p.id (1-side)) a l r))
      (forkNode_other hb) (by
        intro q qn he
        cases he
        exact ⟨hs.1, han, hap⟩)) w rfl
  let old := encode (rootWidth v4) (.child p.id side) n .empty .empty
  let parent := forkNode (rootWidth v4) (rootSlot v4) p side (.node n .empty .empty) (.node a l r)
  let sibling := some (a.id, encode (rootWidth v4) (.child p.id (1-side)) a l r)
  have hm := removalCollapseRoot_metadata d n.id old p.id side parent v4 sibling
  have he : (Tree.fork p side (.node n .empty .empty) (.node a l r)).eraseId n.id = .node a l r := by
    simpa [hpowner] using Tree.eraseId_leaf_parent hc hn
  refine ⟨w', hrun, hk, ⟨?_, ?_, hm.1, hm.2.2, ?_, ?_, ?_⟩⟩
  · rw [he]; exact hm.2.1
  · rw [he]; exact removalCollapseRoot_rep (unlisted d n.id) v4 p n a side l r hb hr hn
  · intro q hq
    have hnq : n.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
    have hpq : p.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, he])
    have haq : a.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
    simp [removalCollapseRoot_node, hnq, hpq, haq, unlisted]
  · intro q hq hgone
    rw [he] at hgone
    have hqn : q = p.id ∨ q = n.id := by
      simp only [Tree.mem_fork_nodeIds, Tree.nodeIds, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false, false_or] at hq hgone
      grind only
    rcases hqn with rfl | rfl
    · simp [removalCollapseRoot_node]
    · simp [removalCollapseRoot_node, Ne.symm hnp, han]
  · exact removalCollapseRoot_frame d n.id old p.id side parent v4 sibling

theorem case_remove_collapse_child (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (outer : Context) (g p n a : NodeData) (gside side : Nat)
    (l r outerSibling : Tree) (hgb : gside < 2) (hb : side < 2) (hpowner : p.peer = none)
    (hroot : rootValue d v4 = (outer.plug (Tree.fork g gside
      (Tree.fork p side (.node n .empty .empty) (.node a l r)) outerSibling)).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (outer.plug (Tree.fork g gside
      (Tree.fork p side (.node n .empty .empty) (.node a l r)) outerSibling)))
    (hn : (outer.plug (Tree.fork g gside
      (Tree.fork p side (.node n .empty .empty) (.node a l r)) outerSibling)).nodeIds.Nodup)
    (hc : (outer.plug (Tree.fork g gside
      (Tree.fork p side (.node n .empty .empty) (.node a l r)) outerSibling)).Compressed) :
    let target := Tree.fork p side (.node n .empty .empty) (.node a l r)
    let old := encode (rootWidth v4) (.child p.id side) n .empty .empty
    let parent := forkNode (rootWidth v4) (.child g.id gside) p side (.node n .empty .empty) (.node a l r)
    let grand := forkNode (rootWidth v4) (outer.slot (rootSlot v4)) g gside target outerSibling
    let sibling := some (a.id, encode (rootWidth v4) (.child p.id (1-side)) a l r)
    let out := removalCollapseChild (unlisted d n.id) n.id old p.id side parent g.id gside grand sibling
    ∃ w', (removeStep n.id).run w = .ok (.yield (), w') ∧
      w'.k = { w.k with wg := some out } ∧
      RemovedTree d out v4 (outer.plug (Tree.fork g gside target outerSibling)) n.id := by
  dsimp only
  have hfocus := outer.focus_rep _ _ hr
  have hnf := outer.focus_nodup _ hn
  obtain ⟨hg, hpr, hos⟩ := fork_rep_parts hgb hfocus
  obtain ⟨hp, ht, hs⟩ := fork_rep_parts hb hpr
  obtain ⟨hgp, _, hpdup, _, _⟩ := (Tree.fork_nodup_iff ..).mp hnf
  obtain ⟨hpt, hps, _, _, hts⟩ := (Tree.fork_nodup_iff ..).mp hpdup
  have hnp : n.id ≠ p.id := fun he => hpt (by simp [Tree.nodeIds, he])
  have hng : n.id ≠ g.id := fun he => hgp (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
  have hpg : p.id ≠ g.id := fun he => hgp (by simp [Tree.mem_fork_nodeIds, he])
  have hap : a.id ≠ p.id := fun he => hps (by simp [Tree.nodeIds, he])
  have han : a.id ≠ n.id := fun he => hts n.id (by simp [Tree.nodeIds]) (by simp [Tree.nodeIds, ← he])
  have hag : a.id ≠ g.id := fun he => hgp (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
  obtain ⟨result, w', hrun, rfl, hk⟩ := (total_iff_run _ _ _).mp
    (removeStep_leaf_collapse_child_wp w.k d hd n.id p.id side g.id gside _ _ _ ht.1 hp hg
      hnp hng hpg (by omega) (by omega) (by simpa using hpowner) rfl rfl forkNode_parent
      (some (a.id, encode (rootWidth v4) (.child p.id (1-side)) a l r))
      (forkNode_other hb) (by
        intro q qn he
        cases he
        exact ⟨hs.1, han, hap, hag⟩)) w rfl
  let old := encode (rootWidth v4) (.child p.id side) n .empty .empty
  let parent := forkNode (rootWidth v4) (.child g.id gside) p side (.node n .empty .empty) (.node a l r)
  let grand := forkNode (rootWidth v4) (outer.slot (rootSlot v4)) g gside
    (Tree.fork p side (.node n .empty .empty) (.node a l r)) outerSibling
  let sibling := some (a.id, encode (rootWidth v4) (.child p.id (1-side)) a l r)
  have hm := removalCollapseChild_metadata d n.id old p.id side parent g.id gside grand sibling
  refine ⟨w', hrun, hk, ?_⟩
  apply removedTree_context d _ v4 n.id outer _ (Tree.fork g gside (.node a l r) outerSibling) hr hn
  · have he := (outer.append (gapContext g gside outerSibling)).eraseId_leaf_parent p n side (.node a l r)
      (by simpa [gapContext_plug] using hc) (by simpa [gapContext_plug] using hn)
    simpa [gapContext_plug, hpowner] using he
  · exact removalCollapseChild_rep (unlisted d n.id) _ _ g p n a gside side l r outerSibling hgb hb hfocus hnf
  · exact .inr (by simp)
  · intro q hq
    have hnq : n.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
    have hpq : p.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, he])
    have hgq : g.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, he])
    have haq : a.id ≠ q := fun he => hq (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds, he])
    simp [removalCollapseChild_node, hnq, hpq, hgq, haq, unlisted]
  · exact (hm.2 v4).trans (hroot.trans (outer.root_congr
      (before := Tree.fork g gside (Tree.fork p side (.node n .empty .empty) (.node a l r)) outerSibling)
      (after := Tree.fork g gside (.node a l r) outerSibling) (by simp)).symm)
  · exact hm.1
  · exact hm.2 _
  · intro q hq hgone
    have hqn : q = p.id ∨ q = n.id := by
      simp only [Tree.mem_fork_nodeIds, Tree.nodeIds, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false, false_or] at hq hgone
      grind only
    rcases hqn with rfl | rfl
    · simp [removalCollapseChild_node]
    · simp [removalCollapseChild_node, Ne.symm hnp, Ne.symm hng, han]
  · rfl

end Leanux.Proofs.WG.AllowedIps
