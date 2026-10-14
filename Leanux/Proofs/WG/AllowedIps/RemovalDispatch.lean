import Leanux.Proofs.WG.AllowedIps.RemovalCases

/-! Total target-removal dispatch from an actual represented-tree member.
The source step is the factor of original removeByPeer; neither an absent
target no-op nor saved-list coherence is assumed or concluded here. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

def RemovalRun (w : World) (d : WG.Device) (v4 : Bool) (t : Tree) (id : Nat) : Prop :=
  ∃ out w', (removeStep id).run w = .ok (.yield (), w') ∧
    w'.k = {w.k with wg := some out} ∧ RemovedTree d out v4 t id

theorem remove_unary_total (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (c : Context) (n a : NodeData) (side : Nat) (l r : Tree) (hb : side < 2)
    (hroot : rootValue d v4 = (c.plug (Tree.fork n side (.node a l r) .empty)).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork n side (.node a l r) .empty)))
    (hn : (c.plug (Tree.fork n side (.node a l r) .empty)).nodeIds.Nodup)
    (hc : (c.plug (Tree.fork n side (.node a l r) .empty)).Compressed) :
    RemovalRun w d v4 (c.plug (Tree.fork n side (.node a l r) .empty)) n.id := by
  by_cases he : c = .here
  · subst c
    have hs : side = 0 ∨ side = 1 := by omega
    rcases hs with rfl | rfl
    · obtain ⟨w', he, hk, ht⟩ := case_remove_root_unary w d hd v4 true n a l r hr hn hc
      exact ⟨_, w', he, hk, ht⟩
    · obtain ⟨w', he, hk, ht⟩ := case_remove_root_unary w d hd v4 false n a l r hr hn hc
      exact ⟨_, w', he, hk, ht⟩
  · obtain ⟨outer, p, ps, sibling, hps, rfl⟩ := c.last_gap_shape he
    simp only [Context.plug_append, gapContext_plug] at *
    obtain ⟨w', he, hk, ht⟩ := case_remove_child_unary w d hd v4 outer p n a ps side l r sibling
      hps hb hroot hr hn hc
    exact ⟨_, w', he, hk, ht⟩

theorem remove_leaf_total (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (c : Context) (n : NodeData)
    (hroot : rootValue d v4 = (c.plug (.node n .empty .empty)).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (.node n .empty .empty)))
    (hn : (c.plug (.node n .empty .empty)).nodeIds.Nodup)
    (hc : (c.plug (.node n .empty .empty)).Compressed) :
    RemovalRun w d v4 (c.plug (.node n .empty .empty)) n.id := by
  by_cases he : c = .here
  · subst c
    obtain ⟨w', he, hk, ht⟩ := case_remove_root_leaf w d hd v4 n hr
    exact ⟨_, w', he, hk, ht⟩
  · obtain ⟨outer, p, side, sibling, hb, rfl⟩ := c.last_gap_shape he
    simp only [Context.plug_append, gapContext_plug] at *
    cases hpowner : p.peer with
    | some pid =>
      obtain ⟨w', he, hk, ht⟩ := case_remove_child_leaf_owned w d hd v4 outer p n side sibling
        hb (by simp [hpowner]) hroot hr hn hc
      exact ⟨_, w', he, hk, ht⟩
    | none =>
      have hs := (Tree.fork_compressed_parts (outer.focus_compressed _ hc)).2.2 hpowner
      cases sibling with
      | empty => simp [Tree.root] at hs
      | node a l r =>
        by_cases ho : outer = .here
        · subst outer
          obtain ⟨w', he, hk, ht⟩ := case_remove_collapse_root w d hd v4 p n a side l r hb hpowner hr hn hc
          exact ⟨_, w', he, hk, ht⟩
        · obtain ⟨top, g, gs, other, hgb, rfl⟩ := outer.last_gap_shape ho
          simp only [Context.plug_append, gapContext_plug] at *
          obtain ⟨w', he, hk, ht⟩ := case_remove_collapse_child w d hd v4 top g p n a gs side l r other
            hgb hb hpowner hroot hr hn hc
          exact ⟨_, w', he, hk, ht⟩

/-- Every represented member selects exactly one of the seven local shapes.
Validity of prefix bits is unnecessary for source totality; compression and
distinct node IDs supply the shape and alias obligations. -/
theorem remove_selected_total (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (t : Tree) (id : Nat)
    (hroot : rootValue d v4 = t.root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (hn : t.nodeIds.Nodup) (hc : t.Compressed) (hi : id ∈ t.nodeIds) :
    RemovalRun w d v4 t id := by
  obtain ⟨c, n, l, r, rfl, rfl⟩ := Tree.focus_of_mem hi
  cases l with
  | empty =>
    cases r with
    | empty => exact remove_leaf_total w d hd v4 c n hroot hr hn hc
    | node a al ar => exact remove_unary_total w d hd v4 c n a 1 al ar (by omega) hroot hr hn hc
  | node a al ar =>
    cases r with
    | empty => exact remove_unary_total w d hd v4 c n a 0 al ar (by omega) hroot hr hn hc
    | node b bl br =>
      obtain ⟨w', he, hk, ht⟩ := case_remove_binary w d hd v4 c n a b al ar bl br hroot hr hn hc
      exact ⟨_, w', he, hk, ht⟩

theorem RemovedTree.below {id : Nat} (h : RemovedTree d out v4 t id)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t) (hb : NodesBelow d) :
    NodesBelow out := h.outside.below hr h.metadata.1 hb

theorem RemovedTree.other_rep {id : Nat} (h : RemovedTree d out v4 t id)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) :
    RepAt out.nodes (rootWidth (!v4)) (rootSlot (!v4)) other :=
  h.outside.other hr ho (by cases v4 <;> simp [rootWidth])

/-- The full Kernel endpoint changes only the device's node store, peer
lists and allowed-IP roots. Both families represent pure erasure; all other
resident nodes and all other device and Kernel fields are framed. -/
structure RemovedForest (d out : WG.Device) (t4 t6 : Tree) (id : Nat) : Prop where
  forest : ForestRep out (t4.eraseId id) (t6.eraseId id)
  metadata : RemovalMetadata d out id
  outside : ∀ q, q ∉ t4.nodeIds ++ t6.nodeIds → out.nodes[q]? = d.nodes[q]?
  retired : ∀ q ∈ t4.nodeIds ++ t6.nodeIds,
    q ∉ (t4.eraseId id).nodeIds ++ (t6.eraseId id).nodeIds → out.nodes[q]? = none
  frame : out = {d with nodes := out.nodes, peers := out.peers, peerAllowedips := out.peerAllowedips}
  below : NodesBelow d → NodesBelow out

theorem remove_forest_total (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (t4 t6 : Tree) (id : Nat) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed)
    (hi : id ∈ t4.nodeIds ++ t6.nodeIds) :
    ∃ out w', (removeStep id).run w = .ok (.yield (), w') ∧
      w'.k = {w.k with wg := some out} ∧ RemovedForest d out t4 t6 id := by
  rcases List.mem_append.mp hi with hi4 | hi6
  · obtain ⟨out, w', hrun, hk, hr⟩ := remove_selected_total w d hd true t4 id hf.1 hf.2.2.1 hn4 hc4 hi4
    have hother : id ∉ t6.nodeIds := hf.2.2.1.disjoint_width hf.2.2.2 (by omega) id hi4
    have he6 := Tree.eraseId_absent hc6 hother
    refine ⟨out, w', hrun, hk, ⟨?_, hr.metadata, ?_, ?_, hr.frame, hr.below hf.2.2.1⟩⟩
    · rw [he6]
      exact ⟨hr.root, hr.otherRoot.trans hf.2.1, hr.rep, hr.other_rep hf.2.2.1 t6 hf.2.2.2⟩
    · intro q hq
      exact hr.outside q (fun h => hq (List.mem_append_left _ h))
    · intro q hq hgone
      rw [he6] at hgone
      rcases List.mem_append.mp hq with h4 | h6
      · exact hr.retired q h4 (fun h => hgone (List.mem_append_left _ h))
      · exact False.elim (hgone (List.mem_append_right _ h6))
  · obtain ⟨out, w', hrun, hk, hr⟩ := remove_selected_total w d hd false t6 id hf.2.1 hf.2.2.2 hn6 hc6 hi6
    have hother : id ∉ t4.nodeIds := hf.2.2.2.disjoint_width hf.2.2.1 (by omega) id hi6
    have he4 := Tree.eraseId_absent hc4 hother
    refine ⟨out, w', hrun, hk, ⟨?_, hr.metadata, ?_, ?_, hr.frame, hr.below hf.2.2.2⟩⟩
    · rw [he4]
      exact ⟨hr.otherRoot.trans hf.1, hr.root, hr.other_rep hf.2.2.2 t4 hf.2.2.1, hr.rep⟩
    · intro q hq
      exact hr.outside q (fun h => hq (List.mem_append_right _ h))
    · intro q hq hgone
      rw [he4] at hgone
      rcases List.mem_append.mp hq with h4 | h6
      · exact False.elim (hgone (List.mem_append_left _ h4))
      · exact hr.retired q h6 (fun h => hgone (List.mem_append_right _ h))

theorem remove_forest_endpoint (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (t4 t6 : Tree) (id : Nat) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed) (hi : id ∈ t4.nodeIds ++ t6.nodeIds)
    (result : ForInStep PUnit) (hrun : (removeStep id).run w = .ok (result, w')) :
    result = .yield () ∧ ∃ out, w'.k = {w.k with wg := some out} ∧ RemovedForest d out t4 t6 id := by
  obtain ⟨out, finish, he, hk, hs⟩ := remove_forest_total w d hd t4 t6 id hf hn4 hn6 hc4 hc6 hi
  rw [hrun] at he
  cases he
  exact ⟨rfl, out, hk, hs⟩

/-- Querying the actual post-removal family root uses the unchanged original
traversal and selects the winner among exactly the non-erased entries. -/
theorem RemovedForest.findNode {id : Nat} (h : RemovedForest d out t4 t6 id)
    (w : World) (hd : w.k.wg = some out)
    (hv4 : t4.Valid 32) (hv6 : t6.Valid 128)
    (v4 : Bool) (key : Nat) (hk : key < 2 ^ rootWidth v4) :
    let t := if v4 then t4 else t6
    ∃ w', (WG.findNode (rootValue out v4) (rootWidth v4) key).run w =
        .ok ((t.eraseId id).lookupId (rootWidth v4) key, w') ∧
      w'.k = w.k ∧ Winner (rootWidth v4) key (t.entries.filter (fun e => e.id != id))
        ((t.eraseId id).lookup (rootWidth v4) key) := by
  cases v4
  · obtain ⟨w', he, hf⟩ := findNode_run w out 128 key (.inr rfl) hk hd
      (t6.eraseId id) .root6 h.forest.2.2.2 (Tree.eraseId_valid hv6 id)
    exact ⟨w', by simpa only [rootValue, Bool.false_eq_true, ↓reduceIte, rootWidth, h.forest.2.1] using he,
      hf, Tree.eraseId_lookup_spec hv6 id key⟩
  · obtain ⟨w', he, hf⟩ := findNode_run w out 32 key (.inl rfl) hk hd
      (t4.eraseId id) .root4 h.forest.2.2.1 (Tree.eraseId_valid hv4 id)
    exact ⟨w', by simpa only [rootValue, ↓reduceIte, rootWidth, h.forest.1] using he,
      hf, Tree.eraseId_lookup_spec hv4 id key⟩

end Leanux.Proofs.WG.AllowedIps
