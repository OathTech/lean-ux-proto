import Leanux.Proofs.WG.AllowedIps.RemovalChildStore
import Leanux.Proofs.WG.AllowedIps.GraftLink

/-! Structural evidence for removal. Membership supplies a real focus;
duplicate-free trees supply separation, and unequal encoded widths separate
the two families. None of these facts require resident owner labels. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem Tree.focus_of_mem {t : Tree} {id : Nat} (hi : id ∈ t.nodeIds) :
    ∃ (c : Context) (n : NodeData) (l r : Tree), t = c.plug (.node n l r) ∧ n.id = id := by
  induction t with
  | empty => simp [Tree.nodeIds] at hi
  | node n l r ihl ihr =>
    simp only [Tree.nodeIds, List.mem_cons, List.mem_append] at hi
    rcases hi with he | hi | hi
    · exact ⟨.here, n, l, r, rfl, he.symm⟩
    · obtain ⟨c, a, al, ar, he, hid⟩ := ihl hi
      exact ⟨.left n c r, a, al, ar, congrArg (fun x => Tree.node n x r) he, hid⟩
    · obtain ⟨c, a, al, ar, he, hid⟩ := ihr hi
      exact ⟨.right n l c, a, al, ar, congrArg (Tree.node n l) he, hid⟩

theorem Context.last_gap_shape (c : Context) (hc : c ≠ .here) :
    ∃ (outer : Context) (parent : NodeData) (side : Nat) (sibling : Tree),
      side < 2 ∧ c = outer.append (gapContext parent side sibling) := by
  obtain ⟨outer, parent, l, r, side, hb, he⟩ := c.last_edge hc
  have hs : side = 0 ∨ side = 1 := by omega
  rcases hs with rfl | rfl
  · exact ⟨outer, parent, 0, r, by omega, he⟩
  · exact ⟨outer, parent, 1, l, by omega, he⟩

@[simp] theorem gapContext_slot (n : NodeData) (side : Nat) (sibling : Tree)
    (hb : side < 2) (base : WG.Slot) :
    (gapContext n side sibling).slot base = .child n.id side := by
  have hs : side = 0 ∨ side = 1 := by omega
  rcases hs with rfl | rfl <;> rfl

theorem RepAt.disjoint_width (ha : RepAt nodes wa pa a) (hb : RepAt nodes wb pb b)
    (hw : wa ≠ wb) : ∀ id ∈ a.nodeIds, id ∉ b.nodeIds := by
  intro id hi hj
  obtain ⟨n, hn, hnw⟩ := ha.resident_bitlen hi
  obtain ⟨m, hm, hmw⟩ := hb.resident_bitlen hj
  have he := Option.some.inj (hn.symm.trans hm)
  exact hw (hnw.symm.trans (he ▸ hmw))

theorem Tree.fork_nodup_iff (n : NodeData) (side : Nat) (chosen sibling : Tree) :
    (Tree.fork n side chosen sibling).nodeIds.Nodup ↔
      n.id ∉ chosen.nodeIds ∧ n.id ∉ sibling.nodeIds ∧
      chosen.nodeIds.Nodup ∧ sibling.nodeIds.Nodup ∧
      ∀ id ∈ chosen.nodeIds, id ∉ sibling.nodeIds := by
  have hp := Tree.fork_nodeIds_perm n side chosen sibling
  rw [hp.nodup_iff]
  simp only [List.nodup_cons, List.nodup_append, List.mem_append, not_or]
  grind

@[simp] theorem forkNode_parent : (forkNode width base n side chosen sibling).parent = base := by
  unfold forkNode; split <;> rfl

@[simp] theorem forkNode_peer : (forkNode width base n side chosen sibling).peer = n.peer := by
  unfold forkNode; split <;> rfl

theorem forkNode_other (hb : side < 2) :
    (forkNode width base n side chosen sibling).bit[1-side]? = some sibling.root := by
  have hs : side = 0 ∨ side = 1 := by omega
  rcases hs with rfl | rfl <;> rfl

theorem Tree.fork_compressed_parts
    (hc : (Tree.fork n side chosen sibling).Compressed) :
    chosen.Compressed ∧ sibling.Compressed ∧
      (n.peer = none → chosen.root.isSome ∧ sibling.root.isSome) := by
  unfold Tree.fork at hc
  split at hc
  · exact hc
  · exact ⟨hc.2.1, hc.1, fun hp => ⟨(hc.2.2 hp).2, (hc.2.2 hp).1⟩⟩

theorem RepAt.erase_disjoint {id : Nat} (hr : RepAt nodes width base t) (hi : id ∉ t.nodeIds) :
    RepAt (nodes.erase id) width base t := by
  apply hr.congr
  intro q hq
  have hne : id ≠ q := fun he => hi (he ▸ hq)
  simp [Std.TreeMap.getElem?_erase, hne]

/-- Pointwise preservation outside the original selected tree also preserves
unreachable resident entries. It is stronger than an other-family frame. -/
def RemovalOutside (d out : WG.Device) (t : Tree) : Prop :=
  ∀ q, q ∉ t.nodeIds → out.nodes[q]? = d.nodes[q]?

theorem RemovalOutside.below (hf : RemovalOutside d out t)
    (hr : RepAt d.nodes width base t) (hn : out.nextNode = d.nextNode)
    (hb : NodesBelow d) : NodesBelow out := by
  intro q n hg
  rw [hn]
  by_cases hq : q ∈ t.nodeIds
  · exact hr.ids_below hb q hq
  · exact hb q n ((hf q hq) ▸ hg)

theorem RemovalOutside.other {other : Tree} (hf : RemovalOutside d out t)
    (hr : RepAt d.nodes width base t) (ho : RepAt d.nodes width' base' other)
    (hw : width ≠ width') : RepAt out.nodes width' base' other := by
  apply ho.congr
  intro q hq
  exact hf q (fun ht => hr.disjoint_width ho hw q ht hq)

theorem Context.eraseId_unary (c : Context) (n a : NodeData) (side : Nat) (l r : Tree)
    (hc : (c.plug (Tree.fork n side (.node a l r) .empty)).Compressed)
    (hn : (c.plug (Tree.fork n side (.node a l r) .empty)).nodeIds.Nodup) :
    (c.plug (Tree.fork n side (.node a l r) .empty)).eraseId n.id = c.plug (.node a l r) := by
  by_cases hs : side = 0
  · simpa [Tree.fork, hs, Tree.compact] using
      c.eraseId_nonleaf n (.node a l r) .empty (by simpa [Tree.fork, hs] using hc)
        (by simpa [Tree.fork, hs] using hn) (.inl rfl)
  · simpa [Tree.fork, hs, Tree.compact] using
      c.eraseId_nonleaf n .empty (.node a l r) (by simpa [Tree.fork, hs] using hc)
        (by simpa [Tree.fork, hs] using hn) (.inr rfl)

theorem removalCollapseRoot_frame (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (v4 : Bool) (sibling : Option (Nat × WG.AipNode)) :
    let out := removalCollapseRoot (unlisted d id) id n parent side pn v4 sibling
    out = {d with nodes := out.nodes, peers := out.peers, peerAllowedips := out.peerAllowedips} := by
  cases v4 <;> cases sibling <;>
    simp only [removalCollapseRoot, removalParentRoot, removalSibling,
      removalLeafDetached, removalCleared, unlisted, rootWrite, Bool.false_eq_true,
      ↓reduceIte, Option.map_none, Option.map_some]

end Leanux.Proofs.WG.AllowedIps
