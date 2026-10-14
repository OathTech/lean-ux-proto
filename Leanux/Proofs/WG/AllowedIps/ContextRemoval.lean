import Leanux.Proofs.WG.AllowedIps.Removal
import Leanux.Proofs.WG.AllowedIps.Context

/-! Context evidence for local pure removal. A nonempty replacement cannot
trigger compaction above the focus; leaf removal is handled at its immediate
parent. No source execution or peer-list coherence is assumed or concluded. -/
namespace Leanux.Proofs.WG.AllowedIps

theorem Context.focus_compressed (c : Context) (u : Tree)
    (hc : (c.plug u).Compressed) : u.Compressed := by
  induction c with
  | here => exact hc
  | left n c r ih => exact ih hc.1
  | right n l c ih => exact ih hc.2.1

theorem Context.plug_nonempty (c : Context) {u : Tree} (hu : u.root.isSome) :
    (c.plug u).root.isSome := by
  cases c <;> first | exact hu | rfl

/-- Context transport requires only untouched IDs outside the focus and a
nonempty erased focus. Both premises are derived below for the local cases. -/
theorem Context.eraseId_nonempty (c : Context) (u : Tree) {id : Nat}
    (hc : (c.plug u).Compressed) (hi : id ∉ (c.plug .empty).nodeIds)
    (he : (u.eraseId id).root.isSome) :
    (c.plug u).eraseId id = c.plug (u.eraseId id) := by
  induction c with
  | here => rfl
  | left n c r ih =>
    have hn : n.id ≠ id := fun h => hi (by simp [Context.plug, Tree.nodeIds, h])
    have hr : id ∉ r.nodeIds := fun h => hi (by simp [Context.plug, Tree.nodeIds, h])
    have hcId : id ∉ (c.plug .empty).nodeIds := fun h => hi (by simp [Context.plug, Tree.nodeIds, h])
    have hrec := ih hc.1 hcId
    have hcomp : (c.plug (u.eraseId id)).Compressed := by
      rw [← hrec]
      exact Tree.eraseId_compressed _ _
    change Tree.compact (if n.id = id then {n with peer := none} else n)
      ((c.plug u).eraseId id) (r.eraseId id) = .node n (c.plug (u.eraseId id)) r
    rw [if_neg hn, hrec, Tree.eraseId_absent hc.2.1 hr]
    exact Tree.compact_eq ⟨hcomp, hc.2.1, fun hp => ⟨c.plug_nonempty he, (hc.2.2 hp).2⟩⟩
  | right n l c ih =>
    have hn : n.id ≠ id := fun h => hi (by simp [Context.plug, Tree.nodeIds, h])
    have hl : id ∉ l.nodeIds := fun h => hi (by simp [Context.plug, Tree.nodeIds, h])
    have hcId : id ∉ (c.plug .empty).nodeIds := fun h => hi (by simp [Context.plug, Tree.nodeIds, h])
    have hrec := ih hc.2.1 hcId
    have hcomp : (c.plug (u.eraseId id)).Compressed := by
      rw [← hrec]
      exact Tree.eraseId_compressed _ _
    change Tree.compact (if n.id = id then {n with peer := none} else n)
      (l.eraseId id) ((c.plug u).eraseId id) = .node n l (c.plug (u.eraseId id))
    rw [if_neg hn, Tree.eraseId_absent hc.1 hl, hrec]
    exact Tree.compact_eq ⟨hc.1, hcomp, fun hp => ⟨(hc.2.2 hp).1, c.plug_nonempty he⟩⟩

/-- Removing a binary or unary target cannot affect any ancestor's node
data or sibling. ID separation follows from the whole-tree structural premise. -/
theorem Context.eraseId_nonleaf (c : Context) (n : NodeData) (l r : Tree)
    (hc : (c.plug (.node n l r)).Compressed)
    (hn : (c.plug (.node n l r)).nodeIds.Nodup)
    (hchild : l.root.isSome ∨ r.root.isSome) :
    (c.plug (.node n l r)).eraseId n.id =
      c.plug (Tree.compact {n with peer := none} l r) := by
  have hfc := c.focus_compressed _ hc
  have hfn := c.focus_nodup _ hn
  have heq := Tree.eraseId_at_root hfc hfn
  have hi : n.id ∉ (c.plug .empty).nodeIds :=
    c.focus_disjoint _ hn n.id (by simp [Tree.nodeIds])
  have he : ((Tree.node n l r).eraseId n.id).root.isSome := by
    rw [heq, Tree.root_isSome_iff]
    intro h
    have hh := Tree.compact_eq_empty.mp h
    rcases hchild with hl | hr
    · exact (Tree.root_isSome_iff _).mp hl hh.2.1
    · exact (Tree.root_isSome_iff _).mp hr hh.2.2
  rw [c.eraseId_nonempty _ hc hi he, heq]

theorem Tree.eraseId_leaf_parent_nonempty {parent n : NodeData} {sibling : Tree}
    {side : Nat}
    (hc : (Tree.fork parent side (.node n .empty .empty) sibling).Compressed)
    (hn : (Tree.fork parent side (.node n .empty .empty) sibling).nodeIds.Nodup) :
    ((Tree.fork parent side (.node n .empty .empty) sibling).eraseId n.id).root.isSome := by
  rw [Tree.eraseId_leaf_parent hc hn]
  split
  · rename_i hp
    by_cases hs : side = 0
    · simp only [Tree.fork, if_pos hs, Tree.Compressed] at hc
      exact (hc.2.2 hp).2
    · simp only [Tree.fork, if_neg hs, Tree.Compressed] at hc
      exact (hc.2.2 hp).1
  · rw [Tree.fork_root]
    rfl

/-- A leaf removes at most its immediate parent. If that parent is owned,
only the target slot is cleared; otherwise its nonempty sibling is promoted.
All outer ancestors and sibling subtrees remain exactly the same pure data. -/
theorem Context.eraseId_leaf_parent (c : Context) (parent n : NodeData)
    (side : Nat) (sibling : Tree)
    (hc : (c.plug (Tree.fork parent side (.node n .empty .empty) sibling)).Compressed)
    (hn : (c.plug (Tree.fork parent side (.node n .empty .empty) sibling)).nodeIds.Nodup) :
    (c.plug (Tree.fork parent side (.node n .empty .empty) sibling)).eraseId n.id =
      c.plug (if parent.peer = none then sibling else Tree.fork parent side .empty sibling) := by
  have hfc := c.focus_compressed _ hc
  have hfn := c.focus_nodup _ hn
  have hi : n.id ∉ (c.plug .empty).nodeIds := c.focus_disjoint _ hn n.id
    ((Tree.mem_fork_nodeIds _ _ _ _ _).mpr (.inr (.inl (by simp [Tree.nodeIds]))))
  rw [c.eraseId_nonempty _ hc hi (Tree.eraseId_leaf_parent_nonempty hfc hfn),
    Tree.eraseId_leaf_parent hfc hfn]

end Leanux.Proofs.WG.AllowedIps
