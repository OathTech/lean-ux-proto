import Leanux.Proofs.WG.AllowedIps.RemovalMirror
import Leanux.Proofs.WG.AllowedIps.ContextRemoval

/-! Exact node-store and backlink consequences of the local source endpoints.
The peer-map facts describe source filtering, including orphan owner labels. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem removalCleared_node (d : WG.Device) (id : Nat) (n : WG.AipNode) (q : Nat) :
    (removalCleared d id n).nodes[q]? =
      if id = q then some { n with peer := none } else d.nodes[q]? := by
  simp [removalCleared, Std.TreeMap.getElem?_insert]

theorem removalRootLeaf_node (d : WG.Device) (v4 : Bool) (id : Nat)
    (n : WG.AipNode) (q : Nat) :
    (removalRootLeaf d v4 id n).nodes[q]? = if id = q then none else d.nodes[q]? := by
  cases v4 <;> by_cases h : id = q <;>
    simp [removalRootLeaf, removalCleared, rootWrite,
      Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert, h]

theorem removalRootUnary_node (d : WG.Device) (v4 : Bool) (id : Nat)
    (n : WG.AipNode) (child : Nat) (cn : WG.AipNode) (q : Nat) :
    (removalRootUnary d v4 id n child cn).nodes[q]? =
      if id = q then none else if child = q then
        some { cn with parent := rootSlot v4 } else d.nodes[q]? := by
  cases v4 <;> by_cases h : id = q <;> by_cases hc : child = q <;>
    simp [removalRootUnary, removalCleared, rootWrite,
      Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert, h, hc]

theorem removalRootLeaf_metadata (d : WG.Device) (v4 : Bool) (id : Nat)
    (n : WG.AipNode) :
    let out := removalRootLeaf (unlisted d id) v4 id n
    out.nextNode = d.nextNode ∧ rootValue out v4 = none ∧
      rootValue out (!v4) = rootValue d (!v4) ∧
      out.peerAllowedips.seq = d.peerAllowedips.seq ∧
      ∀ q : Nat, out.peers[q]? = (d.peers[q]?).map (unlist id) := by
  dsimp only
  cases v4 <;> simp [removalRootLeaf, removalCleared, rootWrite, rootValue, unlisted_get]
  all_goals exact ⟨rfl, rfl, rfl⟩

theorem removalRootUnary_metadata (d : WG.Device) (v4 : Bool) (id : Nat)
    (n : WG.AipNode) (child : Nat) (cn : WG.AipNode) :
    let out := removalRootUnary (unlisted d id) v4 id n child cn
    out.nextNode = d.nextNode ∧ rootValue out v4 = some child ∧
      rootValue out (!v4) = rootValue d (!v4) ∧
      out.peerAllowedips.seq = d.peerAllowedips.seq ∧
      ∀ q : Nat, out.peers[q]? = (d.peers[q]?).map (unlist id) := by
  dsimp only
  cases v4 <;> simp [removalRootUnary, removalCleared, rootWrite, rootValue, unlisted_get]
  all_goals exact ⟨rfl, rfl, rfl⟩

theorem removalCleared_rep (d : WG.Device) (width : Nat) (base : WG.Slot)
    (n : NodeData) (l r : Tree)
    (hr : RepAt d.nodes width base (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup) :
    RepAt (removalCleared d n.id (encode width base n l r)).nodes width base
      (.node {n with peer := none} l r) := by
  have hi : n.id ∉ l.nodeIds ++ r.nodeIds := (List.nodup_cons.mp hn).1
  refine ⟨?_, hr.2.1.insert_disjoint n.id _ ?_, hr.2.2.insert_disjoint n.id _ ?_⟩
  · simp [removalCleared, encode]
  · exact fun h => hi (List.mem_append_left _ h)
  · exact fun h => hi (List.mem_append_right _ h)

/-- A promoted child keeps every field except its root backlink. Separation
of the retired parent and the child's descendants follows from tree Nodup. -/
theorem removalRootUnary_rep (d : WG.Device) (v4 : Bool) (n c : NodeData)
    (l r : Tree) (left : Bool)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4)
      (if left then .node n (.node c l r) .empty else .node n .empty (.node c l r)))
    (hn : (if left then Tree.node n (.node c l r) .empty
      else Tree.node n .empty (.node c l r)).nodeIds.Nodup) :
    let t := Tree.node c l r
    let old := encode (rootWidth v4) (rootSlot v4) n
      (if left then t else .empty) (if left then .empty else t)
    let child := encode (rootWidth v4) (.child n.id (if left then 0 else 1)) c l r
    RepAt (removalRootUnary d v4 n.id old c.id child).nodes
      (rootWidth v4) (rootSlot v4) t := by
  dsimp only
  cases left <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
  all_goals
    have hn' : (n.id :: c.id :: (l.nodeIds ++ r.nodeIds)).Nodup := by
      simpa [Tree.nodeIds] using hn
    have hnc : n.id ≠ c.id := fun he => (List.nodup_cons.mp hn').1 (by simp [he])
    have hnd : n.id ∉ l.nodeIds ++ r.nodeIds :=
      fun hi => (List.nodup_cons.mp hn').1 (by simp [hi])
    have hcd : c.id ∉ l.nodeIds ++ r.nodeIds :=
      (List.nodup_cons.mp (List.nodup_cons.mp hn').2).1
    apply RepAt.root_reparent (by first | exact hr.2.2 | exact hr.2.1)
    · simp [removalRootUnary_node, hnc, encode]
    · intro q hq
      have hnp : n.id ≠ q := fun he => hnd (he ▸ hq)
      have hcp : c.id ≠ q := fun he => hcd (he ▸ hq)
      simp [removalRootUnary_node, hnp, hcp]

end Leanux.Proofs.WG.AllowedIps
