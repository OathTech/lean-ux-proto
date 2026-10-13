import Leanux.Proofs.WG.AllowedIps.Store
import Leanux.Proofs.WG.AllowedIps.Insertion

/-! Structural store facts for mutation refinement. Freshness concerns every
resident node, including entries outside the represented tree. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

def NodesBelow (d : WG.Device) : Prop :=
  ∀ id n, d.nodes[id]? = some n → id < d.nextNode

def ForestRep (d : WG.Device) (t4 t6 : Tree) : Prop :=
  d.peerAllowedips.root4 = t4.root ∧ d.peerAllowedips.root6 = t6.root ∧
    RepAt d.nodes 32 .root4 t4 ∧ RepAt d.nodes 128 .root6 t6

theorem RepAt.resident {nodes : Std.TreeMap Nat WG.AipNode} {width : Nat}
    {parent : WG.Slot} {t : Tree} (h : RepAt nodes width parent t)
    {id : Nat} (hi : id ∈ t.nodeIds) : ∃ n, nodes[id]? = some n := by
  induction t generalizing parent with
  | empty => simp [Tree.nodeIds] at hi
  | node n l r ihl ihr =>
    simp only [Tree.nodeIds, List.mem_cons, List.mem_append] at hi
    rcases hi with rfl | hi | hi
    · exact ⟨_, h.1⟩
    · exact ihl h.2.1 hi
    · exact ihr h.2.2 hi

theorem RepAt.congr {nodes nodes' : Std.TreeMap Nat WG.AipNode} {width : Nat}
    {parent : WG.Slot} {t : Tree} (h : RepAt nodes width parent t)
    (he : ∀ id ∈ t.nodeIds, nodes'[id]? = nodes[id]?) :
    RepAt nodes' width parent t := by
  induction t generalizing parent with
  | empty => trivial
  | node n l r ihl ihr =>
    refine ⟨(he n.id (by simp [Tree.nodeIds])).trans h.1, ?_, ?_⟩
    · exact ihl h.2.1 (fun id hi => he id (by simp [Tree.nodeIds, hi]))
    · exact ihr h.2.2 (fun id hi => he id (by simp [Tree.nodeIds, hi]))

theorem RepAt.insert_disjoint {nodes : Std.TreeMap Nat WG.AipNode} {width : Nat}
    {parent : WG.Slot} {t : Tree} (h : RepAt nodes width parent t)
    (id : Nat) (n : WG.AipNode) (hi : id ∉ t.nodeIds) :
    RepAt (nodes.insert id n) width parent t := by
  apply h.congr
  intro j hj
  have hne : id ≠ j := fun he => hi (he ▸ hj)
  simp [Std.TreeMap.getElem?_insert, hne]

theorem RepAt.ids_below {d : WG.Device} {width : Nat} {parent : WG.Slot} {t : Tree}
    (h : RepAt d.nodes width parent t) (hb : NodesBelow d) :
    ∀ id ∈ t.nodeIds, id < d.nextNode := by
  intro id hi
  obtain ⟨n, hn⟩ := h.resident hi
  exact hb id n hn

theorem NodesBelow.allocate {d : WG.Device} (h : NodesBelow d) (n : WG.AipNode) :
    NodesBelow { d with nextNode := d.nextNode + 1, nodes := d.nodes.insert d.nextNode n } := by
  intro id value hv
  change id < d.nextNode + 1
  simp only [Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq] at hv
  split at hv
  · rename_i he
    simp_all
  · exact Nat.lt_trans (h id value hv) (Nat.lt_succ_self _)

/-- Every represented identifier names a node of this family's width,
including ownerless internal nodes. -/
theorem RepAt.resident_bitlen {nodes : Std.TreeMap Nat WG.AipNode} {width : Nat}
    {parent : WG.Slot} {t : Tree} (h : RepAt nodes width parent t)
    {id : Nat} (hi : id ∈ t.nodeIds) :
    ∃ n, nodes[id]? = some n ∧ n.bitlen = width := by
  induction t generalizing parent with
  | empty => simp [Tree.nodeIds] at hi
  | node n l r ihl ihr =>
    simp only [Tree.nodeIds, List.mem_cons, List.mem_append] at hi
    rcases hi with rfl | hi | hi
    · exact ⟨_, h.1, rfl⟩
    · exact ihl h.2.1 hi
    · exact ihr h.2.2 hi

end Leanux.Proofs.WG.AllowedIps
