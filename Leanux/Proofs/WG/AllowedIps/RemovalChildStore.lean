import Leanux.Proofs.WG.AllowedIps.RemovalSteps
import Leanux.Proofs.WG.AllowedIps.RemovalStore

/-! Whole-store equations for nonroot removal. Conditional priority follows
the actual writes even on aliased raw arguments; execution theorems establish
the distinctness needed for target/parent retirement and sibling promotion. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem removalChildUnary_node (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (child : Nat) (cn : WG.AipNode) (q : Nat) :
    (removalChildUnary d id n parent side pn child cn).nodes[q]? =
      if id = q then none else if parent = q then
        some { pn with bit := pn.bit.set! side (some child) } else if child = q then
        some { cn with parent := .child parent side } else d.nodes[q]? := by
  simp [removalChildUnary, connectedChild, removalCleared, Std.TreeMap.getElem?_erase,
    Std.TreeMap.getElem?_insert]
  split <;> simp_all

theorem removalLeafDetached_node (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (q : Nat) :
    (removalLeafDetached d id n parent side pn).nodes[q]? =
      if id = q then none else if parent = q then
        some { pn with bit := pn.bit.set! side none } else d.nodes[q]? := by
  simp [removalLeafDetached, removalCleared, Std.TreeMap.getElem?_erase,
    Std.TreeMap.getElem?_insert]
  split <;> simp_all

theorem removalCollapseRoot_node (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (v4 : Bool)
    (sibling : Option (Nat × WG.AipNode)) (q : Nat) :
    (removalCollapseRoot d id n parent side pn v4 sibling).nodes[q]? =
      if parent = q then none else
        match sibling with
        | none => if id = q then none else d.nodes[q]?
        | some (c, cn) => if c = q then some { cn with parent := rootSlot v4 }
            else if id = q then none else d.nodes[q]? := by
  cases v4 <;> cases sibling with
  | none =>
    by_cases hp : parent = q <;> by_cases hi : id = q <;>
      simp [removalCollapseRoot, removalParentRoot, removalSibling, rootWrite,
        removalLeafDetached_node, Std.TreeMap.getElem?_erase, hp, hi]
  | some s =>
    rcases s with ⟨c, cn⟩
    by_cases hp : parent = q <;> by_cases hi : id = q <;> by_cases hc : c = q <;>
      simp [removalCollapseRoot, removalParentRoot, removalSibling, rootWrite, rootSlot,
        removalLeafDetached_node, Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert, hp, hi, hc]

theorem removalCollapseChild_node (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (grand gside : Nat) (gn : WG.AipNode)
    (sibling : Option (Nat × WG.AipNode)) (q : Nat) :
    (removalCollapseChild d id n parent side pn grand gside gn sibling).nodes[q]? =
      if parent = q then none else if grand = q then
        some { gn with bit := gn.bit.set! gside (sibling.map Prod.fst) } else
        match sibling with
        | none => if id = q then none else d.nodes[q]?
        | some (c, cn) => if c = q then some { cn with parent := .child grand gside }
            else if id = q then none else d.nodes[q]? := by
  cases sibling with
  | none =>
    by_cases hp : parent = q <;> by_cases hg : grand = q <;> by_cases hi : id = q <;>
      simp [removalCollapseChild, removalParentChild, removalSibling,
        removalLeafDetached_node, Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert, hp, hg, hi]
  | some s =>
    rcases s with ⟨c, cn⟩
    by_cases hp : parent = q <;> by_cases hg : grand = q <;>
      by_cases hi : id = q <;> by_cases hc : c = q <;>
      simp [removalCollapseChild, removalParentChild, removalSibling,
        removalLeafDetached_node, Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert,
        Std.TreeMap.getElem_insert, hp, hg, hi, hc]

/-- The shared metadata concerns one list iteration; the outer loop's
single sequence increment remains outside these endpoints. -/
def RemovalMetadata (d out : WG.Device) (id : Nat) : Prop :=
  out.nextNode = d.nextNode ∧ out.peerAllowedips.seq = d.peerAllowedips.seq ∧
    ∀ q : Nat, out.peers[q]? = (d.peers[q]?).map (unlist id)

theorem removalChildUnary_metadata (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (child : Nat) (cn : WG.AipNode) :
    let out := removalChildUnary (unlisted d id) id n parent side pn child cn
    RemovalMetadata d out id ∧ ∀ v4, rootValue out v4 = rootValue d v4 := by
  dsimp only [RemovalMetadata, removalChildUnary, connectedChild, removalCleared, rootValue, unlisted]
  refine ⟨⟨rfl, rfl, ?_⟩, fun _ => rfl⟩
  exact unlisted_get d id

theorem removalLeafDetached_metadata (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) :
    let out := removalLeafDetached (unlisted d id) id n parent side pn
    RemovalMetadata d out id ∧ ∀ v4, rootValue out v4 = rootValue d v4 := by
  dsimp only [RemovalMetadata, removalLeafDetached, removalCleared, rootValue, unlisted]
  refine ⟨⟨rfl, rfl, ?_⟩, fun _ => rfl⟩
  exact unlisted_get d id

theorem removalCollapseRoot_metadata (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (v4 : Bool) (sibling : Option (Nat × WG.AipNode)) :
    let out := removalCollapseRoot (unlisted d id) id n parent side pn v4 sibling
    RemovalMetadata d out id ∧ rootValue out v4 = sibling.map Prod.fst ∧
      rootValue out (!v4) = rootValue d (!v4) := by
  cases v4 <;> cases sibling <;>
    dsimp only [RemovalMetadata, removalCollapseRoot, removalParentRoot, removalSibling,
      removalLeafDetached, removalCleared, rootWrite, rootValue, unlisted, Option.map]
  all_goals exact ⟨⟨rfl, rfl, unlisted_get d id⟩, rfl, rfl⟩

theorem removalCollapseChild_metadata (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (grand gside : Nat) (gn : WG.AipNode)
    (sibling : Option (Nat × WG.AipNode)) :
    let out := removalCollapseChild (unlisted d id) id n parent side pn grand gside gn sibling
    RemovalMetadata d out id ∧ ∀ v4, rootValue out v4 = rootValue d v4 := by
  cases sibling <;>
    dsimp only [RemovalMetadata, removalCollapseChild, removalParentChild, removalSibling,
      removalLeafDetached, removalCleared, rootValue, unlisted]
  all_goals exact ⟨⟨rfl, rfl, unlisted_get d id⟩, fun _ => rfl⟩

end Leanux.Proofs.WG.AllowedIps
