import C1TrunkRootBody
import AllowedipsChildSource
import AllowedipsChildChecked
/-! Result C1, package 2: the source side of case `child`. `step`'s device
for the case is the landed endpoint `childInstalled` (plain equality, given
that the next node id is not the parent's), and the case facts the landed
`ChildFinish.initialization_child_checked` takes: the parent's slot on the
key's side is empty, and the case has a placed node. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem ordered_bump (d : Device) : ordered (bump d) = ordered d := rfl

/-- What `ordered` says of one stored node: two child slots, and every
child named in a slot is a stored node. -/
theorem ordered_children {d : Device} (o : ordered d = true) {id : NodeId} {n : AipNode}
    (present : d.nodes.get? id = some n) :
    n.bit.size = 2 ∧ ∀ (i : Nat) (child : NodeId), n.bit[i]? = some (some child) → ∃ c, d.nodes.get? child = some c := by
  unfold ordered at o
  simp only [Bool.and_eq_true, List.all_eq_true] at o
  have h := o.1 (id,n) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present)
  simp only [beq_iff_eq] at h
  refine ⟨h.1.2,?_⟩
  intro i child at'
  have member : (some child,i) ∈ n.bit.toList.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using at'
  have checked := h.2 (some child,i) member
  cases got : d.nodes.get? child with
  | none => simp only [got, Bool.false_eq_true] at checked
  | some c => exact ⟨c,rfl⟩

/-- `ordered`: a root slot names a stored node. -/
theorem ordered_root_plain {d : Device} (o : ordered d = true) (family : Nat) {rootId : NodeId}
    (root : (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId) :
    ∃ node, d.nodes.get? rootId = some node ∧ node.bitlen = (if family == 4 then 32 else 128) := by
  unfold ordered at o
  simp only [Bool.and_eq_true, List.all_eq_true] at o
  have roots := o.2
  by_cases four : (family == 4) = true
  · simp only [four, ↓reduceIte] at root ⊢
    have h := roots (d.peerAllowedips.root4,32) (by simp)
    cases got : d.nodes.get? rootId with
    | none => simp only [root, got] at h; cases h
    | some node => simp only [root, got] at h; exact ⟨node,rfl,eq_of_beq h⟩
  · simp only [four, Bool.false_eq_true, ↓reduceIte] at root ⊢
    have h := roots (d.peerAllowedips.root6,128) (by simp)
    cases got : d.nodes.get? rootId with
    | none => simp only [root, got] at h; cases h
    | some node => simp only [root, got] at h; exact ⟨node,rfl,eq_of_beq h⟩

/-- Case `child` (nothing stored below the placement) with a placed node:
the placed node's slot on the key's side is empty. -/
theorem child_empty {d0 : Device} (o : ordered d0 = true) {root : Option NodeId} {key : Nat}
    {p : NodeId} {parentNode : AipNode} (hasParent : d0.nodes.get? p = some parentNode)
    (nothing : (below d0 root key (some p)).bind
      (fun id => (d0.nodes.get? id).map fun n => (id,n)) = none) :
    parentNode.bit[key / 2^(parentNode.bitlen-1-parentNode.cidr) % 2]? = some none := by
  obtain ⟨size,children⟩ := ordered_children o hasParent
  have lt : key / 2^(parentNode.bitlen-1-parentNode.cidr) % 2 < parentNode.bit.size := by
    rw [size]; exact Nat.mod_lt _ (by decide)
  cases entry : parentNode.bit[key / 2^(parentNode.bitlen-1-parentNode.cidr) % 2]? with
  | none => rw [Array.getElem?_eq_none_iff] at entry; omega
  | some slot =>
    cases slot with
    | none => rfl
    | some child =>
      exfalso
      obtain ⟨c,stored⟩ := children _ child entry
      have b : below d0 root key (some p) = some child := by
        simp only [below, hasParent, entry]
        rfl
      rw [b, Option.bind_some, stored, Option.map_some] at nothing
      cases nothing

/-- Case `child` with nothing placed does not arise: below the empty
placement is the root, which is stored. -/
theorem child_placed {d0 : Device} {rootId : NodeId} {key : Nat} {node : AipNode}
    (hasRoot : d0.nodes.get? rootId = some node) :
    (below d0 (some rootId) key none).bind
      (fun id => (d0.nodes.get? id).map fun n => (id,n)) ≠ none := by
  intro h
  have b : below d0 (some rootId) key none = some rootId := rfl
  rw [b, Option.bind_some, hasRoot, Option.map_some] at h
  cases h

/-- `step`'s device for case `child` is the landed `childInstalled`. The
direction is `side` of the parent on the new node's key, which `newNode`
stores unmasked. `d0.nextNode ≠ p` is needed: otherwise the allocation
overwrites the parent and `chooseConnect` reads the new node as the parent. -/
theorem child_device (d0 : Device) (p key cidr bits pid : Nat) (parentNode : AipNode) (owner : Peer)
    (hasParent : d0.nodes.get? p = some parentNode) (hasPeer : d0.peers.get? pid = some owner)
    (different : d0.nextNode ≠ p) :
    chooseConnect (addTail (alloc d0 (newNode key cidr bits (some pid))) pid d0.nextNode) p d0.nextNode =
      childInstalled d0 p (key / 2^(parentNode.bitlen-1-parentNode.cidr) % 2) key cidr bits pid
        parentNode owner := by
  have hp : d0.peers[pid]? = some owner := hasPeer
  have hn : d0.nodes[p]? = some parentNode := hasParent
  simp [chooseConnect, connect, addTail, alloc, setSlot, hp, hn, side, childInstalled, newNode,
    Std.TreeMap.getElem?_insert, different]

#print axioms ordered_bump
#print axioms ordered_children
#print axioms ordered_root_plain
#print axioms child_empty
#print axioms child_placed
#print axioms child_device
end C1Trunk
