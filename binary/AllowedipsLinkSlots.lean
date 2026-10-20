import AllowedipsStorage
import AllowedipsPeerListIdentity

namespace Binary.Pair.Allowedips

theorem Geometry.slices_apart {names o} (g : Geometry names o) {l r : Span}
    (lm : l ∈ allocations names o) (rm : r ∈ allocations names o)
    (offset size otherOffset otherSize : Nat) (within : offset+size≤l.2) (otherWithin : otherOffset+otherSize≤r.2)
    (same : l=r → offset+size≤otherOffset ∨ otherOffset+otherSize≤offset) :
    ∀ a, InRange (.ofNat 64 (l.1+offset)) size a → ¬InRange (.ofNat 64 (r.1+otherOffset)) otherSize a := by
  have lb := g.bounded l lm
  have rb := g.bounded r rm
  have numeric : l.1+offset+size≤r.1+otherOffset ∨ r.1+otherOffset+otherSize≤l.1+offset := by
    by_cases equal : l=r
    · rcases same equal with h|h <;> have := congrArg Prod.fst equal <;> omega
    · have ranges := Trie.pairwise_mem_ne (R := fun a b : Span => disjointRanges a.1 a.2 b.1 b.2=true)
        (fun a b h => by simpa only [disjointRanges,Bool.or_comm] using h) g.apart lm rm equal
      have disjoint : l.1+l.2≤r.1 ∨ r.1+r.2≤l.1 := by
        simpa only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] using ranges
      rcases disjoint with h|h <;> omega
  intro a first second
  have := Span.location (span := (l.1+offset,size)) (by omega) first
  have := Span.location (span := (r.1+otherOffset,otherSize)) (by omega) second
  rcases numeric with h|h <;> omega

inductive LinkSlot (names : Names) : Nat → Prop
  | node {id base} (named : (id,base) ∈ names.trie.nodes) : LinkSlot names (base+56)
  | peer {id base} (named : (id,base) ∈ names.trie.peers) : LinkSlot names (base+1096)

theorem LinkSlot.word {names o link} (slot : LinkSlot names link) (layout : o.nodeSize=72)
    (offset : Nat) (which : offset=0 ∨ offset=8) : WordSlot names o (link+offset) := by
  cases slot with
  | node named =>
    rw [Nat.add_assoc]
    apply WordSlot.node named
    · rcases which with rfl|rfl <;> decide
    · rw [layout]; rcases which with rfl|rfl <;> decide
  | peer named =>
    rw [Nat.add_assoc]
    apply WordSlot.peer named
    · rcases which with rfl|rfl <;> decide
    · rcases which with rfl|rfl <;> decide

theorem node_allocation {names o id base} (named : (id,base) ∈ names.trie.nodes) :
    (base,o.nodeSize) ∈ allocations names o :=
  List.mem_append_left _ (List.mem_map.mpr ⟨(id,base),named,rfl⟩)

theorem peer_allocation {names o id base} (named : (id,base) ∈ names.trie.peers) :
    (base,Layouts.peerSize) ∈ allocations names o :=
  List.mem_append_right _ (List.mem_map.mpr ⟨(id,base),named,rfl⟩)

/-- Next and previous fields cannot alias, including a peer sentinel and a
node in that peer's list. This follows from allocation geometry, not alignment. -/
theorem LinkSlot.forward_back_apart {names o left right}
    (l : LinkSlot names left) (r : LinkSlot names right) (g : Geometry names o) (layout : o.nodeSize=72) :
    ∀ a, InRange (.ofNat 64 left) 8 a → ¬InRange (.ofNat 64 (right+8)) 8 a := by
  cases l with
  | node ln =>
    cases r with
    | node rn =>
      simpa only [Nat.add_assoc] using g.slices_apart (node_allocation ln) (node_allocation rn) 56 8 64 8
        (by dsimp only; rw [layout]; decide) (by dsimp only; rw [layout]; decide) (fun _ => .inl (by decide))
    | peer rn =>
      simpa only [Nat.add_assoc] using g.slices_apart (node_allocation ln) (peer_allocation rn) 56 8 1104 8
        (by dsimp only; rw [layout]; decide) (by dsimp only; decide) (fun _ => .inl (by decide))
  | peer ln =>
    cases r with
    | node rn =>
      simpa only [Nat.add_assoc] using g.slices_apart (peer_allocation ln) (node_allocation rn) 1096 8 64 8
        (by dsimp only; decide) (by dsimp only; rw [layout]; decide) (fun _ => .inr (by decide))
    | peer rn =>
      simpa only [Nat.add_assoc] using g.slices_apart (peer_allocation ln) (peer_allocation rn) 1096 8 1104 8
        (by dsimp only; decide) (by dsimp only; decide) (fun _ => .inl (by decide))

theorem LinkSlot.owner_apart {names o link id base} (slot : LinkSlot names link)
    (owner : (id,base) ∈ names.trie.nodes) (g : Geometry names o) (layout : o.nodeSize=72)
    (offset : Nat) (which : offset=0 ∨ offset=8) :
    ∀ a, InRange (.ofNat 64 (link+offset)) 8 a → ¬InRange (.ofNat 64 base) 8 a := by
  cases slot with
  | node named =>
    simpa only [Nat.add_assoc,Nat.add_zero] using g.slices_apart (node_allocation named) (node_allocation owner)
      (56+offset) 8 0 8 (by dsimp only; rw [layout]; rcases which with rfl|rfl <;> decide)
      (by dsimp only; rw [layout]; decide) (fun _ => .inr (by omega))
  | peer named =>
    simpa only [Nat.add_assoc,Nat.add_zero] using g.slices_apart (peer_allocation named) (node_allocation owner)
      (1096+offset) 8 0 8 (by dsimp only; rcases which with rfl|rfl <;> decide)
      (by dsimp only; rw [layout]; decide) (fun _ => .inr (by omega))

theorem Ring.Fields.slot {names m head previous link next id}
    (fields : Ring.Fields names m head previous link next id) : LinkSlot names link := by
  have named := fields.named
  have location : link-AllowedipsMutationLayout.peer_list+56=link := by
    have := fields.valid
    change 56≤link at this
    change link-56+56=link
    omega
  rw [←location]
  exact .node named

#print axioms LinkSlot.forward_back_apart
#print axioms LinkSlot.owner_apart
end Binary.Pair.Allowedips
