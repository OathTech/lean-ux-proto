import PairAllowedipsDecode
import PairAllocationProof

namespace Binary.Pair.Allowedips

/-- Allocation geometry is derived from existing reconstruction validation.
These spans support word-separation proofs; they add no relation clauses. -/
def allocations (names : Names) (o : AllowedipsProbe.Offsets) : List Span :=
  names.trie.nodes.map (fun (_,a) => (a,o.nodeSize)) ++
    names.trie.peers.map (fun (_,a) => (a,Layouts.peerSize))

structure Geometry (names : Names) (o : AllowedipsProbe.Offsets) : Prop where
  bounded : ∀ span ∈ allocations names o, span.1+span.2≤2^64
  apart : (allocations names o).Pairwise (fun a b => disjointRanges a.1 a.2 b.1 b.2=true)

theorem geometry {names o m d} (related : Corresponds names o m d) : Geometry names o := by
  have core := related.trie
  have fields := Trie.reconstruct_fields core
  unfold Trie.Corresponds Trie.reconstruct at core
  obtain ⟨value,validated,_⟩ := bind_ok core
  cases value
  refine ⟨?_,Trie.validate_pairwise validated⟩
  intro span member
  rcases List.mem_append.mp member with node | peer
  · obtain ⟨⟨id,a⟩,named,rfl⟩ := List.mem_map.mp node
    exact Nat.le_of_lt (fields.nodeRange id a named).2
  · obtain ⟨⟨id,a⟩,named,rfl⟩ := List.mem_map.mp peer
    exact Nat.le_of_lt (fields.peerRange id a named).2

/-- A word-sized field at an eight-byte offset in a named allocation. The
allocation base itself need not be aligned for x86-64 word accesses. -/
def WordSlot (names : Names) (o : AllowedipsProbe.Offsets) (address : Nat) : Prop :=
  ∃ span ∈ allocations names o, ∃ offset, offset%8=0 ∧ offset+8≤span.2 ∧ address=span.1+offset

theorem WordSlot.bounded {names o address} (slot : WordSlot names o address) (g : Geometry names o) :
    address+8≤2^64 := by
  obtain ⟨span,member,offset,_,within,rfl⟩ := slot
  have := g.bounded span member
  omega

theorem WordSlot.disjoint {names o address destination}
    (left : WordSlot names o address) (right : WordSlot names o destination)
    (g : Geometry names o) (different : address≠destination) :
    ∀ a, InRange (.ofNat 64 address) 8 a → ¬InRange (.ofNat 64 destination) 8 a := by
  have lb := left.bounded g
  have rb := right.bounded g
  obtain ⟨l,lm,lo,la,lw,rfl⟩ := left
  obtain ⟨r,rm,ro,ra,rw,rfl⟩ := right
  have numeric : l.1+lo+8≤r.1+ro ∨ r.1+ro+8≤l.1+lo := by
    by_cases same : l=r
    · subst r
      omega
    · have apart := Trie.pairwise_mem_ne (R := fun a b : Span => disjointRanges a.1 a.2 b.1 b.2=true)
        (fun a b h => by simpa only [disjointRanges,Bool.or_comm] using h) g.apart lm rm same
      have ranges : l.1+l.2≤r.1 ∨ r.1+r.2≤l.1 := by
        simpa only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] using apart
      rcases ranges with h|h <;> omega
  intro a first second
  have := Span.location (span := (l.1+lo,8)) lb first
  have := Span.location (span := (r.1+ro,8)) rb second
  rcases numeric with h|h <;> omega

theorem WordSlot.node {names o id base offset}
    (named : (id,base) ∈ names.trie.nodes) (align : offset%8=0) (size : offset+8≤o.nodeSize) :
    WordSlot names o (base+offset) :=
  ⟨(base,o.nodeSize),List.mem_append_left _ (List.mem_map.mpr ⟨(id,base),named,rfl⟩),offset,align,size,rfl⟩

theorem WordSlot.peer {names o id base offset}
    (named : (id,base) ∈ names.trie.peers) (align : offset%8=0) (size : offset+8≤Layouts.peerSize) :
    WordSlot names o (base+offset) :=
  ⟨(base,Layouts.peerSize),List.mem_append_right _ (List.mem_map.mpr ⟨(id,base),named,rfl⟩),offset,align,size,rfl⟩

#print axioms geometry
#print axioms WordSlot.disjoint
end Binary.Pair.Allowedips
