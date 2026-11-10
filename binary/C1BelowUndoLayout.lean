import C1BelowUndoAttach
import C1BelowFlight
import PairAllowedipsReadSet

/-! Result C1, work package 3, rollback: where the bytes the old
interpretation reads lie in the layout (fixed words or handed-out nodes),
and stack-byte arithmetic. -/
namespace Binary.Statements.C1.Proof.Undo
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.Pair.Allowedips.Root

variable {L : Layout} {A : Allocator} {c : Context} {s : MachineState} {family : Nat} {ra : UInt64}

/-- A byte of one of the layout's fixed words. -/
def Fixed (L : Layout) (x : BitVec 64) : Prop := ∃ span ∈ L.fixed, span.contains x

theorem Fixed.heap {x : BitVec 64} (fixed : Fixed L x) : L.Heap x := by
  obtain ⟨span,member,inside⟩ := fixed
  exact ⟨span,List.mem_append_left _ member,inside⟩

private theorem table_fields : ∀ field ∈ tableFields, field.1+field.2 ≤ AllowedipsMutationLayout.tableSize := by
  decide

private theorem peer_fields : ∀ field ∈ peerFields nodeOffsets, field.1+field.2 ≤ Layouts.peerSize := by
  decide

private theorem node_fields : ∀ field ∈ nodeFields nodeOffsets, field.1+field.2 ≤ 72 := by
  decide

/-- A fixed word lies inside the table or a peer object. -/
theorem Fixed.object {x : BitVec 64} (fixed : Fixed L x) : ∃ object ∈ objectsOf L, object.contains x := by
  obtain ⟨span,member,inside⟩ := fixed
  rcases List.mem_append.mp member with table | peer
  · obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp table
    exact ⟨(L.table,AllowedipsMutationLayout.tableSize),List.mem_append_left _ (List.mem_singleton_self _),
      range_slice (table_fields _ field) inside⟩
  · obtain ⟨⟨id,address⟩,named,inner⟩ := List.mem_flatMap.mp peer
    obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp inner
    exact ⟨(address,Layouts.peerSize),
      List.mem_append_right _ (List.mem_map.mpr ⟨(id,address),named,rfl⟩),
      range_slice (peer_fields _ field) inside⟩

/-- Fixed words are outside the arena. -/
theorem Fixed.not_arena (apart : spansApart (objectsOf L) L.arena = true) {x : BitVec 64}
    (fixed : Fixed L x) : ¬L.Arena x := by
  obtain ⟨object,member,inside⟩ := fixed.object
  rintro ⟨span,named,within⟩
  exact spansApart_sound apart member named inside within

/-- A word of a link slot is a fixed word of a peer or lies in an old node. -/
theorem slot_class {names : Allowedips.Names} (peers : names.trie.peers = L.peers) {link offset : Nat}
    (slot : LinkSlot names link) (which : offset = 0 ∨ offset = 8) {x : BitVec 64}
    (inside : InRange (.ofNat 64 (link+offset)) 8 x) :
    Fixed L x ∨ Kept (names.trie.nodes.map (·.2)) x := by
  cases slot with
  | @node id address named =>
    right
    refine ⟨address,List.mem_map.mpr ⟨(id,address),named,rfl⟩,?_⟩
    rw [Nat.add_assoc] at inside
    exact range_slice (by rcases which with rfl | rfl <;> decide) inside
  | @peer id address named =>
    left
    rw [peers] at named
    rw [Nat.add_assoc] at inside
    refine ⟨(address+(1096+offset),8),List.mem_append_right _ (List.mem_flatMap.mpr ⟨(id,address),named,
      List.mem_map.mpr ⟨(1096+offset,8),?_,rfl⟩⟩),inside⟩
    rcases which with rfl | rfl <;> decide

/-- Every byte the old interpretation reads is a fixed word or lies in an old node. -/
theorem read_class {names : Allowedips.Names} (table : names.table = L.table)
    (peers : names.trie.peers = L.peers) {span : Pair.Span}
    (member : span ∈ readSpans names nodeOffsets) {x : BitVec 64} (inside : span.contains x) :
    Fixed L x ∨ Kept (names.trie.nodes.map (·.2)) x := by
  unfold readSpans at member
  rw [table,peers] at member
  rcases List.mem_append.mp member with tableField | rest
  · exact .inl ⟨span,List.mem_append_left _ tableField,inside⟩
  · rcases List.mem_append.mp rest with node | peer
    · obtain ⟨⟨id,address⟩,named,inner⟩ := List.mem_flatMap.mp node
      obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp inner
      exact .inr ⟨address,List.mem_map.mpr ⟨(id,address),named,rfl⟩,range_slice (node_fields _ field) inside⟩
    · exact .inl ⟨span,List.mem_append_right _ peer,inside⟩

/-- Releasing the fresh node leaves the old nodes. -/
theorem erase_fresh {nodes : List Nat} {base : Nat} (absent : base ∉ nodes) :
    (nodes ++ [base]).erase base = nodes := by
  rw [List.erase_append_right _ absent]
  simp

/-- Natural bounds of a footprint that does not wrap. -/
theorem range_nat {base : BitVec 64} {n : Nat} {y : BitVec 64} (fits : base.toNat+n ≤ 2^64)
    (inside : InRange base n y) : base.toNat ≤ y.toNat ∧ y.toNat < base.toNat+n := by
  obtain ⟨i,bound,at_⟩ := inside
  have value := congrArg BitVec.toNat at_
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat] at value
  omega

/-- A byte whose natural address lies in a non-wrapping range is in it. -/
theorem range_of_nat {base : BitVec 64} {n : Nat} {y : BitVec 64}
    (low : base.toNat ≤ y.toNat) (high : y.toNat < base.toNat+n) : InRange base n y := by
  refine ⟨y.toNat-base.toNat,by omega,?_⟩
  apply BitVec.eq_of_toNat_eq
  have small := y.isLt
  have other := base.isLt
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

/-- A byte at a natural address inside the caller's window with the return word. -/
theorem window_nat {y : BitVec 64}
    (fits : insertWindow + A.depth ≤ s.data.regs.rsp.toNat)
    (low : s.data.regs.rsp.toNat ≤ y.toNat + (insertWindow + A.depth))
    (high : y.toNat < s.data.regs.rsp.toNat + 8) : Window A s y := by
  apply range_of_nat
  · have bound := s.data.regs.rsp.toBitVec.isLt
    have rsp : s.data.regs.rsp.toBitVec.toNat = s.data.regs.rsp.toNat := rfl
    simp only [BitVec.toNat_sub,BitVec.toNat_ofNat,rsp]
    omega
  · have bound := s.data.regs.rsp.toBitVec.isLt
    have rsp : s.data.regs.rsp.toBitVec.toNat = s.data.regs.rsp.toNat := rfl
    simp only [BitVec.toNat_sub,BitVec.toNat_ofNat,rsp]
    omega

#print axioms read_class
#print axioms slot_class
#print axioms window_nat
end Binary.Statements.C1.Proof.Undo
