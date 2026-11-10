import C1BelowWholeSource
import C1BelowWholeGrown
import C1BelowInternal
import C1BelowPrefixBytes
import C1BelowSeq

/-! Result C1, work package 3, the split path: everything known at the state
`t` after the successful second allocation, as one bundle, and the facts the
later segments take from it (positions, separations, the guarded bytes, the
pending first node). -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- The handed-out nodes after the first allocation. -/
abbrev liveOf (names : Allowedips.Names) (base : Nat) : List Nat := names.trie.nodes.map (·.2) ++ [base]

/-- Two memories that agree byte for byte on a range load the same value. -/
theorem loadInt_same {m m' : DataMem} (address : BitVec 64) (n : Nat)
    (same : ∀ i < n, m'.get? (address + .ofNat 64 i) = m.get? (address + .ofNat 64 i)) :
    m'.loadInt address n = m.loadInt address n := by
  have outside : EqualOutside (fun y => m'.get? y ≠ m.get? y) m' m := fun y h => Classical.not_not.mp h
  exact outside.loadInt address n (fun i bound differ => differ (same i bound))

/-- The bundle. `e` is the cut, `a` the state at the comparison (`add+0x267`),
`t` the state after the second allocation (`add+0x292`). -/
structure SplitCtx (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) (c : Context)
    (s : MachineState) (ra : UInt64) (w : World) (d : Device) (family key cidr pid : Nat)
    (stream : List HiddenRecord) (placed : Option NodeId) (names : Allowedips.Names) (base : Nat)
    (e a t : MachineState) (m : DataMem) (downId child : Nat) (downNode : AipNode)
    (rest : List HiddenRecord) (base2 : Nat) : Prop where
  rfacts : ReadyFacts L A c s family ra
  cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e
  extra : CutExtra L s e family
  summary : NodeInit.effect e.data = .ok (m,base)
  named : (downId,child) ∈ names.trie.nodes
  hasDown : (bump d).nodes.get? downId = some downNode
  cmp : Compared names c e.data (bump d) key cidr pid base child (widthOf family) downNode.bits m a
  ac : AtCompare L A c s e names base cidr stream m a
  grown : Grown L A c s a t (liveOf names base) rest base2
  fits : cidr ≤ widthOf family
  shorter : AllowedipsRelation.common (widthOf family) downNode.bits key < cidr
  keyBound : key < 2^widthOf family
  downWidth : downNode.bitlen = widthOf family

namespace SplitCtx
variable {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} {c : Context}
  {s : MachineState} {ra : UInt64} {w : World} {d : Device} {family key cidr pid : Nat}
  {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base : Nat}
  {e a t : MachineState} {m : DataMem} {downId child : Nat} {downNode : AipNode}
  {rest : List HiddenRecord} {base2 : Nat}
  (x : SplitCtx fetch L A c s ra w d family key cidr pid stream placed names base e a t m downId child
    downNode rest base2)
include x

theorem res : Res names c e.data base := resources x.rfacts x.cut x.extra

theorem fields : NodeInit.BoundaryFields names Root.nodeOffsets (bumped w d) e key cidr pid base :=
  NodeInit.boundary_fields x.cut.boundary

theorem wide : widthOf family = 32 ∨ widthOf family = 128 := by
  have := x.fields.family
  rw [x.extra.width] at this
  exact this

theorem stackA : a.data.regs.rsp = e.data.regs.rsp := x.cmp.held.stack

theorem stackT : t.data.regs.rsp = e.data.regs.rsp := x.grown.stack.trans x.stackA

/-- Where `add`'s frame lies. -/
theorem frame : 48 ≤ e.data.regs.rsp.toNat ∧ e.data.regs.rsp.toNat + 48 ≤ s.data.regs.rsp.toNat ∧
    s.data.regs.rsp.toNat + 8 ≤ 2^64 ∧ s.data.regs.rsp.toNat + 48 ≤ e.data.regs.rsp.toNat + 200 ∧
    200 + A.depth ≤ s.data.regs.rsp.toNat := by
  obtain ⟨fits,top⟩ := x.rfacts.window_bounds
  have high := x.extra.frameHigh
  have low := x.extra.frameLow
  unfold insertWindow at fits low
  omega

/-- A byte within 48 of the cut's stack pointer is in the caller's window. -/
theorem near (y : BitVec 64) (low : e.data.regs.rsp.toNat ≤ y.toNat + 48)
    (high : y.toNat < e.data.regs.rsp.toNat + 48) : Window A s y := by
  have position := x.frame
  apply window_nat x.rfacts
  · unfold insertWindow; omega
  · omega

theorem near_scratch (y : BitVec 64) (low : e.data.regs.rsp.toNat ≤ y.toNat + 48)
    (high : y.toNat < e.data.regs.rsp.toNat + 48) : Scratch s (insertWindow + A.depth) y := by
  have position := x.frame
  apply scratch_nat
  · unfold insertWindow; omega
  · omega

theorem liveArena : ∀ node ∈ liveOf names base, InArena L node := by
  intro node member
  rcases List.mem_append.mp member with old|new
  · obtain ⟨pair,named,rfl⟩ := List.mem_map.mp old
    exact x.cut.arena pair named
  · cases List.mem_singleton.mp new
    exact x.cut.fresh

omit x in
theorem baseLive : base ∈ liveOf names base := List.mem_append_right _ (List.mem_singleton_self _)

omit x in
theorem nodeLive {id address : Nat} (named : (id,address) ∈ names.trie.nodes) :
    address ∈ liveOf names base :=
  List.mem_append_left _ (List.mem_map.mpr ⟨(id,address),named,rfl⟩)

theorem liveBound {node : Nat} (member : node ∈ liveOf names base) : node + 72 ≤ 2^64 :=
  Rollback.live_bound x.cut.apart x.liveArena member

/-- The second object against a node handed out before it. -/
theorem freshApart {node : Nat} (member : node ∈ liveOf names base) :
    base2 + 72 ≤ node ∨ node + 72 ≤ base2 := by
  have checked := x.grown.fresh node member
  simp only [disjointRanges,nodeSize,Bool.or_eq_true] at checked
  exact checked.imp of_decide_eq_true of_decide_eq_true

/-- The first object against an old node. -/
theorem firstApart {id address : Nat} (named : (id,address) ∈ names.trie.nodes) :
    base + 72 ≤ address ∨ address + 72 ≤ base := by
  have checked := (allocated_facts x.fields.allocated).2.2.2.1 _ (node_allocation named)
  change disjointRanges base 72 address 72 = true at checked
  simp only [disjointRanges,Bool.or_eq_true] at checked
  exact checked.imp of_decide_eq_true of_decide_eq_true

theorem top2 : base2 + 72 < 2^64 := x.grown.top

omit x in
/-- A byte of a handed-out node, as a guarded byte. -/
theorem keptByte {node : Nat} (member : node ∈ liveOf names base) {y : BitVec 64}
    (inside : InRange (.ofNat 64 node) 72 y) : Rollback.Guarded L s a (liveOf names base) y :=
  .inr (.inr (.inl ⟨node,member,inside⟩))

omit x in
theorem nodeHeap {node : Nat} (arena : InArena L node) {y : BitVec 64}
    (inside : InRange (.ofNat 64 node) 72 y) : L.Heap y :=
  arena_heap (offset := 0) arena (by decide) inside

/-- Heap bytes are apart from the stack near the cut and from the coverage state. -/
theorem heapFar {y : BitVec 64} (heap : L.Heap y) :
    ¬(e.data.regs.rsp.toNat ≤ y.toNat + 48 ∧ y.toNat < e.data.regs.rsp.toNat + 48) ∧
    ¬c.bytes y ∧ ¬c.writes y :=
  ⟨fun near => x.rfacts.heap_window heap (x.near y near.1 near.2),x.rfacts.heap_bytes heap,
    x.rfacts.heap_writes heap⟩

/-- The coverage state is apart from the stack near the cut. -/
theorem contextFar {y : BitVec 64} (read : c.bytes y) :
    ¬(e.data.regs.rsp.toNat ≤ y.toNat + 48 ∧ y.toNat < e.data.regs.rsp.toNat + 48) :=
  fun near => x.rfacts.bytes_window read (x.near y near.1 near.2)

/-- A local of `add` reads at `t` what it read at `a`. -/
theorem localSame (offset n : Nat) (within : offset + n ≤ 48) :
    t.data.dmem.loadInt (e.data.regs.rsp.toBitVec + .ofNat 64 offset) n =
      a.data.dmem.loadInt (e.data.regs.rsp.toBitVec + .ofNat 64 offset) n := by
  have position := x.frame
  apply loadInt_same
  intro i bound
  apply x.grown.kept
  left
  rw [x.stackA]
  refine ⟨offset+i,by omega,?_⟩
  rw [BitVec.add_assoc,←BitVec.ofNat_add]

/-- A range inside a handed-out node reads at `t` what it read at `a`. -/
theorem nodeSame {node : Nat} (member : node ∈ liveOf names base) (offset n : Nat) (within : offset + n ≤ 72) :
    t.data.dmem.loadInt (.ofNat 64 (node+offset)) n = a.data.dmem.loadInt (.ofNat 64 (node+offset)) n := by
  apply loadInt_same
  intro i bound
  apply x.grown.kept
  apply keptByte member
  refine ⟨offset+i,by omega,?_⟩
  simp only [BitVec.ofNat_add,BitVec.add_assoc]

/-- What reconstruction reads under the names with the first node is fixed or kept. -/
theorem readGuarded : ∀ span ∈ readSpans (names.allocated base) Root.nodeOffsets, ∀ y, span.contains y →
    Rollback.Guarded L s a (liveOf names base) y := by
  intro span member y inside
  rcases List.mem_append.mp member with table|more
  · obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp table
    have same : (names.allocated base).table = L.table := x.cut.table
    rw [same] at inside
    exact .inr (.inl ⟨(L.table+offset,size),List.mem_append_left _ (List.mem_map.mpr ⟨(offset,size),field,rfl⟩),inside⟩)
  · rcases List.mem_append.mp more with node|peer
    · obtain ⟨⟨id,address⟩,named,mapped⟩ := List.mem_flatMap.mp node
      obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp mapped
      have all : ∀ f ∈ nodeFields Root.nodeOffsets, f.1+f.2≤72 := by decide
      have within := all _ field
      have live : address ∈ liveOf names base := by
        rcases List.mem_append.mp named with old|new
        · exact nodeLive old
        · cases List.mem_singleton.mp new
          exact baseLive
      apply keptByte live
      obtain ⟨i,bound,location⟩ := inside
      refine ⟨offset+i,by dsimp only at within bound; omega,?_⟩
      rw [location]
      simp only [BitVec.ofNat_add,BitVec.add_assoc]
    · obtain ⟨⟨id,address⟩,named,mapped⟩ := List.mem_flatMap.mp peer
      obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp mapped
      have same : (names.allocated base).trie.peers = L.peers := x.cut.peers
      rw [same] at named
      exact .inr (.inl ⟨(address+offset,size),List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨(id,address),named,List.mem_map.mpr ⟨(offset,size),field,rfl⟩⟩),inside⟩)

theorem tableGuarded (y : BitVec 64) (inside : InRange (.ofNat 64 names.table) 24 y) :
    Rollback.Guarded L s a (liveOf names base) y := by
  obtain ⟨i,bound,location⟩ := inside
  rw [x.cut.table] at location
  have field (offset : Nat) (member : (offset,8) ∈ tableFields) (low : offset ≤ i) (high : i < offset+8) :
      Rollback.Guarded L s a (liveOf names base) y := by
    refine .inr (.inl ⟨(L.table+offset,8),List.mem_append_left _ (List.mem_map.mpr ⟨(offset,8),member,rfl⟩),
      i-offset,by omega,?_⟩)
    rw [location]
    change _ = BitVec.ofNat 64 (L.table+offset) + BitVec.ofNat 64 (i-offset)
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  rcases Nat.lt_or_ge i 8 with one|one
  · exact field 0 (by decide) (by omega) (by omega)
  · rcases Nat.lt_or_ge i 16 with two|two
    · exact field 8 (by decide) (by omega) (by omega)
    · exact field 16 (by decide) (by omega) (by omega)

/-- The pending first node, in the memory after the second allocation. -/
theorem pendingT : NodeInit.Pending names e.data (bump d) key cidr pid base t.data.dmem := by
  have outside : EqualOutside (fun y => a.data.dmem.get? y ≠ t.data.dmem.get? y) a.data.dmem t.data.dmem :=
    fun y h => Classical.not_not.mp h
  exact x.cmp.held.pending.frame outside
    (fun span member y inside differ => differ (x.grown.kept y (x.readGuarded span member y inside)).symm)
    (fun y inside differ => differ (x.grown.kept y (x.tableGuarded y inside)).symm)

/-- A local of `add` as a decoded word at `t`. -/
theorem localWord (offset n value : Nat) (within : offset + n ≤ 48) (path : String)
    (read : a.data.dmem.loadInt (e.data.regs.rsp.toBitVec + .ofNat 64 offset) n = some (value : Int)) :
    word t.data.dmem path (t.data.regs.rsp.toNat+offset) n = .ok value := by
  have position := x.frame
  rw [x.stackT]
  apply Trie.word_of_loadInt path (by omega)
  rw [BitVec.ofNat_add,Root.ofNat_uint64,x.localSame offset n within]
  exact read

omit x in
/-- A natural range as bounds on the address. -/
theorem range_nat {p n : Nat} {y : BitVec 64} (fits : p + n ≤ 2^64) (inside : InRange (.ofNat 64 p) n y) :
    p ≤ y.toNat ∧ y.toNat < p + n :=
  Span.location (span := (p,n)) fits inside

omit x in
/-- Two handed-out objects that do not overlap share no byte. -/
theorem objects_apart {p q n k : Nat} {y : BitVec 64} (fp : p + n ≤ 2^64) (fq : q + k ≤ 2^64)
    (apart : p + n ≤ q ∨ q + k ≤ p) (left : InRange (.ofNat 64 p) n y) : ¬InRange (.ofNat 64 q) k y := by
  intro right
  have l := range_nat fp left
  have r := range_nat fq right
  omega

end SplitCtx

#print axioms SplitCtx.pendingT
end Binary.Statements.C1.Proof
