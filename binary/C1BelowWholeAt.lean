import C1BelowWholeInit
import C1BelowWholeValid
import C1BelowSplitSegment

/-! Result C1, work package 3, the split path: the facts the connections
take at `add+0x338`, derived from the bundle and `AtConnect`: which bytes
are as they were after the second allocation, the pending first node and
the old nodes decoded there, the validity of the twice-extended names, the
initialized internal node, the machine entry state of the connections. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root AllowedipsChild Binary.AllowedipsRelation
local instance : Labels := Image.linkedLabels

/-- A range inside an object at a natural address, as bounds. -/
theorem natRange {p off n : Nat} {y : BitVec 64} (fits : p + 72 ≤ 2^64) (within : off + n ≤ 72)
    (inside : InRange (BitVec.ofNat 64 p + BitVec.ofNat 64 off) n y) :
    p + off ≤ y.toNat ∧ y.toNat < p + off + n := by
  rw [←BitVec.ofNat_add] at inside
  exact SplitCtx.range_nat (by omega) inside

theorem natRange2 {p o1 o2 n : Nat} {y : BitVec 64} (fits : p + 72 ≤ 2^64) (within : o1 + o2 + n ≤ 72)
    (inside : InRange (BitVec.ofNat 64 p + BitVec.ofNat 64 o1 + BitVec.ofNat 64 o2) n y) :
    p + o1 + o2 ≤ y.toNat ∧ y.toNat < p + o1 + o2 + n := by
  rw [←BitVec.ofNat_add,←BitVec.ofNat_add] at inside
  exact SplitCtx.range_nat (by omega) inside

/-- Bounds on an address put it in the object's 72 bytes. -/
theorem inObject {p : Nat} {y : BitVec 64} (low : p ≤ y.toNat) (high : y.toNat < p + 72) :
    InRange (.ofNat 64 p) 72 y := by
  refine ⟨y.toNat-p,by omega,?_⟩
  apply BitVec.eq_of_toNat_eq
  have small := y.isLt
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

/-- Fixed words and bytes of nodes handed out before the second allocation. -/
def Solid (L : Layout) (names : Allowedips.Names) (base : Nat) (y : BitVec 64) : Prop :=
  (∃ span ∈ L.fixed, span.contains y) ∨ Kept (liveOf names base) y

namespace SplitCtx
variable {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} {c : Context}
  {s : MachineState} {ra : UInt64} {w : World} {d : Device} {family key cidr pid : Nat}
  {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base : Nat}
  {e a t : MachineState} {m : DataMem} {downId child : Nat} {downNode : AipNode}
  {rest : List HiddenRecord} {base2 : Nat}
  (x : SplitCtx fetch L A c s ra w d family key cidr pid stream placed names base e a t m downId child
    downNode rest base2)
include x

/-- A fixed word of the layout is not in the arena. -/
theorem fixedOutside {y : BitVec 64} (fixed : ∃ span ∈ L.fixed, span.contains y) : ¬L.Arena y := by
  obtain ⟨span,member,inside⟩ := fixed
  rintro ⟨region,named,within⟩
  have object : ∃ obj ∈ objectsOf L, obj.contains y := by
    rcases List.mem_append.mp member with table|peer
    · obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp table
      have all : ∀ f ∈ tableFields, f.1+f.2≤AllowedipsMutationLayout.tableSize := by decide
      have small := all _ field
      obtain ⟨i,bound,location⟩ := inside
      refine ⟨(L.table,AllowedipsMutationLayout.tableSize),by simp [objectsOf],offset+i,
        by dsimp only at small bound ⊢; omega,?_⟩
      rw [location]
      simp only [BitVec.ofNat_add,BitVec.add_assoc]
    · obtain ⟨⟨id,address⟩,present,mapped⟩ := List.mem_flatMap.mp peer
      obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp mapped
      have all : ∀ f ∈ peerFields Root.nodeOffsets, f.1+f.2≤Layouts.peerSize := by decide
      have small := all _ field
      obtain ⟨i,bound,location⟩ := inside
      refine ⟨(address,Layouts.peerSize),by
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨(id,address),present,rfl⟩,offset+i,
        by dsimp only at small bound ⊢; omega,?_⟩
      rw [location]
      simp only [BitVec.ofNat_add,BitVec.add_assoc]
  obtain ⟨obj,listed,covers⟩ := object
  exact spansApart_sound x.cut.apart listed named covers within

/-- Bytes of the second object are in the arena. -/
theorem secondArena {y : BitVec 64} (inside : InRange (.ofNat 64 base2) 72 y) : L.Arena y :=
  Rollback.kept_arena (live := [base2]) (fun node member => by
    cases List.mem_singleton.mp member; exact x.grown.arena) ⟨base2,List.mem_singleton_self _,inside⟩

theorem solidHeap {y : BitVec 64} (solid : Solid L names base y) : L.Heap y := by
  rcases solid with ⟨span,member,inside⟩|kept
  · exact ⟨span,List.mem_append_left _ member,inside⟩
  · exact Rollback.arena_heap (Rollback.kept_arena x.liveArena kept)

theorem solidOff {y : BitVec 64} (solid : Solid L names base y) : ¬InRange (.ofNat 64 base2) 72 y := by
  intro second
  rcases solid with fixed|⟨node,member,inside⟩
  · exact x.fixedOutside fixed (x.secondArena second)
  · exact objects_apart (Nat.le_of_lt x.top2) (x.liveBound member) (x.freshApart member) second inside

theorem solidT {y : BitVec 64} (solid : Solid L names base y) : t.data.dmem.get? y = a.data.dmem.get? y :=
  x.grown.kept y (solid.elim (fun fixed => .inr (.inl fixed)) (fun kept => .inr (.inr (.inl kept))))

theorem readSolid : ∀ span ∈ readSpans (names.allocated base) Root.nodeOffsets, ∀ y, span.contains y →
    Solid L names base y := by
  intro span member y inside
  rcases List.mem_append.mp member with table|more
  · obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp table
    have same : (names.allocated base).table = L.table := x.cut.table
    rw [same] at inside
    exact .inl ⟨(L.table+offset,size),List.mem_append_left _ (List.mem_map.mpr ⟨(offset,size),field,rfl⟩),inside⟩
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
      obtain ⟨i,bound,location⟩ := inside
      refine .inr ⟨address,live,offset+i,by dsimp only at within bound; unfold nodeSize; omega,?_⟩
      rw [location]
      simp only [BitVec.ofNat_add,BitVec.add_assoc]
    · obtain ⟨⟨id,address⟩,named,mapped⟩ := List.mem_flatMap.mp peer
      obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp mapped
      have same : (names.allocated base).trie.peers = L.peers := x.cut.peers
      rw [same] at named
      exact .inl ⟨(address+offset,size),List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨(id,address),named,List.mem_map.mpr ⟨(offset,size),field,rfl⟩⟩),inside⟩

theorem tableSolid (y : BitVec 64) (inside : InRange (.ofNat 64 names.table) 24 y) : Solid L names base y := by
  obtain ⟨i,bound,location⟩ := inside
  rw [x.cut.table] at location
  have field (offset : Nat) (member : (offset,8) ∈ tableFields) (low : offset ≤ i) (high : i < offset+8) :
      Solid L names base y := by
    refine .inl ⟨(L.table+offset,8),List.mem_append_left _ (List.mem_map.mpr ⟨(offset,8),member,rfl⟩),
      i-offset,by omega,?_⟩
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

/-- The bytes below the stack pointer that a call pushes, as bounds. -/
theorem pushNear {r : UInt64} (same : r = e.data.regs.rsp) {y : BitVec 64}
    (push : InRange (r.toBitVec - 8) 8 y) :
    e.data.regs.rsp.toNat ≤ y.toNat + 48 ∧ y.toNat < e.data.regs.rsp.toNat + 48 := by
  rw [same] at push
  have position := x.frame
  obtain ⟨i,small,location⟩ := push
  have rsp : e.data.regs.rsp.toBitVec.toNat = e.data.regs.rsp.toNat := rfl
  have value : y.toNat = e.data.regs.rsp.toNat - 8 + i := by rw [location]; bv_omega
  omega

/-- A heap byte outside the second object is not written by the internal
node's initialization. -/
theorem untouched {y : BitVec 64} (heap : L.Heap y) (off : ¬InRange (.ofNat 64 base2) 72 y) :
    ¬C1Internal.Writes c t.data.regs.rsp base2 y := by
  have position := x.frame
  have far := x.heapFar heap
  have stackN : t.data.regs.rsp.toNat = e.data.regs.rsp.toNat := by rw [x.stackT]
  rintro (node|saved|push|buffer)
  · exact off node
  · have near := range_nat (by omega) saved
    exact far.1 (by omega)
  · exact far.1 (x.pushNear x.stackT push)
  · exact far.2.2 buffer

theorem valid2 : validate ((names.allocated base).allocated base2) nodeOffsets = .ok () := by
  have position := x.frame
  apply validate_allocate_valid x.fields.allocated (Nat.pos_of_ne_zero x.grown.nonzero) x.grown.aligned x.top2
  · intro span member
    rcases List.mem_append.mp member with node|peer
    · obtain ⟨⟨id,address⟩,named,rfl⟩ := List.mem_map.mp node
      have live : address ∈ liveOf names base := by
        rcases List.mem_append.mp named with old|new
        · exact nodeLive old
        · cases List.mem_singleton.mp new
          exact baseLive
      exact x.grown.fresh address live
    · obtain ⟨⟨id,address⟩,named,rfl⟩ := List.mem_map.mp peer
      have same : (names.allocated base).trie.peers = L.peers := x.cut.peers
      rw [same] at named
      obtain ⟨region,listed,low,high⟩ := x.grown.arena
      have checked := List.all_eq_true.mp (List.all_eq_true.mp x.cut.apart (address,Layouts.peerSize)
        (List.mem_append_right _ (List.mem_map.mpr ⟨(id,address),named,rfl⟩))) region listed
      simp only [Bool.and_eq_true,decide_eq_true_eq,disjointRanges,Bool.or_eq_true] at checked
      unfold nodeSize at high
      simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq]
      change base2+72 ≤ address ∨ address+Layouts.peerSize ≤ base2
      omega
  · obtain ⟨region,listed,low,high⟩ := x.grown.arena
    have checked := List.all_eq_true.mp (List.all_eq_true.mp x.cut.apart (L.table,AllowedipsMutationLayout.tableSize)
      (by simp [objectsOf])) region listed
    simp only [Bool.and_eq_true,decide_eq_true_eq,disjointRanges,Bool.or_eq_true] at checked
    unfold nodeSize at high
    simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq]
    change base2+72 ≤ (names.allocated base).table ∨ (names.allocated base).table+AllowedipsMutationLayout.tableSize ≤ base2
    have same : (names.allocated base).table = L.table := x.cut.table
    rw [same]
    omega

section Connected
variable {u : MachineState} {sel : Nat}
  (k : AtConnect c e t u base base2 child (widthOf family)
    (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)) key sel)
include k

theorem solidU {y : BitVec 64} (solid : Solid L names base y) : u.data.dmem.get? y = t.data.dmem.get? y :=
  (k.frame y (x.untouched (x.solidHeap solid) (x.solidOff solid))).symm

/-- The pending first node at `add+0x338`. -/
theorem pendingU : NodeInit.Pending names e.data (bump d) key cidr pid base u.data.dmem :=
  x.pendingT.frame k.frame
    (fun span member y inside => x.untouched (x.solidHeap (x.readSolid span member y inside))
      (x.solidOff (x.readSolid span member y inside)))
    (fun y inside => x.untouched (x.solidHeap (x.tableSolid y inside)) (x.solidOff (x.tableSolid y inside)))

theorem mappedU : MappedLe e.data.dmem u.data.dmem :=
  x.cmp.held.mapped.trans (x.grown.mapped.trans k.mapped)

/-- An old node decoded at `add+0x338`. -/
theorem oldU {id address : Nat} {node : AipNode} (named : (id,address) ∈ names.trie.nodes)
    (present : (bump d).nodes.get? id = some node) :
    Trie.decodeNode (names.allocated base).trie nodeOffsets u.data.dmem address = .ok (Trie.targetNode node) :=
  (x.pendingU k).old_node x.cut.related.1 named present

/-- An old node's packed parent word is readable. -/
theorem parentWordU {id address : Nat} (named : (id,address) ∈ names.trie.nodes) :
    (u.data.dmem.loadInt (.ofNat 64 (address+48)) 8).isSome = true := by
  obtain ⟨⟨current,actual⟩,_,read⟩ := (reconstruct_fields x.cut.related.1).nodes.left (id,address) named
  unfold Allowedips.decodeNode at read
  obtain ⟨core,_,run⟩ := bind_ok read
  obtain ⟨raw,rawRead,_⟩ := bind_ok run
  exact x.mappedU k _ _ (Option.isSome_of_eq_some (word_loadInt _ _ _ _ _ rawRead))

theorem init : C1Split.InternalInit (names.allocated base) u.data.dmem u.data.dmem base2 key
    (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)) e.data.regs.rbp.toNat := by
  refine ⟨?_,⟨readNat_of_word k.next,?_⟩,⟨fun _ => False,fun _ _ => rfl,fun _ h => h.elim⟩⟩
  · rw [x.extra.width]; exact k.record _
  · rw [Nat.add_assoc]; exact readNat_of_word k.prev

end Connected
end SplitCtx

#print axioms SplitCtx.pendingU
#print axioms SplitCtx.valid2
#print axioms SplitCtx.init
end Binary.Statements.C1.Proof
