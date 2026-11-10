import C1BelowWholeAt

/-! Result C1, work package 3, the split path: the machine-side hypotheses of
the connections at `add+0x338`, common to the parent and root sub-cases,
discharged from the bundle and `AtConnect`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root AllowedipsChild Binary.AllowedipsRelation
open Binary.SplitStage3 Binary.SplitStage3.Path
local instance : Labels := Image.linkedLabels

namespace SplitCtx
variable {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} {c : Context}
  {s : MachineState} {ra : UInt64} {w : World} {d : Device} {family key cidr pid : Nat}
  {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base : Nat}
  {e a t : MachineState} {m : DataMem} {downId child : Nat} {downNode : AipNode}
  {rest : List HiddenRecord} {base2 : Nat}
  (x : SplitCtx fetch L A c s ra w d family key cidr pid stream placed names base e a t m downId child
    downNode rest base2)
  {u : MachineState} {sel : Nat}
  (k : AtConnect c e t u base base2 child (widthOf family)
    (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)) key sel)
include x k

omit x in
theorem r12bv : u.data.regs.r12.toBitVec = .ofNat 64 base2 := by rw [k.r12]; exact UInt64.toBitVec_ofNat' ..
omit x in
theorem r8bv : u.data.regs.r8.toBitVec = .ofNat 64 base := by rw [k.r8]; exact UInt64.toBitVec_ofNat' ..
omit x in
theorem rdibv : u.data.regs.rdi.toBitVec = .ofNat 64 child := by rw [k.rdi]; exact UInt64.toBitVec_ofNat' ..

omit k in
theorem childBound : child + 72 ≤ 2^64 := x.liveBound (nodeLive (base := base) x.named)
omit k in
theorem baseBound : base + 72 ≤ 2^64 := x.liveBound baseLive

omit k in
/-- The byte selector of the internal node is inside the key. -/
theorem indexInside : byteSelector (widthOf family)
    (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)) < widthOf family / 8 :=
  (selector_position _ _ x.wide x.proper).2

omit k in
theorem wideBytes : widthOf family / 8 ≤ 16 := by rcases x.wide with h|h <;> rw [h] <;> decide

/-- Where the four stores of the first two connections fall. -/
theorem connNat {b1 b2 : Nat} (one : b1 < 2) (two : b2 < 2) {y : BitVec 64}
    (written : SplitStage3.Writes u.data.regs.r12.toBitVec u.data.regs.rdi.toBitVec u.data.regs.r8.toBitVec b1 b2 y) :
    (child + 48 ≤ y.toNat ∧ y.toNat < child + 56) ∨ (base2 + 8 ≤ y.toNat ∧ y.toNat < base2 + 24) ∨
    (base + 48 ≤ y.toNat ∧ y.toNat < base + 56) := by
  have top := x.top2
  rw [r12bv k,rdibv k,r8bv k] at written
  rcases written with down|first|leaf|second
  · have bounds := natRange (off := 48) x.childBound (by decide) down
    omega
  · have bounds := natRange (off := 8+8*b1) (Nat.le_of_lt top) (by omega) first
    omega
  · have bounds := natRange (off := 48) x.baseBound (by decide) leaf
    omega
  · have bounds := natRange (off := 8+8*b2) (Nat.le_of_lt top) (by omega) second
    omega

omit k in
/-- The three objects of the first two connections, as kept bytes. -/
theorem keptOf {y : BitVec 64}
    (bounds : (child ≤ y.toNat ∧ y.toNat < child + 72) ∨ (base2 ≤ y.toNat ∧ y.toNat < base2 + 72) ∨
      (base ≤ y.toNat ∧ y.toNat < base + 72)) : Kept (liveOf names base ++ [base2]) y := by
  rcases bounds with down|node|leaf
  · exact ⟨child,List.mem_append_left _ (nodeLive x.named),inObject down.1 down.2⟩
  · exact ⟨base2,List.mem_append_right _ (List.mem_singleton_self _),inObject node.1 node.2⟩
  · exact ⟨base,List.mem_append_left _ baseLive,inObject leaf.1 leaf.2⟩

omit k in
theorem liveArena2 : ∀ node ∈ liveOf names base ++ [base2], InArena L node := by
  intro node member
  rcases List.mem_append.mp member with old|new
  · exact x.liveArena node old
  · cases List.mem_singleton.mp new
    exact x.grown.arena

omit k in
theorem keptHeap {y : BitVec 64} (kept : Kept (liveOf names base ++ [base2]) y) : L.Heap y :=
  Rollback.arena_heap (Rollback.kept_arena x.liveArena2 kept)

/-- A heap byte is not written by the coverage callback after the connections. -/
theorem callFar {y : BitVec 64} (heap : L.Heap y) : ¬CallWrites u.data c y := by
  rintro (push|buffer)
  · exact (x.heapFar heap).1 (x.pushNear k.rsp push)
  · exact (x.heapFar heap).2.2 buffer

omit k in
/-- What reconstruction reads under the twice-extended names is heap. -/
theorem readHeap2 : ∀ span ∈ readSpans ((names.allocated base).allocated base2) nodeOffsets,
    ∀ y, span.contains y → L.Heap y := by
  intro span member y inside
  rcases List.mem_append.mp member with table|more
  · obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp table
    have same : ((names.allocated base).allocated base2).table = L.table := x.cut.table
    rw [same] at inside
    exact fixed_table field inside
  · rcases List.mem_append.mp more with node|peer
    · obtain ⟨⟨id,address⟩,named,mapped⟩ := List.mem_flatMap.mp node
      obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp mapped
      have all : ∀ f ∈ nodeFields Root.nodeOffsets, f.1+f.2≤72 := by decide
      have arena : InArena L address := by
        rcases List.mem_append.mp named with old|new
        · exact x.cut.named_arena old
        · cases List.mem_singleton.mp new
          exact x.grown.arena
      exact arena_heap arena (all _ field) inside
    · obtain ⟨⟨id,address⟩,named,mapped⟩ := List.mem_flatMap.mp peer
      obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp mapped
      have same : ((names.allocated base).allocated base2).trie.peers = L.peers := x.cut.peers
      rw [same] at named
      exact fixed_peer named field inside

omit k in
/-- The internal node's prefix length and the bit chosen for the node below are the mirror's. -/
theorem downFacts : ∀ down, (bump d).nodes.get? downId = some down →
    min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key) =
      min cidr (AllowedipsRelation.common (widthOf family) down.bits key) ∧
    chosen family key cidr downNode = down.bits/2^(widthOf family-1-
      min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key))%2 := by
  intro down present
  cases Option.some.inj (present.symm.trans x.hasDown)
  exact ⟨rfl,queryByte_select _ _ _ x.wide x.proper⟩

/-- The machine entry state of the connections. -/
theorem entryU (same : sel = chosen family key cidr downNode) :
    SplitStage3.Entry u.data sel
      (byteSelector (widthOf family) (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)))
      (7 - min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key) % 8)
      (queryByte (widthOf family) key
        (byteSelector (widthOf family) (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)))) := by
  have top := x.top2
  have fields := Trie.decodeNode_fields (k.record names)
  have inside := x.indexInside
  have bytes := x.wideBytes
  obtain ⟨left,right,lp,rp,_,leftWord,_,rightWord,_⟩ := fields.children
  have leafWords := key_words (x.pendingU k).core
  have leafWidth : (Trie.targetNode (newNode key cidr e.data.regs.rbp.toNat (some pid))).width = widthOf family :=
    x.extra.width
  rw [leafWidth] at leafWords
  have leafByte := queryByte_read _ _ _ _ _ x.wide inside leafWords
  rw [BitVec.ofNat_add] at leafByte
  have indexWord := word_loadInt _ _ _ _ _ fields.byteSelector
  have shiftWord := word_loadInt _ _ _ _ _ fields.bitSelector
  have leftLoad := word_loadInt _ _ _ _ _ leftWord
  have rightLoad := word_loadInt _ _ _ _ _ rightWord
  rw [BitVec.ofNat_add] at indexWord shiftWord leftLoad
  have rightAddress : BitVec.ofNat 64 (base2+nodeOffsets.children+8) = BitVec.ofNat 64 base2 + 16 := by
    rw [Nat.add_assoc,BitVec.ofNat_add]; rfl
  rw [rightAddress] at rightLoad
  have downParent := x.parentWordU k x.named
  rw [BitVec.ofNat_add] at downParent
  have leafParent := x.mappedU k _ _ (Option.isSome_of_eq_some
    (word_loadInt _ _ _ _ _ (x.fields.zero_word "node.parent" 48 8 (by decide))))
  rw [BitVec.ofNat_add] at leafParent
  have fresh := x.freshApart (nodeLive (base := base) x.named)
  have first := x.firstApart x.named
  exact {
    directionBound := by rw [same]; unfold chosen selected; omega
    rax := k.rax
    rdx := k.rdx
    rcx := k.rcx
    indexRead := by rw [r12bv k]; exact indexWord
    shiftRead := by rw [r12bv k]; exact shiftWord
    byteRead := by rw [r8bv k]; exact leafByte
    indexBound := by omega
    shiftBound := by omega
    byteBound := queryByte_bound _ _ _
    downParentMapped := by rw [rdibv k]; exact downParent
    leftMapped := by rw [r12bv k]; exact Option.isSome_of_eq_some leftLoad
    rightMapped := by rw [r12bv k]; exact Option.isSome_of_eq_some rightLoad
    newParentMapped := by rw [r8bv k]; exact leafParent
    nodeDown := by
      rw [r12bv k,rdibv k]
      exact fun y node => objects_apart (Nat.le_of_lt top) x.childBound fresh node
    nodeNew := by
      rw [r12bv k,r8bv k]
      exact fun y node => objects_apart (Nat.le_of_lt top) x.baseBound (x.freshApart baseLive) node
    downNew := by
      rw [rdibv k,r8bv k]
      exact fun y down => objects_apart x.childBound x.baseBound first.symm down }

end SplitCtx

#print axioms SplitCtx.entryU
#print axioms SplitCtx.readHeap2
end Binary.Statements.C1.Proof
