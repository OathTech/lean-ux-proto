import C1TrunkExits
import AllowedipsAllocationValidate
import AllowedipsRootBoundaryResources
/-! Result C1, package 2: the object a successful allocation hands out, as
the landed boundaries want it: the extended interpretation validates, and
the root initialization's write spans lie in the heap. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- Nonempty spans with no byte in common are apart in the executable sense. -/
theorem apart_of_bytes (X Y : List Pair.Span)
    (hx : ∀ a ∈ X, a.1 + a.2 ≤ 2^64 ∧ 0 < a.2) (hy : ∀ b ∈ Y, b.1 + b.2 ≤ 2^64 ∧ 0 < b.2)
    (sep : ∀ a ∈ X, ∀ b ∈ Y, ∀ x, a.contains x → ¬b.contains x) : spansApart X Y = true := by
  unfold spansApart
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  obtain ⟨ba,pa⟩ := hx a ha
  obtain ⟨bb,pb⟩ := hy b hb
  have dis : a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1 := by
    by_cases h : a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1
    · exact h
    · exfalso
      obtain ⟨m,m1,m2,m3,m4⟩ : ∃ m, a.1 ≤ m ∧ b.1 ≤ m ∧ m < a.1 + a.2 ∧ m < b.1 + b.2 :=
        ⟨max a.1 b.1,by omega,by omega,by omega,by omega⟩
      apply sep a ha b hb (.ofNat 64 m)
      · exact ⟨m - a.1,by omega,by rw [← BitVec.ofNat_add]; congr 1; omega⟩
      · exact ⟨m - b.1,by omega,by rw [← BitVec.ofNat_add]; congr 1; omega⟩
  simp only [disjointRanges, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  exact ⟨⟨ba,bb⟩,dis⟩

/-- An object inside the arena is apart from the table and from every peer. -/
theorem arena_object_apart {L : Statements.C1.Layout}
    (objectsApart : spansApart ([(L.table,AllowedipsMutationLayout.tableSize)] ++
      L.peers.map fun (_,a) => (a,Layouts.peerSize)) L.arena = true)
    {n : Nat} (arena : InArena L n) (object : Pair.Span)
    (member : object ∈ [(L.table,AllowedipsMutationLayout.tableSize)] ++
      L.peers.map fun (_,a) => (a,Layouts.peerSize)) :
    disjointRanges n 72 object.1 object.2 = true := by
  obtain ⟨span,isArena,low,high⟩ := arena
  have checked := List.all_eq_true.mp (List.all_eq_true.mp objectsApart object member) span isArena
  simp only [disjointRanges, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at checked ⊢
  unfold nodeSize at high
  omega

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- What a successful allocation gives, for the landed boundaries. -/
structure Object (L : Statements.C1.Layout) (names : Allowedips.Names) (n : Nat) : Prop where
  positive : 0 < n
  aligned : n % 8 = 0
  top : n + 72 < 2^64
  arena : InArena L n
  valid : validate (names.allocated n) Root.nodeOffsets = .ok ()

theorem object_of_result (below : NodeBelowTop) (premises : Premises fetch L A)
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {t : MachineState} {record : HiddenRecord} {rest : List HiddenRecord}
    (result : AllocResult L A (names.trie.nodes.map (·.2)) record rest t)
    (ok : record.bytes.head? = some 1) :
    Object L names t.data.regs.rax.toNat ∧ readNat t t.data.regs.rax.toNat nodeSize = .ok 0 ∧
    A.Idle t.data.dmem (names.trie.nodes.map (·.2) ++ [t.data.regs.rax.toNat]) rest := by
  have top := below fetch L A premises _ record rest t result ok
  obtain ⟨nonzero,aligned,arena,apartLive,zero,idle⟩ := result.2 ok
  refine ⟨⟨by omega,aligned,top,arena,?_⟩,zero,idle⟩
  apply validate_allocate trunk.relatedA (by omega) aligned top
  · intro span member
    rcases List.mem_append.mp member with node | peer
    · obtain ⟨named,isNode,rfl⟩ := List.mem_map.mp node
      exact apartLive named.2 (List.mem_map.mpr ⟨named,isNode,rfl⟩)
    · obtain ⟨named,isPeer,rfl⟩ := List.mem_map.mp peer
      rw [trunk.peers] at isPeer
      exact arena_object_apart trunk.objectsApart arena _
        (List.mem_append_right _ (List.mem_map.mpr ⟨named,isPeer,rfl⟩))
  · rw [trunk.table]
    exact arena_object_apart trunk.objectsApart arena _
      (List.mem_append_left _ (List.mem_singleton.mpr rfl))

theorem Object.inArena (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {n : Nat} (object : Object L names n) :
    ∀ node ∈ (names.allocated n).trie.nodes,
      ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2 := by
  intro node member
  rcases List.mem_append.mp member with old | new
  · exact trunk.inArena node old
  · rw [List.mem_singleton.mp new]
    exact object.arena

/-- The arena is apart from the table and from every peer object. -/
theorem arena_not_object {L : Statements.C1.Layout}
    (objectsApart : spansApart ([(L.table,AllowedipsMutationLayout.tableSize)] ++
      L.peers.map fun (_,a) => (a,Layouts.peerSize)) L.arena = true)
    (object : Pair.Span)
    (member : object ∈ [(L.table,AllowedipsMutationLayout.tableSize)] ++
      L.peers.map fun (_,a) => (a,Layouts.peerSize))
    (x : BitVec 64) (inside : object.contains x) : ¬L.Arena x := by
  rintro ⟨span,isArena,inArena⟩
  exact spansApart_sound objectsApart member isArena inside inArena

/-- The root initialization's write spans: nonempty and not wrapping, in the
heap, apart from the sequence word, and inside the arena only within a node
that stays handed out. -/
theorem Object.writeSpans (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {n : Nat} (object : Object L names n) (v : MachineData) (rbx : v.regs.rbx.toNat = n) :
    ∀ span ∈ Root.writeSpans (names.allocated n) v,
      (span.1 + span.2 ≤ 2^64 ∧ 0 < span.2) ∧ (∀ x, span.contains x → L.Heap x) ∧
      (∀ x, span.contains x → ¬InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 x) ∧
      (∀ x, span.contains x → L.Arena x → Kept (names.trie.nodes.map (·.2) ++ [n]) x) := by
  obtain ⟨tableTop,tableApart⟩ := Root.table_valid_geometry object.valid
  have tableEq : (names.allocated n).table = L.table := trunk.table
  rw [tableEq] at tableTop tableApart
  have trieValid : Trie.validate (names.allocated n).trie Root.nodeOffsets = .ok () := by
    have valid := object.valid
    unfold validate at valid
    obtain ⟨_,trieValid,_⟩ := bind_ok valid
    exact trieValid
  have ranges := trie_validate_ranges trieValid
  have inArena := object.inArena trunk
  have seqValue : AllowedipsMutationLayout.seq = 16 := rfl
  have seqSpan (x : BitVec 64) (h : InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 x) :
      Pair.Span.contains (L.table+AllowedipsMutationLayout.seq,8) x := h
  have nodeCase (base : Nat) (named : ∃ node ∈ (names.allocated n).trie.nodes, node.2 = base)
      (off size : Nat) (fits : off + size ≤ 72) (positive : 0 < size) :
      (base + off + size ≤ 2^64 ∧ 0 < size) ∧
      (∀ x, Pair.Span.contains (base+off,size) x → L.Heap x) ∧
      (∀ x, Pair.Span.contains (base+off,size) x →
        ¬InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 x) ∧
      (∀ x, Pair.Span.contains (base+off,size) x → L.Arena x →
        Kept (names.trie.nodes.map (·.2) ++ [n]) x) := by
    obtain ⟨node,isNode,rfl⟩ := named
    have allocation : (node.2,Root.nodeOffsets.nodeSize) ∈ allocations (names.allocated n) Root.nodeOffsets :=
      List.mem_append_left _ (List.mem_map.mpr ⟨node,isNode,rfl⟩)
    have bound := (ranges _ allocation).2
    have apart := tableApart _ allocation
    have size72 : Root.nodeOffsets.nodeSize = 72 := rfl
    simp only [disjointRanges, Bool.or_eq_true, decide_eq_true_eq, size72] at apart bound
    obtain ⟨home,isArena,low,high⟩ := inArena node isNode
    unfold nodeSize at high
    refine ⟨⟨by omega,positive⟩,fun x inside => ?_,fun x inside h => ?_,fun x inside _ => ?_⟩
    · exact arena_heap x ⟨home,isArena,span_within _ _ _ _ (by omega) (by omega) x inside⟩
    · exact nat_apart (node.2+off,size) (L.table+AllowedipsMutationLayout.seq,8)
        (by show node.2+off+size ≤ 2^64; omega) (by simp only [seqValue]; omega)
        (by show node.2+off+size ≤ L.table+AllowedipsMutationLayout.seq ∨
              L.table+AllowedipsMutationLayout.seq+8 ≤ node.2+off
            simp only [seqValue]; omega) x inside (seqSpan x h)
    · refine ⟨node.2,?_,span_within _ _ _ _ (by omega) (by unfold nodeSize; omega) x inside⟩
      have member : node.2 ∈ (names.allocated n).trie.nodes.map (·.2) := List.mem_map.mpr ⟨node,isNode,rfl⟩
      simpa [Names.allocated] using member
  intro span member
  simp only [Root.writeSpans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl) | node) | peer
  · rw [rbx]
    have h := nodeCase n ⟨(names.nextNode,n),List.mem_append_right _ (List.mem_singleton.mpr rfl),rfl⟩
      0 72 (by omega) (by omega)
    exact h
  · have inTable (x : BitVec 64) (inside : Pair.Span.contains
        ((names.allocated n).table+(if (v.regs.rbp.toNat == 32) = true then 0 else 8),8) x) :
        Pair.Span.contains (L.table,AllowedipsMutationLayout.tableSize) x := by
      rw [tableEq] at inside
      exact span_within _ _ _ _ (by omega) (by show _ ≤ L.table + 24; split <;> omega) x inside
    refine ⟨⟨?_,Nat.zero_lt_succ _⟩,fun x inside => ?_,fun x inside h => ?_,fun x inside arena => ?_⟩
    · show (names.allocated n).table + _ + 8 ≤ 2^64
      rw [tableEq]
      split <;> omega
    · rw [tableEq] at inside
      refine ⟨_,?_,inside⟩
      by_cases four : (v.regs.rbp.toNat == 32) = true <;>
        simp [four, Layout.heap, Layout.fixed, tableFields, AllowedipsMutationLayout.root4,
          AllowedipsMutationLayout.root6]
    · rw [tableEq] at inside
      exact nat_apart _ (L.table+AllowedipsMutationLayout.seq,8)
        (by show L.table + _ + 8 ≤ 2^64; split <;> omega) (by simp only [seqValue]; omega)
        (by show L.table + _ + 8 ≤ L.table+AllowedipsMutationLayout.seq ∨ _
            simp only [seqValue]; split <;> omega) x inside (seqSpan x h)
    · exact absurd arena (arena_not_object trunk.objectsApart _
        (List.mem_append_left _ (List.mem_singleton.mpr rfl)) x (inTable x inside))
  · obtain ⟨named,isNode,rfl⟩ := List.mem_map.mp node
    exact nodeCase named.2 ⟨named,isNode,rfl⟩ 56 16 (by omega) (by omega)
  · obtain ⟨named,isPeer,rfl⟩ := List.mem_map.mp peer
    have allocation : (named.2,Layouts.peerSize) ∈ allocations (names.allocated n) Root.nodeOffsets :=
      List.mem_append_right _ (List.mem_map.mpr ⟨named,isPeer,rfl⟩)
    have bound := (ranges _ allocation).2
    have apart := tableApart _ allocation
    have size : Layouts.peerSize = 1520 := rfl
    simp only [disjointRanges, Bool.or_eq_true, decide_eq_true_eq, size] at apart bound
    have isPeer' : named ∈ L.peers := trunk.peers ▸ isPeer
    refine ⟨⟨by show named.2 + 1096 + 16 ≤ 2^64; omega,Nat.zero_lt_succ _⟩,fun x inside => ?_,
      fun x inside h => ?_,fun x inside arena => ?_⟩
    · obtain ⟨i,hi,eq⟩ := inside
      by_cases first : i < 8
      · exact ⟨(named.2+1096,8),List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨named,isPeer',List.mem_map.mpr ⟨(1096,8),by decide,rfl⟩⟩)),⟨i,first,eq⟩⟩
      · refine ⟨(named.2+1104,8),List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨named,isPeer',List.mem_map.mpr ⟨(1104,8),by decide,rfl⟩⟩)),
          ⟨i-8,by omega,?_⟩⟩
        rw [eq, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
        congr 1
        show named.2 + 1096 + i = named.2 + 1104 + (i - 8)
        omega
    · exact nat_apart (named.2+1096,16) (L.table+AllowedipsMutationLayout.seq,8)
        (by show named.2+1096+16 ≤ 2^64; omega) (by simp only [seqValue]; omega)
        (by show named.2+1096+16 ≤ L.table+AllowedipsMutationLayout.seq ∨
              L.table+AllowedipsMutationLayout.seq+8 ≤ named.2+1096
            simp only [seqValue]; omega) x inside (seqSpan x h)
    · exact absurd arena (arena_not_object trunk.objectsApart (named.2,Layouts.peerSize)
        (List.mem_append_right _ (List.mem_map.mpr ⟨named,isPeer',rfl⟩)) x
        (span_within _ _ _ _ (by omega) (by show named.2+1096+16 ≤ named.2+1520; omega) x inside))
end

#print axioms apart_of_bytes
#print axioms object_of_result
#print axioms Object.writeSpans
end C1Trunk
