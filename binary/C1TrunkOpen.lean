import C1TrunkApart
import AllowedipsRootMetadata
import AllowedipsAllocatedFacts
/-! Result C1, package 2: the invariant's interpretation against the caller's
conditions (its read spans lie in the heap; they are apart from the sequence
word), both wrappers as one entering theorem, and the trial's entry assertion
for `add`'s failure exits derived from them. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem span_within (b n B N : Nat) (h1 : B ≤ b) (h2 : b + n ≤ B + N) (x : BitVec 64)
    (inside : InRange (.ofNat 64 b) n x) : InRange (.ofNat 64 B) N x := by
  obtain ⟨i,hi,eq⟩ := inside
  refine ⟨b-B+i,by omega,?_⟩
  rw [eq, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  omega

theorem nat_apart (l r : Pair.Span) (bl : l.1+l.2 ≤ 2^64) (br : r.1+r.2 ≤ 2^64)
    (apart : l.1+l.2 ≤ r.1 ∨ r.1+r.2 ≤ l.1) (a : BitVec 64) (la : l.contains a) : ¬r.contains a := by
  intro ra
  have h1 := Span.location bl la
  have h2 := Span.location br ra
  omega

theorem nodeFields_inside : ∀ p ∈ nodeFields Root.nodeOffsets, p.1+p.2 ≤ 72 := by decide
theorem peerFields_inside : ∀ p ∈ peerFields Root.nodeOffsets, p.1+p.2 ≤ 1520 := by decide

/-- Every byte the relation reads lies in the layout's heap. -/
theorem read_heap {L : Statements.C1.Layout} {names : Allowedips.Names}
    (table : names.table = L.table) (peers : names.trie.peers = L.peers)
    (arena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2) :
    ∀ span ∈ readSpans names Root.nodeOffsets, ∀ a, span.contains a → L.Heap a := by
  intro span member a inside
  simp only [readSpans, List.mem_append] at member
  rcases member with tableField | nodeField | peerField
  · rw [table] at tableField
    exact ⟨span,List.mem_append_left _ (List.mem_append_left _ tableField),inside⟩
  · obtain ⟨node,named,field⟩ := List.mem_flatMap.mp nodeField
    obtain ⟨slot,present,equal⟩ := List.mem_map.mp field
    obtain ⟨home,isArena,low,high⟩ := arena node named
    have fits := nodeFields_inside slot present
    subst equal
    refine ⟨home,List.mem_append_right _ isArena,?_⟩
    exact span_within _ _ _ _ (by omega) (by unfold nodeSize at high; omega) a inside
  · rw [peers] at peerField
    exact ⟨span,List.mem_append_left _ (List.mem_append_right _ peerField),inside⟩

theorem kept_read {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {span : Pair.Span}
    (member : span ∈ keptSpans names o) : span ∈ readSpans names o := by
  simp only [keptSpans, readSpans, List.mem_append] at member ⊢
  rcases member with table | rest
  · left
    simp only [tableFields, List.map_cons, List.map_nil]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at table ⊢
    rcases table with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · exact .inr rest

/-- The read spans other than the sequence word are apart from it. -/
theorem kept_seq_apart {names : Allowedips.Names}
    (valid : validate names Root.nodeOffsets = .ok ()) :
    ∀ span ∈ keptSpans names Root.nodeOffsets, ∀ a, span.contains a →
      ¬InRange (.ofNat 64 (names.table+AllowedipsMutationLayout.seq)) 8 a := by
  obtain ⟨tableTop,tableApart⟩ := Root.table_valid_geometry valid
  have trieValid : Trie.validate names.trie Root.nodeOffsets = .ok () := by
    unfold validate at valid
    obtain ⟨_,trieValid,_⟩ := bind_ok valid
    exact trieValid
  have ranges := trie_validate_ranges trieValid
  intro span member a inside
  have target : Pair.Span.contains (names.table+AllowedipsMutationLayout.seq,8) a →
      InRange (.ofNat 64 (names.table+AllowedipsMutationLayout.seq)) 8 a := fun h => h
  intro seqAt
  revert inside
  simp only [keptSpans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  have seqValue : AllowedipsMutationLayout.seq = 16 := rfl
  rcases member with (rfl | rfl) | nodeField | peerField
  · intro inside
    exact nat_apart _ (names.table+AllowedipsMutationLayout.seq,8)
      (by simp only [AllowedipsMutationLayout.root4]; omega) (by simp only [seqValue]; omega)
      (by simp only [AllowedipsMutationLayout.root4, seqValue]; omega) a inside seqAt
  · intro inside
    exact nat_apart _ (names.table+AllowedipsMutationLayout.seq,8)
      (by simp only [AllowedipsMutationLayout.root6]; omega) (by simp only [seqValue]; omega)
      (by simp only [AllowedipsMutationLayout.root6, seqValue]; omega) a inside seqAt
  · obtain ⟨node,named,field⟩ := List.mem_flatMap.mp nodeField
    obtain ⟨slot,present,equal⟩ := List.mem_map.mp field
    have fits := nodeFields_inside slot present
    have allocation : (node.2,Root.nodeOffsets.nodeSize) ∈ allocations names Root.nodeOffsets :=
      List.mem_append_left _ (List.mem_map.mpr ⟨node,named,rfl⟩)
    have apart := tableApart _ allocation
    have bound := (ranges _ (List.mem_append_left _ (List.mem_map.mpr ⟨node,named,rfl⟩))).2
    have size : Root.nodeOffsets.nodeSize = 72 := rfl
    simp only [disjointRanges, Bool.or_eq_true, decide_eq_true_eq, size] at apart bound
    subst equal
    intro inside
    exact nat_apart _ (names.table+AllowedipsMutationLayout.seq,8)
      (by show node.2+slot.1+slot.2 ≤ 2^64; omega) (by simp only [seqValue]; omega)
      (by show node.2+slot.1+slot.2 ≤ names.table+AllowedipsMutationLayout.seq ∨
            names.table+AllowedipsMutationLayout.seq+8 ≤ node.2+slot.1
          simp only [seqValue]; omega) a inside seqAt
  · obtain ⟨peer,named,field⟩ := List.mem_flatMap.mp peerField
    obtain ⟨slot,present,equal⟩ := List.mem_map.mp field
    have fits := peerFields_inside slot present
    have allocation : (peer.2,Layouts.peerSize) ∈ allocations names Root.nodeOffsets :=
      List.mem_append_right _ (List.mem_map.mpr ⟨peer,named,rfl⟩)
    have apart := tableApart _ allocation
    have bound := (ranges _ (List.mem_append_right _ (List.mem_map.mpr ⟨peer,named,rfl⟩))).2
    have size : Layouts.peerSize = 1520 := rfl
    simp only [disjointRanges, Bool.or_eq_true, decide_eq_true_eq, size] at apart bound
    subst equal
    intro inside
    exact nat_apart _ (names.table+AllowedipsMutationLayout.seq,8)
      (by show peer.2+slot.1+slot.2 ≤ 2^64; omega) (by simp only [seqValue]; omega)
      (by show peer.2+slot.1+slot.2 ≤ names.table+AllowedipsMutationLayout.seq ∨
            names.table+AllowedipsMutationLayout.seq+8 ≤ peer.2+slot.1
          simp only [seqValue]; omega) a inside seqAt

/-- The sequence word's address as the wrapper computes it. -/
theorem seq_address (x : UInt64) (table : Nat) (held : x.toNat = table) :
    x.toBitVec + 16 = .ofNat 64 (table+AllowedipsMutationLayout.seq) := by
  have e : BitVec.ofNat 64 x.toNat = x.toBitVec := by
    show BitVec.ofNat 64 x.toBitVec.toNat = x.toBitVec
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [← held, BitVec.ofNat_add, e]
  rfl

/-- Both wrappers: entry to `add`'s entry. -/
theorem enter (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    {c : Context} {s : MachineData} {seq : BitVec 64} (caller : Caller c s seq)
    (v4 : Bool) (key : Nat)
    (keyAt : Binary.Allowedips.NetworkKey s.dmem s.regs.rsi.toBitVec (if v4 then 32 else 128) key)
    (keyStack : ∀ a, InRange s.regs.rsi.toBitVec (if v4 then 4 else 16) a →
      ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 200 a)
    (keyBuffer : ∀ a, InRange s.regs.rsi.toBitVec (if v4 then 4 else 16) a → ¬c.writes a)
    (keySeq : ∀ a, InRange s.regs.rsi.toBitVec (if v4 then 4 else 16) a →
      ¬InRange (s.regs.rdi.toBitVec+16) 8 a) :
    Eventually (instructionStep fetch) (fun t => t.pc = Add.entry ∧ AtAdd c s seq v4 key t.data)
      ⟨s,if v4 then Insert4.entry else Insert6.entry⟩ := by
  cases v4
  · obtain ⟨high,low,wordHigh,wordLow,value⟩ : ∃ high low : BitVec 64,
        s.dmem.loadInt s.regs.rsi.toBitVec 8 = some (high.toNat : Int) ∧
        s.dmem.loadInt (s.regs.rsi.toBitVec+8) 8 = some (low.toNat : Int) ∧
        (Binary.Allowedips.swap64 high).toNat*2^64+(Binary.Allowedips.swap64 low).toNat = key := by
      simpa [Binary.Allowedips.NetworkKey] using keyAt
    rw [← value]
    exact enter6 fetch decoder tracePc caller high low wordHigh wordLow keyStack keyBuffer keySeq
  · obtain ⟨word,wordAt,value⟩ : ∃ word : BitVec 32,
        s.dmem.loadInt s.regs.rsi.toBitVec 4 = some (word.toNat : Int) ∧
        (Binary.Allowedips.swap32 word).toNat = key := by
      simpa [Binary.Allowedips.NetworkKey] using keyAt
    rw [← value]
    exact enter4 fetch decoder tracePc caller word wordAt keyStack keyBuffer keySeq

#print axioms read_heap
#print axioms kept_seq_apart
#print axioms enter
end C1Trunk
