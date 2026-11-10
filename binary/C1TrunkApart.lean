import C1TrunkLeave
/-! Result C1, package 2: the separations the caller's conditions give, as
byte-level propositions. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem cover_sub {xs ys : List Pair.Span} {P : BitVec 64 → Prop} (sub : ∀ x ∈ xs, x ∈ ys)
    (cover : Covers xs P) : Covers ys P := by
  intro a h
  obtain ⟨span,member,inside⟩ := cover a h
  exact ⟨span,sub span member,inside⟩

theorem services_cover (c : Context) : Covers (Trie.callServices c) c.bytes := by
  intro a read
  obtain ⟨span,member,inside⟩ := Trie.readSpans_cover read
  exact ⟨span,List.mem_append_left _ (List.mem_append_left _ member),inside⟩

theorem buffers_cover (c : Context) : Covers (Trie.callBuffers c) c.writes := by
  intro a write
  obtain ⟨span,member,inside⟩ := Trie.writeSpans_cover write
  exact ⟨span,List.mem_append_left _ member,inside⟩

theorem metadata_cover (c : Context) : Covers (Trie.callMetadata c) c.metadataBytes := by
  intro a read
  obtain ⟨span,member,inside⟩ := Trie.metadataSpans_cover read
  exact ⟨span,List.mem_append_left _ (List.mem_append_left _ member),inside⟩

theorem heap_cover (L : Statements.C1.Layout) : Covers L.heap L.Heap := fun _ h => h

theorem own_spans (s : MachineState) (W : Nat) (query : Pair.Span) :
    callerSpans s W query true =
      [((s.data.regs.rsp.toBitVec - .ofNat 64 W).toNat, W+8), query, (cacheWord,8)] := rfl

/-- Byte-level separation at an insertion's entry. `n` is the address's size. -/
structure Separate (L : Statements.C1.Layout) (c : Context) (s : MachineData) (W n : Nat) : Prop where
  room : W ≤ s.regs.rsp.toNat
  top : s.regs.rsp.toNat + 8 ≤ 2^64
  heapStack : ∀ a, L.Heap a → ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 W) (W+8) a
  heapBytes : ∀ a, L.Heap a → ¬c.bytes a
  heapWrites : ∀ a, L.Heap a → ¬c.writes a
  heapQuery : ∀ a, L.Heap a → ¬InRange s.regs.rsi.toBitVec n a
  heapCache : ∀ a, L.Heap a → ¬InRange (.ofNat 64 cacheWord) 8 a
  bytesStack : ∀ a, c.bytes a → ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 W) (W+8) a
  writesMetadata : ∀ a, c.writes a → ¬c.metadataBytes a
  writesPreempt : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a
  writesQuery : ∀ a, c.writes a → ¬InRange s.regs.rsi.toBitVec n a
  writesCache : ∀ a, c.writes a → ¬InRange (.ofNat 64 cacheWord) 8 a
  stackQuery : ∀ a, InRange (s.regs.rsp.toBitVec - .ofNat 64 W) W a → ¬InRange s.regs.rsi.toBitVec n a
  stackCache : ∀ a, InRange (s.regs.rsp.toBitVec - .ofNat 64 W) W a →
    ¬InRange (.ofNat 64 cacheWord) 8 a

theorem FrameFacts.separate {L : Statements.C1.Layout} {c : Context} {s : MachineState} {ra : UInt64}
    {W n : Nat} (facts : FrameFacts L c s ra W (s.data.regs.rsi.toNat, n)) :
    Separate L c s.data W n := by
  have heapApart := facts.heapApart
  have serviceStack : spansApart (Trie.callServices c)
      [((s.data.regs.rsp.toBitVec - .ofNat 64 W).toNat, W+8)] = true := facts.serviceStack
  have bufferApart := facts.bufferApart
  have callerApart := facts.callerApart
  rw [own_spans] at heapApart bufferApart callerApart
  have stackCover : Covers [((s.data.regs.rsp.toBitVec - .ofNat 64 W).toNat, W+8)]
      (InRange (s.data.regs.rsp.toBitVec - .ofNat 64 W) (W+8)) := Covers.range _ _
  have lowCover : Covers [((s.data.regs.rsp.toBitVec - .ofNat 64 W).toNat, W)]
      (InRange (s.data.regs.rsp.toBitVec - .ofNat 64 W) W) := Covers.range _ _
  have queryCover : Covers [(s.data.regs.rsi.toNat, n)] (InRange s.data.regs.rsi.toBitVec n) :=
    Covers.range _ _
  have cacheCover : Covers [(cacheWord,8)] (InRange (.ofNat 64 cacheWord) 8) :=
    fun a h => ⟨_,List.mem_singleton.mpr rfl,h⟩
  have bound : (s.data.regs.rsp.toBitVec - .ofNat 64 W).toNat + (W+8) ≤ 2^64 := by
    have member : (L.table+AllowedipsMutationLayout.seq,8) ∈ L.heap := by
      simp [Layout.heap, Layout.fixed, tableFields]
    have checked := List.all_eq_true.mp (List.all_eq_true.mp heapApart _ member)
      ((s.data.regs.rsp.toBitVec - .ofNat 64 W).toNat, W+8) (by simp)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1.2
  have lt := s.data.regs.rsp.toNat_lt
  have value : (s.data.regs.rsp.toBitVec - .ofNat 64 W).toNat =
      (2^64 - W % 2^64 + s.data.regs.rsp.toNat) % 2^64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    rfl
  rw [value] at bound
  refine {
    room := by omega
    top := by omega
    heapStack := spansApart_disjoint heapApart (heap_cover L)
      (cover_sub (by simp) stackCover)
    heapBytes := spansApart_disjoint heapApart (heap_cover L)
      (cover_sub (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) (services_cover c))
    heapWrites := spansApart_disjoint heapApart (heap_cover L)
      (cover_sub (fun _ h => List.mem_append_right _ h) (buffers_cover c))
    heapQuery := spansApart_disjoint heapApart (heap_cover L) (cover_sub (by simp) queryCover)
    heapCache := spansApart_disjoint heapApart (heap_cover L) (cover_sub (by simp) cacheCover)
    bytesStack := spansApart_disjoint serviceStack (services_cover c) stackCover
    writesMetadata := spansApart_disjoint bufferApart (buffers_cover c)
      (cover_sub (fun _ h => List.mem_append_left _ (List.mem_append_right _ h)) (metadata_cover c))
    writesPreempt := spansApart_disjoint bufferApart (buffers_cover c)
      (cover_sub (fun _ h => List.mem_append_right _ h) (Covers.range preemptCountAddress 4))
    writesQuery := spansApart_disjoint bufferApart (buffers_cover c) (cover_sub (by simp) queryCover)
    writesCache := spansApart_disjoint bufferApart (buffers_cover c) (cover_sub (by simp) cacheCover)
    stackQuery := spansApart_disjoint callerApart lowCover (cover_sub (by simp) queryCover)
    stackCache := spansApart_disjoint callerApart lowCover (cover_sub (by simp) cacheCover) }

#print axioms FrameFacts.separate
end C1Trunk
