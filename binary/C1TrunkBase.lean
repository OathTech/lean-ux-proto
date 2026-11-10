import C1TrunkOpen
/-! Result C1, package 2: at `add`'s entry, the trial's entry assertion for
the failure exits, derived from the invariant and the caller's conditions;
and the wrapper's epilogue stated against `AtAdd`. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem sub_sub_ofNat (sp : BitVec 64) (m n : Nat) :
    sp - .ofNat 64 m - .ofNat 64 n = sp - .ofNat 64 (m+n) := by
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]

theorem related_valid {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {d : Device}
    (related : Allowedips.Corresponds names o m d) : validate names o = .ok () := by
  unfold Allowedips.Corresponds Allowedips.reconstruct at related
  obtain ⟨_,valid,_⟩ := bind_ok related
  exact valid

/-- The frame size of a wrapper with the callee's return word. -/
def frameSize (v4 : Bool) : Nat := if v4 then 48 else 56

theorem frameSize_range (v4 : Bool) : 48 ≤ frameSize v4 ∧ frameSize v4 ≤ 56 := by
  cases v4 <;> decide

theorem AtAdd.stackAt {c : Context} {s a : MachineData} {seq : BitVec 64} {v4 : Bool} {key : Nat}
    (atAdd : AtAdd c s seq v4 key a) :
    a.regs.rsp.toBitVec = s.regs.rsp.toBitVec - .ofNat 64 (frameSize v4) := by
  rw [atAdd.stack]
  cases v4 <;> rfl

theorem AtAdd.frameAt {c : Context} {s a : MachineData} {seq : BitVec 64} {v4 : Bool} {key : Nat}
    (atAdd : AtAdd c s seq v4 key a) :
    EqualOutside (fun x =>
      InRange (s.regs.rsp.toBitVec - .ofNat 64 (frameSize v4)) (frameSize v4) x ∨
      InRange (s.regs.rdi.toBitVec+16) 8 x ∨ c.writes x) s.dmem a.dmem := atAdd.frame

/-- The relation at `add`'s entry, against the mirror's device with the
sequence advanced. -/
theorem related_at_add {L : Statements.C1.Layout} {c : Context} {s a : MachineData} {seq : BitVec 64}
    {v4 : Bool} {key : Nat} {names : Allowedips.Names} {d : Device} {W n : Nat} (wide : 200 ≤ W)
    (sep : Separate L c s W n)
    (table : names.table = L.table) (peers : names.trie.peers = L.peers)
    (arena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2)
    (rdi : s.regs.rdi.toNat = L.table)
    (seqWord : s.dmem.loadInt (s.regs.rdi.toBitVec+16) 8 = some (seq.toNat : Int))
    (related : Allowedips.Corresponds names Root.nodeOffsets s.dmem d)
    (shape : Allowedips.heap names (Allowedips.target d) s.dmem = .ok ())
    (atAdd : AtAdd c s seq v4 key a) :
    Allowedips.Corresponds names Root.nodeOffsets a.dmem (bump d) ∧
    Allowedips.heap names (Allowedips.target (bump d)) a.dmem = .ok () := by
  have fs := frameSize_range v4
  have address := seq_address s.regs.rdi names.table (rdi.trans table.symm)
  have valid := related_valid related
  have keptApart : ∀ span ∈ keptSpans names Root.nodeOffsets, ∀ x, span.contains x →
      ¬(InRange (s.regs.rsp.toBitVec - .ofNat 64 (frameSize v4)) (frameSize v4) x ∨
        InRange (s.regs.rdi.toBitVec+16) 8 x ∨ c.writes x) := by
    intro span member x inside written
    have inHeap := read_heap table peers arena span (kept_read member) x inside
    rcases written with h | h | h
    · exact sep.heapStack x inHeap (below_sub _ _ _ W (W+8) (by omega) (by omega) x h)
    · rw [address] at h
      exact kept_seq_apart valid span member x inside h
    · exact sep.heapWrites x inHeap h
  have seqBefore := seqWord
  have seqAfter := atAdd.seqWord
  rw [address] at seqBefore seqAfter
  refine ⟨reconstruct_bump seq related atAdd.frameAt keptApart seqBefore seqAfter,?_⟩
  rw [heap_bump atAdd.frameAt keptApart]
  exact shape

/-- The entry assertion of `add`'s failure exits. -/
theorem entry_base {L : Statements.C1.Layout} {c : Context} {s a : MachineData} {seq : BitVec 64}
    {v4 : Bool} {key : Nat} {names : Allowedips.Names} {w : World} {d : Device} {W n : Nat}
    (wide : 200 ≤ W) (caller : Caller c s seq) (sep : Separate L c s W n)
    (table : names.table = L.table) (peers : names.trie.peers = L.peers)
    (arena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2)
    (rdi : s.regs.rdi.toNat = L.table)
    (related : Allowedips.Corresponds names Root.nodeOffsets s.dmem d)
    (shape : Allowedips.heap names (Allowedips.target d) s.dmem = .ok ())
    (atAdd : AtAdd c s seq v4 key a)
    (mapped : ∀ x k, (s.dmem.loadInt x k).isSome = true → (a.dmem.loadInt x k).isSome = true) :
    EntryBase names c (fun _ => False) (bumped w d) a (if v4 then 32 else 128)
      (s.regs.rdx.toNat % 256) (site v4).toUInt64 (bump d) := by
  have fs := frameSize_range v4
  have stackAt := atAdd.stackAt
  obtain ⟨relatedA,shapeA⟩ := related_at_add wide sep table peers arena rdi caller.seqWord related shape atAdd
  have window (x : BitVec 64) (h : Window a x) :
      InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 x := by
    have h' : InRange (a.regs.rsp.toBitVec - .ofNat 64 104) 112 x := h
    rw [stackAt, sub_sub_ofNat] at h'
    exact below_sub _ _ 112 200 208 (by omega) (by omega) x h'
  have windowW (x : BitVec 64) (h : Window a x) :
      InRange (s.regs.rsp.toBitVec - .ofNat 64 W) (W+8) x := by
    have h' : InRange (a.regs.rsp.toBitVec - .ofNat 64 104) 112 x := h
    rw [stackAt, sub_sub_ofNat] at h'
    exact below_sub _ _ 112 W (W+8) (by omega) (by omega) x h'
  refine {
    resources := {
      coverage := atAdd.coverage
      aligned := ?_
      slots := ?_
      callWord := ?_
      coverageApart := fun x read h => caller.coverageStack x read (window x h)
      metadataSeparate := caller.metadataSeparate
      preemptSeparate := caller.preemptSeparate }
    returnWord := atAdd.returnWord
    device := rfl
    asserted := assertAt_of_related rfl relatedA shapeA
    family := by cases v4 <;> simp
    argBits := atAdd.bits
    argCidr := atAdd.cidr
    readApart := fun span member x inside => by
      have inHeap := read_heap table peers arena span member x inside
      exact ⟨fun h => sep.heapStack x inHeap (windowW x h),sep.heapWrites x inHeap,fun h => h⟩
    awApart := fun x h => h.elim }
  · rw [atAdd.stack]
    cases v4
    · exact aligned_sub _ 56 (by omega) (by omega) caller.aligned caller.room
    · exact aligned_sub _ 48 (by omega) (by omega) caller.aligned caller.room
  · intro i hi
    apply mapped
    have at' : slot a i = s.regs.rsp.toBitVec - .ofNat 64
        (frameSize v4 + (if i<6 then (i+1)*8 else if i=6 then 88 else 80)) := by
      unfold slot
      rw [stackAt, sub_sub_ofNat]
    rw [at']
    have size : slotSize i ≤ 8 := by unfold slotSize; split <;> omega
    have depth : (if i<6 then (i+1)*8 else if i=6 then 88 else 80) ≤ 88 ∧
        8 ≤ (if i<6 then (i+1)*8 else if i=6 then 88 else 80) := by
      split
      · omega
      · split <;> omega
    exact caller.below.load _ _ (by omega) (by omega)
  · apply mapped
    have at' : a.regs.rsp.toBitVec - 104 = s.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 104) := by
      show a.regs.rsp.toBitVec - .ofNat 64 104 = _
      rw [stackAt, sub_sub_ofNat]
    rw [at']
    exact caller.below.load _ 8 (by omega) (by omega)

/-- The wrapper's epilogue, from `add`'s return. -/
theorem leave (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch)
    {c : Context} {s a : MachineData} {seq : BitVec 64} {v4 : Bool} {key : Nat}
    {t : MachineState} {ra : UInt64} {H : BitVec 64 → Prop}
    (W : Nat) (wide : 200 ≤ W) (room : W ≤ s.regs.rsp.toNat) (top : s.regs.rsp.toNat + 8 ≤ 2^64)
    (atAdd : AtAdd c s seq v4 key a)
    (returnWord : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (ra.toNat : Int))
    (buffer : ∀ x, c.writes x → ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 x)
    (seqStack : ∀ x, InRange (s.regs.rdi.toBitVec+16) 8 x →
      ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 x)
    (heapStack : ∀ x, H x → ¬InRange (s.regs.rsp.toBitVec - .ofNat 64 200) 208 x)
    (returned : Returned ⟨a,Add.entry⟩ t (site v4).toUInt64)
    (frame : EqualOutside (fun x =>
      InRange (s.regs.rsp.toBitVec - .ofNat 64 W) (W - frameSize v4 + 8) x ∨ c.writes x ∨ H x)
      a.dmem t.data.dmem) :
    Eventually (instructionStep fetch) (fun f =>
      f.pc = .ofBitVec ra.toBitVec ∧ f.data.regs.rsp = s.regs.rsp + 8 ∧
      f.data.regs.rbx = s.regs.rbx ∧ f.data.regs.rbp = s.regs.rbp ∧
      f.data.regs.r12 = s.regs.r12 ∧ f.data.regs.r13 = s.regs.r13 ∧
      f.data.regs.r14 = s.regs.r14 ∧ f.data.regs.r15 = s.regs.r15 ∧
      f.data.regs.rax = t.data.regs.rax ∧ f.data.dmem = t.data.dmem) t := by
  have stackAt := atAdd.stackAt
  have fs := frameSize_range v4
  have zero : s.regs.rsp.toBitVec - .ofNat 64 0 = s.regs.rsp.toBitVec := by simp
  have raA : a.dmem.loadInt s.regs.rsp.toBitVec 8 = some (ra.toNat : Int) := by
    rw [← zero, ← atAdd.frameAt.loadInt _ 8 (fun i hi h => by
      rcases h with h | h | h
      · exact below_under _ 0 8 _ _ (by omega) (by omega) (by omega) _ ⟨i,hi,rfl⟩ h
      · exact seqStack _ h (below_sub _ 0 8 200 208 (by omega) (by omega) _ ⟨i,hi,rfl⟩)
      · exact buffer _ h (below_sub _ 0 8 200 208 (by omega) (by omega) _ ⟨i,hi,rfl⟩)), zero]
    exact returnWord
  cases v4
  · exact leave_core fetch decoder false 16 rfl W wide room top stackAt atAdd.r13 atAdd.r12 atAdd.rbp
      atAdd.rbx atAdd.r14 atAdd.r15 raA buffer heapStack returned frame
  · exact leave_core fetch decoder true 8 rfl W wide room top stackAt atAdd.r13 atAdd.r12 atAdd.rbp
      atAdd.rbx atAdd.r14 atAdd.r15 raA buffer heapStack returned frame

#print axioms related_at_add
#print axioms entry_base
#print axioms leave
end C1Trunk
