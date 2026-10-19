import PeerComparisons

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

def loaded (s : MachineData) (count : UInt32) : MachineData :=
  {s with regs := {s.regs with rbp := count.toUInt64, r13 := s.regs.rbx+0x420}}

/-- The nonnull prefix loads the actual refcount and reaches its zero test.
    Both instrumentation calls and the comparison call are executed through
    their named contracts. Their memory frames preserve the loaded word. -/
theorem load_prefix (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (s : MachineData) (nonnull : s.regs.rbx ≠ 0) (count : UInt32)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec+0x420) 4 = some count.toNat)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt s)
    (fieldSeparate : ∀ a, InRange (s.regs.rbx.toBitVec+0x420) 4 a →
      ¬(InRange (s.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a)) :
    Eventually (instructionStep fetch) (CallPost (loaded s count) coverage preempt 0x3b)
      ⟨s, Image.PeerGet.entry+0x12⟩ := by
  have guard := region_eventually (Image.PeerGet_r12_layout.agreement agree) s _ (null_guard s)
  apply eventually_trans (instructionStep fetch) _ _ _ guard
  rintro guarded ⟨guardRegs, guardMemory, guardPC⟩
  have atCall : guarded = ⟨guarded.data, Image.PeerGet.entry+0x1b⟩ := by
    have pc : guarded.pc = Image.PeerGet.entry+0x1b := by simpa only [ite_eq_right nonnull] using guardPC
    cases guarded with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [atCall]
  have step1 := pc_region fetch 0x1b (Image.PeerGet_r1b_layout.agreement agree)
    tracePc guarded.data coverage preempt (by simpa only [guardMemory] using ready.state)
    (by simpa only [guardRegs] using ready.aligned)
    (by simpa only [guardRegs, guardMemory] using ready.mapped)
    (by simpa only [guardRegs] using ready.pushSeparate)
    (by simpa only [guardRegs] using ready.returnSeparate)
    ready.metadataSeparate ready.preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ step1
  intro s1 h1
  have h1' : CallPost s coverage preempt 0x20 s1 := by
    simpa only [CallPost, guardRegs, guardMemory] using h1
  have ready1 := h1'.next_ready ready
  have h1regs := h1'
  obtain ⟨pc1, sp1, bx1, _, _, _, _, _, _, frame1, word1⟩ := h1'
  have field1 : s1.data.dmem.loadInt (s1.data.regs.rbx.toBitVec+0x420) 4 = some count.toNat := by
    rw [bx1, ← frame1.loadInt (s.regs.rbx.toBitVec+0x420) 4 (by
      intro byte bound; exact fieldSeparate _ ⟨byte, bound, rfl⟩)]
    exact field
  have atLoad : s1 = ⟨s1.data, Image.PeerGet.entry+0x20⟩ := by
    cases s1 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc1
  rw [atLoad]
  have step2 := region_eventually (Image.PeerGet_r20_layout.agreement agree) s1.data _
    (refcount_load s1.data count field1)
  apply eventually_trans (instructionStep fetch) _ _ _ step2
  rintro s2 ⟨regs2, memory2, pc2⟩
  have ready2 : CallsReady coverage preempt s2.data := by
    exact ⟨by simpa only [memory2] using ready1.state,
      by simpa only [regs2] using ready1.aligned,
      by simpa only [regs2, memory2] using ready1.mapped,
      by simpa only [regs2] using ready1.pushSeparate,
      by simpa only [regs2] using ready1.returnSeparate,
      ready1.metadataSeparate, ready1.preemptSeparate⟩
  have atTrace : s2 = ⟨s2.data, Image.PeerGet.entry+0x2d⟩ := by
    cases s2 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc2
  rw [atTrace]
  have step3 := pc_region fetch 0x2d (Image.PeerGet_r2d_layout.agreement agree)
    tracePc s2.data coverage preempt ready2.state ready2.aligned ready2.mapped
    ready2.pushSeparate ready2.returnSeparate ready2.metadataSeparate ready2.preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ step3
  intro s3 h3
  have h23 : CallPost (loaded s count) coverage preempt 0x32 s3 := by
    obtain ⟨_, _, _, _, r121, _, r141, r151, _, _, _⟩ := h1regs
    obtain ⟨pc3, sp3, bx3, bp3, r123, r133, r143, r153, state3, frame3, word3⟩ := h3
    have sp2 : s2.data.regs.rsp = s.regs.rsp := by simpa only [regs2] using sp1
    refine ⟨pc3, sp3.trans sp2, ?_, ?_, ?_, ?_, ?_, ?_, state3, ?_, ?_⟩
    · simpa only [loaded, regs2, bx1] using bx3
    · simpa only [loaded, regs2] using bp3
    · simpa only [loaded, regs2, r121] using r123
    · simpa only [loaded, regs2, bx1] using r133
    · simpa only [loaded, regs2, r141] using r143
    · simpa only [loaded, regs2, r151] using r153
    · change EqualOutside _ s.dmem s3.data.dmem
      rw [sp2, memory2] at frame3
      intro a outside
      exact (frame1 a outside).trans (frame3 a outside)
    · simpa only [loaded, sp2] using word3
  have ready3 := h3.next_ready ready2
  have atCompare : s3 = ⟨s3.data, Image.PeerGet.entry+0x32⟩ := by
    have pc := h3.1
    cases s3 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [atCompare]
  obtain ⟨word3, wordRead3⟩ := Option.isSome_iff_exists.mp ready3.mapped
  have step4 := comparison_region fetch Image.PeerGet.r32 0x32 0x3b
    (Image.PeerGet_r32_layout.agreement agree) traceCmp s3.data 0
    (.ofBitVec ((s3.data.regs.get (.low .rbp .W32)).setWidth 64))
    (compare_old s3.data word3 wordRead3) coverage preempt ready3.state ready3.aligned
    ready3.pushSeparate ready3.returnSeparate ready3.metadataSeparate ready3.preemptSeparate
  apply eventually_weaken (instructionStep fetch) _ _ _ _ step4
  intro t h4
  exact h23.trans h4

#print axioms load_prefix
end Binary.PeerGet
