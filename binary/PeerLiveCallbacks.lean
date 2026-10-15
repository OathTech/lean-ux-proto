import PeerComparisons

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Instrumented success suffix after CMPXCHG and its comparison callback.
    The three branch facts are consequences of the proved increment and
    the mirror's accepted refcount bound, supplied by the caller. -/
theorem live_callbacks (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt s)
    (success : s.regs.get (.low .r15 .W8) ≠ 0)
    (oldPositive : (s.regs.get (.low .rbp .W32)).msb = false)
    (newPositive : (s.regs.get (.low .r12 .W32)).msb = false) :
    Eventually (instructionStep fetch) (CallPost s coverage preempt 0x9d)
      ⟨s, Image.PeerGet.entry+0x60⟩ := by
  have branchRun0 := retry_guard s
  simp only [ite_eq_right success] at branchRun0
  have step1 := guard_pc_region fetch Image.PeerGet.r60 0x60 0x69
    (Image.PeerGet_r60_layout.agreement agree) (Image.PeerGet_r69_layout.agreement agree)
    tracePc s (by simpa using branchRun0)
    coverage preempt ready
  apply eventually_trans (instructionStep fetch) _ _ _ step1
  intro s1 h1
  have ready1 := h1.next_ready ready
  have at1 : s1 = ⟨s1.data, Image.PeerGet.entry+0x6e⟩ := by
    have pc := h1.1
    cases s1 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [at1]
  obtain ⟨word1, wordRead1⟩ := Option.isSome_iff_exists.mp ready1.mapped
  have step2 := comparison_region fetch Image.PeerGet.r6e 0x6e 0x77
    (Image.PeerGet_r6e_layout.agreement agree) traceCmp s1.data 0
    (.ofBitVec ((s1.data.regs.get (.low .rbp .W32)).setWidth 64))
    (compare_negative s1.data word1 wordRead1) coverage preempt
    ready1.state ready1.aligned ready1.pushSeparate ready1.returnSeparate
    ready1.metadataSeparate ready1.preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ step2
  intro s2 h2
  have ready2 := h2.next_ready ready1
  have total2 := h1.trans h2
  have at2 : s2 = ⟨s2.data, Image.PeerGet.entry+0x77⟩ := by
    have pc := h2.1
    cases s2 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [at2]
  have branch1 : (s2.data.regs.get (.low .rbp .W32)).msb = false := by
    have same := total2.2.2.2.1
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, same] using oldPositive
  have branchRun1 := negative_guard s2.data
  have step3 := guard_pc_region fetch Image.PeerGet.r77 0x77 0x7b
    (Image.PeerGet_r77_layout.agreement agree) (Image.PeerGet_r7b_layout.agreement agree)
    tracePc s2.data (by simpa [branch1] using branchRun1)
    coverage preempt ready2
  apply eventually_trans (instructionStep fetch) _ _ _ step3
  intro s3 h3
  have ready3 := h3.next_ready ready2
  have at3 : s3 = ⟨s3.data, Image.PeerGet.entry+0x80⟩ := by
    have pc := h3.1
    cases s3 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [at3]
  obtain ⟨word3, wordRead3⟩ := Option.isSome_iff_exists.mp ready3.mapped
  have step4 := comparison_region fetch Image.PeerGet.r80 0x80 0x8a
    (Image.PeerGet_r80_layout.agreement agree) traceCmp s3.data 0
    (.ofBitVec ((s3.data.regs.get (.low .r12 .W32)).setWidth 64))
    (compare_increment s3.data word3 wordRead3) coverage preempt
    ready3.state ready3.aligned ready3.pushSeparate ready3.returnSeparate
    ready3.metadataSeparate ready3.preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ step4
  intro s4 h4
  have ready4 := h4.next_ready ready3
  have total4 := total2.trans (h3.trans h4)
  have at4 : s4 = ⟨s4.data, Image.PeerGet.entry+0x8a⟩ := by
    have pc := h4.1
    cases s4 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [at4]
  have branch2 : (s4.data.regs.get (.low .r12 .W32)).msb = false := by
    have same := total4.2.2.2.2.1
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, same] using newPositive
  have branchRun2 := overflow_guard s4.data
  have step5 := guard_pc_region fetch Image.PeerGet.r8a 0x8a 0x8f
    (Image.PeerGet_r8a_layout.agreement agree) (Image.PeerGet_r8f_layout.agreement agree)
    tracePc s4.data (by simpa [branch2] using branchRun2)
    coverage preempt ready4
  apply eventually_trans (instructionStep fetch) _ _ _ step5
  intro s5 h5
  have ready5 := h5.next_ready ready4
  have at5 : s5 = ⟨s5.data, Image.PeerGet.entry+0x94⟩ := by
    have pc := h5.1
    cases s5 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [at5]
  obtain ⟨word5, wordRead5⟩ := Option.isSome_iff_exists.mp ready5.mapped
  have step6 := comparison_region fetch Image.PeerGet.r94 0x94 0x9d
    (Image.PeerGet_r94_layout.agreement agree) traceCmp s5.data 0
    (.ofBitVec ((s5.data.regs.get (.low .rbp .W32)).setWidth 64))
    (compare_result s5.data word5 wordRead5) coverage preempt
    ready5.state ready5.aligned ready5.pushSeparate ready5.returnSeparate
    ready5.metadataSeparate ready5.preemptSeparate
  apply eventually_weaken (instructionStep fetch) _ _ _ _ step6
  intro t h6
  exact total4.trans (h5.trans h6)

#print axioms live_callbacks
end Binary.PeerGet
