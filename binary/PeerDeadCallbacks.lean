import PeerComparisons

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Actual instrumentation suffix reached after the zero-refcount guard.
    Every callback preserves the physical call invariant; no peer field is
    written along this suffix. The clear-peer instruction follows at +0xdd. -/
theorem dead_callbacks (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt s) :
    Eventually (instructionStep fetch) (CallPost s coverage preempt 0xdd)
      ⟨s, Image.PeerGet.entry+0xb0⟩ := by
  have step1 := pc_region fetch 0xb0 (Image.PeerGet_rb0_layout.agreement agree)
    tracePc s coverage preempt ready.state ready.aligned ready.mapped
    ready.pushSeparate ready.returnSeparate ready.metadataSeparate ready.preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ step1
  intro s1 h1
  have ready1 := h1.next_ready ready
  have at1 : s1 = ⟨s1.data, Image.PeerGet.entry+0xb5⟩ := by
    have pc := h1.1
    cases s1 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [at1]
  obtain ⟨word1, wordRead1⟩ := Option.isSome_iff_exists.mp ready1.mapped
  have step2 := comparison_region fetch Image.PeerGet.rb5 0xb5 0xbe
    (Image.PeerGet_rb5_layout.agreement agree) traceCmp s1.data 0 0
    (compare_zero s1.data word1 wordRead1) coverage preempt ready1.state ready1.aligned
    ready1.pushSeparate ready1.returnSeparate ready1.metadataSeparate ready1.preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ step2
  intro s2 h2
  have ready2 := h2.next_ready ready1
  have at2 : s2 = ⟨s2.data, Image.PeerGet.entry+0xbe⟩ := by
    have pc := h2.1
    cases s2 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [at2]
  have step3 := pc_region fetch 0xbe (Image.PeerGet_rbe_layout.agreement agree)
    tracePc s2.data coverage preempt ready2.state ready2.aligned ready2.mapped
    ready2.pushSeparate ready2.returnSeparate ready2.metadataSeparate ready2.preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ step3
  intro s3 h3
  have ready3 := h3.next_ready ready2
  have at3 : s3 = ⟨s3.data, Image.PeerGet.entry+0xc3⟩ := by
    have pc := h3.1
    cases s3 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [at3]
  obtain ⟨word3, wordRead3⟩ := Option.isSome_iff_exists.mp ready3.mapped
  have step4 := comparison_region fetch Image.PeerGet.rc3 0xc3 0xcf
    (Image.PeerGet_rc3_layout.agreement agree) traceCmp s3.data 0 1
    (compare_one s3.data word3 wordRead3) coverage preempt ready3.state ready3.aligned
    ready3.pushSeparate ready3.returnSeparate ready3.metadataSeparate ready3.preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ step4
  intro s4 h4
  have ready4 := h4.next_ready ready3
  have at4 : s4 = ⟨s4.data, Image.PeerGet.entry+0xcf⟩ := by
    have pc := h4.1
    cases s4 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [at4]
  have step5 := pc_region fetch 0xcf (Image.PeerGet_rcf_layout.agreement agree)
    tracePc s4.data coverage preempt ready4.state ready4.aligned ready4.mapped
    ready4.pushSeparate ready4.returnSeparate ready4.metadataSeparate ready4.preemptSeparate
  apply eventually_trans (instructionStep fetch) _ _ _ step5
  intro s5 h5
  have ready5 := h5.next_ready ready4
  have at5 : s5 = ⟨s5.data, Image.PeerGet.entry+0xd4⟩ := by
    have pc := h5.1
    cases s5 with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [at5]
  obtain ⟨word5, wordRead5⟩ := Option.isSome_iff_exists.mp ready5.mapped
  have step6 := comparison_region fetch Image.PeerGet.rd4 0xd4 0xdd
    (Image.PeerGet_rd4_layout.agreement agree) traceCmp s5.data 0 0
    (compare_dead s5.data word5 wordRead5) coverage preempt ready5.state ready5.aligned
    ready5.pushSeparate ready5.returnSeparate ready5.metadataSeparate ready5.preemptSeparate
  apply eventually_weaken (instructionStep fetch) _ _ _ _ step6
  intro t h6
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

#print axioms dead_callbacks
end Binary.PeerGet
