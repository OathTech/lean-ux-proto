import AllowedipsReturnRegions

namespace Binary.Pair.Allowedips.Return
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem saved_read {s offset value} (checked : saved s offset=.ok value) :
    s.dmem.loadInt (s.regs.rsp.toBitVec+.ofNat 64 offset) 8=some value.toNat := by
  unfold saved at checked
  cases read : readNat ⟨s,0⟩ ((s.regs.rsp.toBitVec+.ofNat 64 offset).toNat) 8 with
  | error message => simp only [read] at checked; cases checked
  | ok n =>
    simp only [read] at checked
    cases checked
    have result := Exact.read_word64 read
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at result
    simpa using result

/-- The executable summary supplies only current saved words; the theorem
executes the image through RET and proves the resulting registers and memory. -/
theorem add_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s regs pc} (checked : addEffect s=.ok (regs,pc)) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs=regs ∧ t.data.dmem=s.dmem ∧ t.pc=pc) ⟨s,Add.entry+0x54e⟩ := by
  unfold addEffect at checked
  obtain ⟨bx,h0,checked⟩ := bind_ok checked
  obtain ⟨bp,h1,checked⟩ := bind_ok checked
  obtain ⟨r12,h2,checked⟩ := bind_ok checked
  obtain ⟨r13,h3,checked⟩ := bind_ok checked
  obtain ⟨r14,h4,checked⟩ := bind_ok checked
  obtain ⟨r15,h5,checked⟩ := bind_ok checked
  obtain ⟨ra,h6,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r54e_layout.agreement decoder.add) s _
      (addPrefix s bx bp r12 r13 r14 r15 (saved_read h0) (saved_read h1)
        (saved_read h2) (saved_read h3) (saved_read h4) (saved_read h5)))
  rintro t ⟨registers,memory,position⟩
  have returnRead : t.data.dmem.loadInt t.data.regs.rsp.toBitVec 8=some ra.toNat := by
    simpa [memory,registers,UInt64.toBitVec_add] using saved_read h6
  rw [Placement.at_pc t _ position]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r55e_layout.agreement decoder.add) t.data _ (ret t.data _ ra returnRead))
  rintro final ⟨registers',memory',pc'⟩
  refine ⟨?_,memory'.trans memory,pc'⟩
  simp only [registers',registers,UInt64.add_assoc]
  rfl

theorem wrapper_layout (v4 : Bool) (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch) :
    LaidOut fetch (if v4 then Insert4.entry+0x42 else Insert6.entry+0x4f) ((wrapperCode v4).take 1) := by
  cases v4
  · exact (AllowedipsLoop.layout_take Insert6_r4f_layout 1).agreement decoder.insert6
  · exact (AllowedipsLoop.layout_take Insert4_r42_layout 1).agreement decoder.insert4

theorem wrapper_checked (v4 : Bool) (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s regs pc} (checked : wrapperEffect v4 s=.ok (regs,pc)) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs=regs ∧ t.data.dmem=s.dmem ∧ t.pc=pc)
      ⟨s,if v4 then Insert4.entry+0x42 else Insert6.entry+0x4f⟩ := by
  unfold wrapperEffect at checked
  obtain ⟨bx,h0,checked⟩ := bind_ok checked
  obtain ⟨bp,h1,checked⟩ := bind_ok checked
  obtain ⟨r12,h2,checked⟩ := bind_ok checked
  obtain ⟨r13,h3,checked⟩ := bind_ok checked
  obtain ⟨ra,h4,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have reads0 := saved_read h0
  have reads1 := saved_read h1
  have reads2 := saved_read h2
  have reads3 := saved_read h3
  have reads4 := saved_read h4
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (wrapper_layout v4 fetch decoder) s _ (wrapper_adjust v4 s _))
  rintro a ⟨regsA,memA,pcA⟩
  have load0 : a.data.dmem.loadInt a.data.regs.rsp.toBitVec 8=some bx.toNat := by
    simpa only [regsA,memA,UInt64.toBitVec_add,UInt64.toBitVec_ofNat',UInt64.toBitVec_ofNat] using reads0
  have load1 : a.data.dmem.loadInt (a.data.regs.rsp.toBitVec+8) 8=some bp.toNat := by
    simp only [regsA,memA,UInt64.toBitVec_add,BitVec.add_assoc]
    cases v4 <;> exact reads1
  have load2 : a.data.dmem.loadInt (a.data.regs.rsp.toBitVec+16) 8=some r12.toNat := by
    simp only [regsA,memA,UInt64.toBitVec_add,BitVec.add_assoc]
    cases v4 <;> exact reads2
  have load3 : a.data.dmem.loadInt (a.data.regs.rsp.toBitVec+24) 8=some r13.toNat := by
    simp only [regsA,memA,UInt64.toBitVec_add,BitVec.add_assoc]
    cases v4 <;> exact reads3
  have popsLayout : LaidOut fetch
      (if v4 then Insert4.entry+0x46 else Insert6.entry+0x53) (Insert4.r42.drop 1 |>.take 4) := by
    cases v4
    · apply LaidOut.agreement (fetch:=Insert6.fetch) _ decoder.insert6
      binary_layout
    · apply LaidOut.agreement (fetch:=Insert4.fetch) _ decoder.insert4
      binary_layout
  have atPops : a.pc=(if v4 then Insert4.entry+0x46 else Insert6.entry+0x53) := by
    rw [pcA]; cases v4 <;> rfl
  rw [Placement.at_pc a _ atPops]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually popsLayout a.data _ (wrapper_pop a.data _ bx bp r12 r13 load0 load1 load2 load3))
  rintro t ⟨registers,memory,position⟩
  have returnRead : t.data.dmem.loadInt t.data.regs.rsp.toBitVec 8=some ra.toNat := by
    simp only [memory,registers,memA,regsA,UInt64.toBitVec_add,BitVec.add_assoc]
    cases v4 <;> exact reads4
  have layout : LaidOut fetch (if v4 then Insert4.entry+0x4c else Insert6.entry+0x59) Add.r55e := by
    cases v4
    · apply LaidOut.agreement (fetch:=Insert6.fetch) _ decoder.insert6
      binary_layout
    · apply LaidOut.agreement (fetch:=Insert4.fetch) _ decoder.insert4
      binary_layout
  have atReturn : t.pc=(if v4 then Insert4.entry+0x4c else Insert6.entry+0x59) := by
    rw [position]; cases v4 <;> rfl
  rw [Placement.at_pc t _ atReturn]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually layout t.data _ (ret t.data _ ra returnRead))
  rintro final ⟨registers',memory',pc'⟩
  refine ⟨?_,memory'.trans (memory.trans memA),pc'⟩
  simp only [registers',registers,regsA,UInt64.add_assoc]
  cases v4 <;> rfl

#print axioms add_checked
#print axioms wrapper_checked
end Binary.Pair.Allowedips.Return
