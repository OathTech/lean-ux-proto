import PairInsertEnable

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels

theorem enable_unhash (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (bh : BhEnableContract fetch) {n o c initial ra shadow s}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra .outer shadow s) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x65 ∧
      Core n o c initial ra .enabled shadow t.data) ⟨s,codeEntry+0x54⟩ := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp (core.calls facts).mapped
  have region := region_eventually (IndexInsertImage.Insert_r54_layout.agreement decoder) s _
    (call_unhash_bh s old read)
  have run := core.enable_region fetch bh facts false ⟨s,codeEntry+0x54⟩ (codeEntry+0x65)
    {s.regs with rsi := 512,rdi := (codeEntry+0x60).toUInt64} rfl rfl (by rfl) region
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨pc,core,_⟩
  exact ⟨pc,core⟩

theorem enable_nested (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (bh : BhEnableContract fetch) {n o c initial ra shadow s}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra .inner shadow s) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x174 ∧
      Core n o c initial ra .outer shadow t.data ∧ t.data.regs.rbx=(codeEntry+0x16c).toUInt64)
      ⟨s,codeEntry+0x160⟩ := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp (core.calls facts).mapped
  have region := region_eventually (IndexInsertImage.Insert_r160_layout.agreement decoder) s _
    (call_nested_bh s old read)
  have run := core.enable_region fetch bh facts true ⟨s,codeEntry+0x160⟩ (codeEntry+0x174)
    {s.regs with rsi := 512,rdi := (codeEntry+0x16c).toUInt64,rbx := (codeEntry+0x16c).toUInt64}
    rfl rfl (by rfl) region
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨pc,core,bx,_⟩
  exact ⟨pc,core,bx⟩

theorem enable_outer (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (bh : BhEnableContract fetch) {n o c initial ra shadow s}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra .outer shadow s) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x181 ∧
      Core n o c initial ra .enabled shadow t.data) ⟨s,codeEntry+0x174⟩ := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp (core.calls facts).mapped
  have region := region_eventually (IndexInsertImage.Insert_r174_layout.agreement decoder) s _
    (call_outer_bh s old read)
  have run := core.enable_region fetch bh facts false ⟨s,codeEntry+0x174⟩ (codeEntry+0x181)
    {s.regs with rsi := 512,rdi := s.regs.rbx} rfl rfl (by rfl) region
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨pc,core,_⟩
  exact ⟨pc,core⟩

#print axioms enable_unhash
#print axioms enable_nested
#print axioms enable_outer
end Binary.Pair.Insert
