import AllowedipsPlacementSteps
import AllowedipsLoopCaller

namespace Binary.Pair.Allowedips.Placement
open TrustBase CommonBitsCoverage AllowedipsMutationImage AllowedipsRelation
local instance : Labels := Image.linkedLabels

private theorem arguments_layout : LaidOut Add.fetch (Add.entry+0x93) (Add.r93.take 3) := by
  binary_layout

theorem Frame.input_caller {base c s} (frame : Frame base c s)
    (bits stored query : Nat) (returnPC : Int64) (family : bits=32 ∨ bits=128)
    (familyByte : s.regs.get (.low .rdx .W8)=.ofNat 8 bits)
    (keyFields : KeyFields s.dmem (s.regs.rdi.toBitVec+32) bits stored query)
    (queryWords : AllowedipsChild.QueryWords s.dmem s.regs.rsi.toBitVec bits query)
    (keyApart : ∀ a, KeyReads (s.regs.rdi.toBitVec+32) bits stored query a → ¬Writes base.regs.rsp c a)
    (queryApart : ∀ a, InRange s.regs.rsi.toBitVec (bits/8) a → ¬Writes base.regs.rsp c a) :
    CommonBits.CallerAt (Common.callInput s bits stored query returnPC) c s returnPC := by
  refine ⟨rfl,rfl,rfl,familyByte.symm,rfl,rfl,rfl,rfl,rfl,?_,?_,frame.ready.state,
    frame.ready.aligned,?_,?_,frame.ready.metadataSeparate,frame.ready.preemptSeparate⟩
  · exact AllowedipsLoop.input_keys s bits stored query family keyFields queryWords
  · intro a read written
    have parts := AllowedipsLoop.input_keyBytes s bits stored query family keyFields.1 keyFields.2.1 a read
    have within : Writes base.regs.rsp c a := by
      rcases written with scratch | buffer
      · exact .inl (scratch_subset (by simpa only [CommonBits.CallerScratch,frame.stack] using scratch))
      · exact .inr buffer
    rcases parts with key | query
    · exact keyApart a key within
    · exact queryApart a query within
  · simpa only [frame.stack] using frame.mapped
  · intro a read scratch
    exact frame.separate a read (scratch_subset (by simpa only [CommonBits.CallerScratch,frame.stack] using scratch))

/-- Argument moves and the complete common_bits call form one reusable
execution segment. All input and separation premises concern the entry bytes. -/
theorem Frame.common_segment (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (mutation : AllowedipsMutationDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch)
    {base c s} (frame : Frame base c s) (bits stored query : Nat)
    (family : bits=32 ∨ bits=128) (width : s.regs.r15=.ofNat bits)
    (keyFields : KeyFields s.dmem (s.regs.rbx.toBitVec+32) bits stored query)
    (queryWords : AllowedipsChild.QueryWords s.dmem s.regs.r13.toBitVec bits query)
    (keyApart : ∀ a, KeyReads (s.regs.rbx.toBitVec+32) bits stored query a → ¬Writes base.regs.rsp c a)
    (queryApart : ∀ a, InRange s.regs.r13.toBitVec (bits/8) a → ¬Writes base.regs.rsp c a) :
    Eventually (instructionStep fetch) (fun t => t.pc=Add.entry+0xa1 ∧
      Frame base c t.data ∧ t.data.regs.rbx=s.regs.rbx ∧ t.data.regs.rbp=s.regs.rbp ∧
      (t.data.regs.get (.low .rax .W8)).toNat=AllowedipsRelation.common bits stored query) ⟨s,Add.entry+0x93⟩ := by
  have first := region_eventually (arguments_layout.agreement mutation.add) s _ (common_arguments s)
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro t ⟨pc,regs,memory⟩
  have framed := frame.congr memory (by simp [regs]) (by simp [regs]) (by simp [regs]) (by simp [regs])
  have fields : KeyFields t.data.dmem (t.data.regs.rdi.toBitVec+32) bits stored query := by
    simpa only [memory,regs] using keyFields
  have words : AllowedipsChild.QueryWords t.data.dmem t.data.regs.rsi.toBitVec bits query := by
    simpa only [memory,regs] using queryWords
  have byte : t.data.regs.get (.low .rdx .W8)=.ofNat 8 bits := by
    rcases family with rfl | rfl <;> simp [regs,width,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
  have caller := framed.input_caller bits stored query (Add.entry+0xa1) family byte fields words
    (by simpa only [regs] using keyApart) (by simpa only [regs] using queryApart)
  have called := framed.common fetch decoder callbacks (Add.entry+0x9c)
    (mutation.add _ _ (by rfl)) (Common.callInput t.data bits stored query (Add.entry+0xa1)) caller
  have state : t=⟨t.data,Add.entry+0x9c⟩ := by cases t; simp_all
  rw [state]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ called
  rintro out ⟨pc,frame,bx,bp,answer⟩
  refine ⟨pc,frame,?_,?_,?_⟩
  · simpa only [regs] using bx
  · simpa only [regs] using bp
  · simpa only [common_input_result _ _ _ _ _ family keyFields.1 keyFields.2.1] using answer

#print axioms Frame.common_segment
end Binary.Pair.Allowedips.Placement
