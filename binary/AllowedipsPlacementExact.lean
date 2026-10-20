import AllowedipsPlacementPrefix

namespace Binary.Pair.Allowedips.Placement
open TrustBase CommonBitsCoverage AllowedipsMutationImage AllowedipsRelation
local instance : Labels := Image.linkedLabels

theorem NodeInput.exact_segment {base c address bits query cidr node}
    (input : NodeInput base c address bits query cidr node)
    (fetch : Int64 → Option Decoded) (mutation : AllowedipsMutationDecoderAgreement fetch)
    (pcContract : AllowedipsTracePcContract fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {s} (frame : Frame base c s) (cursor : s.regs.rbx=address)
    (length : s.regs.rbp=.ofNat node.cidr) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if node.cidr=cidr then Add.entry+0x3ca else Add.entry+0xca) ∧
      Frame base c t.data ∧ t.data.regs.rbx=address ∧ t.data.regs.rbp=.ofNat node.cidr ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8)
      ⟨s,Add.entry+0xb2⟩ := by
  have first := frame.call fetch (Add.entry+0xb2) "L_ffffffff810f31f0" .pc pcContract
    (mutation.add _ _ (by rfl))
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro t1 ⟨pc1,frame1,bx1,bp1,_,parent1⟩
  have second := frame1.exact_arguments fetch mutation cmp
  rw [at_pc t1 _ pc1]
  apply eventually_trans (instructionStep fetch) _ _ _ second
  rintro t2 ⟨pc2,frame2,bx2,bp2,_,parent2⟩
  have length2 : t2.data.regs.rbp=.ofNat node.cidr := bp2.trans (bp1.trans length)
  have lengthByte : (t2.data.regs.get (.low .rbp .W8)).toNat=node.cidr := by
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
      length2,Nat.mod_eq_of_lt input.nodeBound]
  have requestByte : (t2.data.regs.get (.low .r12 .W8)).toNat=cidr := by
    have bound : cidr<256 := by rcases input.family with h|h <;> have := input.cidrBound <;> omega
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
      frame2.cidr,input.requested,Nat.mod_eq_of_lt bound]
  have equal : (t2.data.regs.get (.low .r12 .W8)==t2.data.regs.get (.low .rbp .W8))=(node.cidr==cidr) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,←BitVec.toNat_inj,requestByte,lengthByte]
    exact eq_comm
  have third := frame2.branch (Add_rc1_layout.agreement mutation.add) _ (exact_guard t2.data)
  rw [at_pc t2 _ pc2]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ third
  rintro t3 ⟨pc3,frame3,regs3,memory3⟩
  refine ⟨by simpa only [equal,beq_iff_eq] using pc3,frame3,?_,?_,?_⟩
  · simpa only [regs3] using bx2.trans (bx1.trans cursor)
  · simpa only [regs3] using length2
  · simpa only [memory3] using parent2.trans parent1

#print axioms NodeInput.exact_segment
end Binary.Pair.Allowedips.Placement
