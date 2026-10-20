import AllowedipsPlacementExits

namespace Binary.Pair.Allowedips.Placement
open TrustBase CommonBitsCoverage AllowedipsMutationImage AllowedipsRelation
local instance : Labels := Image.linkedLabels

/-- The read-only input facts consumed by the prefix half of one iteration.
They are entry-byte facts, independently of any execution or desired result. -/
structure NodeInput (base : MachineData) (c : Context) (address : UInt64)
    (bits query cidr : Nat) (node : Leanux.WG.AipNode) : Prop where
  family : bits=32 ∨ bits=128
  width : base.regs.r15=.ofNat bits
  requested : base.regs.r12=.ofNat cidr
  cidrBound : cidr≤bits
  nodeBound : node.cidr<256
  length : base.dmem.loadInt (address.toBitVec+24) 1=some node.cidr
  lengthApart : ∀ a, InRange (address.toBitVec+24) 1 a → ¬Writes base.regs.rsp c a
  keys : KeyFields base.dmem (address.toBitVec+32) bits node.bits query
  keysApart : ∀ a, KeyReads (address.toBitVec+32) bits node.bits query a → ¬Writes base.regs.rsp c a
  queryWords : AllowedipsChild.QueryWords base.dmem base.regs.r13.toBitVec bits query
  queryApart : ∀ a, InRange base.regs.r13.toBitVec (bits/8) a → ¬Writes base.regs.rsp c a

theorem NodeInput.length_current {base c address bits query cidr node}
    (input : NodeInput base c address bits query cidr node) {s}
    (frame : Frame base c s) (cursor : s.regs.rbx=address) :
    s.dmem.loadInt (s.regs.rbx.toBitVec+24) 1=some (BitVec.ofNat 8 node.cidr).toNat := by
  rw [cursor]
  rw [←frame.memory.loadInt (address.toBitVec+24) 1 (fun n bound => input.lengthApart _ ⟨n,bound,rfl⟩)]
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt input.nodeBound] using input.length

theorem NodeInput.common {base c address bits query cidr node}
    (input : NodeInput base c address bits query cidr node)
    (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (mutation : AllowedipsMutationDecoderAgreement fetch) (callbacks : CommonBits.Callbacks fetch)
    {s} (frame : Frame base c s) (cursor : s.regs.rbx=address) :
    Eventually (instructionStep fetch) (fun t => t.pc=Add.entry+0xa1 ∧ Frame base c t.data ∧
      t.data.regs.rbx=s.regs.rbx ∧ t.data.regs.rbp=s.regs.rbp ∧
      (t.data.regs.get (.low .rax .W8)).toNat=AllowedipsRelation.common bits node.bits query ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8)
      ⟨s,Add.entry+0x93⟩ := by
  apply frame.common_segment fetch decoder mutation callbacks bits node.bits query input.family
    (frame.bits.trans input.width)
  · simpa only [cursor] using input.keys.frame frame.memory input.keysApart
  · simpa only [frame.key] using AllowedipsLoop.query_frame input.family input.queryWords frame.memory input.queryApart
  · simpa only [cursor] using input.keysApart
  · simpa only [frame.key] using input.queryApart

theorem low_nat (n : Nat) (bound : n<256) :
    (Reg64s.get {rbp := .ofNat n} (.low .rbp .W8)).toNat=n := by
  simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
    Nat.mod_eq_of_lt bound]

/-- Length comparison from the loop header, including both real callbacks. -/
theorem NodeInput.length_segment {base c address bits query cidr node}
    (input : NodeInput base c address bits query cidr node)
    (fetch : Int64 → Option Decoded) (mutation : AllowedipsMutationDecoderAgreement fetch)
    (pcContract : AllowedipsTracePcContract fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {s} (frame : Frame base c s) (cursor : s.regs.rbx=address) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if node.cidr≤cidr then Add.entry+0x8e else Add.entry+0x113) ∧
      Frame base c t.data ∧ t.data.regs.rbx=address ∧ t.data.regs.rbp=.ofNat node.cidr ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8)
      ⟨s,Add.entry+0xf7⟩ := by
  have first := frame.call fetch (Add.entry+0xf7) "L_ffffffff810f31f0" .pc pcContract
    (mutation.add _ _ (by rfl))
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro t1 ⟨pc1,frame1,bx1,_,_,parent1⟩
  have second := frame1.cidr_arguments fetch mutation cmp (.ofNat 8 node.cidr)
    (input.length_current frame1 (bx1.trans cursor))
  have state1 : t1=⟨t1.data,Add.entry+0xfc⟩ := by cases t1 with | mk data pc => change pc=Add.entry+0xfc at pc1; cases pc1; rfl
  rw [state1]
  apply eventually_trans (instructionStep fetch) _ _ _ second
  rintro t2 ⟨pc2,frame2,bx2,bp2,_,parent2⟩
  have nodeRegister : t2.data.regs.rbp=.ofNat node.cidr := by
    rw [bp2,BitVec.setWidth_ofNat_of_le_of_lt (by decide) input.nodeBound]
    rfl
  have lengthByte : (t2.data.regs.get (.low .rbp .W8)).toNat=node.cidr := by
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
      nodeRegister,Nat.mod_eq_of_lt input.nodeBound]
  have requestByte : (t2.data.regs.get (.low .r12 .W8)).toNat=cidr := by
    have bound : cidr<256 := by rcases input.family with h|h <;> have := input.cidrBound <;> omega
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
      frame2.cidr,input.requested,Nat.mod_eq_of_lt bound]
  have third := frame2.branch (Add_r10a_layout.agreement mutation.add) _ (cidr_guard t2.data)
  have state2 : t2=⟨t2.data,Add.entry+0x10a⟩ := by cases t2 with | mk data pc => change pc=Add.entry+0x10a at pc2; cases pc2; rfl
  rw [state2]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ third
  rintro t3 ⟨pc3,frame3,regs3,memory3⟩
  refine ⟨by simpa only [lengthByte,requestByte] using pc3,frame3,?_,?_,?_⟩
  · simpa only [regs3] using bx2.trans (bx1.trans cursor)
  · simpa only [regs3] using nodeRegister
  · simpa only [memory3] using parent2.trans parent1

#print axioms NodeInput.length_segment
#print axioms NodeInput.common

private theorem low8_low32 (word : BitVec 64) :
    ((word.extractLsb' 0 32).setWidth 64).extractLsb' 0 8=word.extractLsb' 0 8 := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem at_pc (s : MachineState) (pc : Int64) (here : s.pc=pc) : s=⟨s.data,pc⟩ := by
  cases s with
  | mk data current => change current=pc at here; cases here; rfl

theorem NodeInput.prefix_segment {base c address bits query cidr node}
    (input : NodeInput base c address bits query cidr node)
    (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (mutation : AllowedipsMutationDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {s} (frame : Frame base c s) (cursor : s.regs.rbx=address)
    (length : s.regs.rbp=.ofNat node.cidr) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if node.cidr≤AllowedipsRelation.common bits node.bits query then Add.entry+0xb2 else Add.entry+0x113) ∧
      Frame base c t.data ∧ t.data.regs.rbx=address ∧ t.data.regs.rbp=.ofNat node.cidr ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8)
      ⟨s,Add.entry+0x8e⟩ := by
  have first := frame.call fetch (Add.entry+0x8e) "L_ffffffff810f31f0" .pc callbacks.pc
    (mutation.add _ _ (by rfl))
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro t1 ⟨pc1,frame1,bx1,bp1,_,parent1⟩
  have second := input.common fetch decoder mutation callbacks frame1 (bx1.trans cursor)
  rw [at_pc t1 _ pc1]
  apply eventually_trans (instructionStep fetch) _ _ _ second
  rintro t2 ⟨pc2,frame2,bx2,bp2,answer,parent2⟩
  have third := frame2.prefix_arguments fetch mutation cmp
  rw [at_pc t2 _ pc2]
  apply eventually_trans (instructionStep fetch) _ _ _ third
  rintro t3 ⟨pc3,frame3,bx3,bp3,result3,parent3⟩
  have length3 : t3.data.regs.rbp=.ofNat node.cidr := bp3.trans (bp2.trans (bp1.trans length))
  have cidrByte : (t3.data.regs.get (.low .rbp .W8)).toNat=node.cidr := by
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
      length3,Nat.mod_eq_of_lt input.nodeBound]
  have answer3 : (t3.data.regs.get (.low .r14 .W8)).toNat=AllowedipsRelation.common bits node.bits query := by
    simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
      result3,UInt64.toBitVec_ofBitVec,Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self,low8_low32] using answer
  have fourth := frame3.branch (Add_rad_layout.agreement mutation.add) _ (prefix_guard t3.data)
  rw [at_pc t3 _ pc3]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ fourth
  rintro t4 ⟨pc4,frame4,regs4,memory4⟩
  refine ⟨?_,frame4,?_,?_,?_⟩
  · rw [cidrByte,answer3] at pc4
    by_cases matched : node.cidr≤AllowedipsRelation.common bits node.bits query
    · simpa only [ite_eq_left matched,ite_eq_right (Nat.not_lt.mpr matched)] using pc4
    · simpa only [ite_eq_right matched,ite_eq_left (Nat.lt_of_not_ge matched)] using pc4
  · simpa only [regs4] using bx3.trans (bx2.trans (bx1.trans cursor))
  · simpa only [regs4] using length3
  · simpa only [memory4] using parent3.trans (parent2.trans parent1)

/-- Both guards and common_bits, before restoration or exact/child choice. -/
theorem NodeInput.prefix {base c address bits query cidr node}
    (input : NodeInput base c address bits query cidr node)
    (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (mutation : AllowedipsMutationDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {s} (frame : Frame base c s) (cursor : s.regs.rbx=address) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if node.cidr≤cidr ∧ node.cidr≤AllowedipsRelation.common bits node.bits query
        then Add.entry+0xb2 else Add.entry+0x113) ∧
      Frame base c t.data ∧ t.data.regs.rbx=address ∧ t.data.regs.rbp=.ofNat node.cidr ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8)
      ⟨s,Add.entry+0xf7⟩ := by
  have first := input.length_segment fetch mutation callbacks.pc cmp frame cursor
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro t1 ⟨pc1,frame1,bx1,bp1,parent1⟩
  by_cases short : node.cidr≤cidr
  · rw [ite_eq_left short] at pc1
    have second := input.prefix_segment fetch decoder mutation callbacks cmp frame1 bx1 bp1
    rw [at_pc t1 _ pc1]
    apply eventually_weaken (instructionStep fetch) _ _ _ _ second
    rintro t2 ⟨pc2,frame2,bx2,bp2,parent2⟩
    exact ⟨by simpa only [short,true_and] using pc2,frame2,bx2,bp2,parent2.trans parent1⟩
  · exact .done _ ⟨by simpa only [ite_eq_right short,short,false_and,ite_false] using pc1,
      frame1,bx1,bp1,parent1⟩

#print axioms NodeInput.prefix
end Binary.Pair.Allowedips.Placement
