import AllowedipsRootStore

namespace Binary.Pair.Allowedips.Root
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

structure CopyFrame (before after : Reg64s) : Prop where
  base : after.rbx=before.rbx
  stack : after.rsp=before.rsp
  bits : after.rbp=before.rbp
  kept12 : after.r12=before.r12
  query : after.r13=before.r13
  peer : after.r14=before.r14
  kept15 : after.r15=before.r15
  dest : after.rsi=before.rsi

theorem copy4_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s memory} (bits : s.regs.rbp=32) (size : s.regs.rax=4)
    (dest : s.regs.rsi.toBitVec=s.regs.rbx.toBitVec+32)
    (checked : copy s s.dmem=.ok memory) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x4d6 ∧ t.data.dmem=memory ∧ CopyFrame s.regs t.data.regs)
      ⟨s,Add.entry+0x51f⟩ := by
  unfold copy at checked
  simp only [bits,show ((32 : UInt64).toNat==32)=true from rfl,ite_true] at checked
  obtain ⟨first,firstRead,checked⟩ := bind_ok checked
  obtain ⟨middle,firstStore,checked⟩ := bind_ok checked
  obtain ⟨again,againRead,checked⟩ := bind_ok checked
  obtain ⟨last,againStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  obtain ⟨firstMapped,firstEq⟩ := store_facts firstStore
  obtain ⟨againMapped,againEq⟩ := store_facts againStore
  rw [store_nat32] at firstEq againEq
  have firstMem : middle=first4Memory s (.ofNat 32 first) := by
    simpa [first4Memory,BitVec.ofNat_add,ofNat_uint64] using firstEq
  have lastMem : memory=copied4Memory s (.ofNat 32 first) (.ofNat 32 again) := by
    simpa [copied4Memory,firstMem,BitVec.ofNat_add,ofNat_uint64] using againEq
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r51f_layout.agreement decoder.add) s _ (copy4_branch s size))
  rintro a ⟨mem,regs,pc⟩
  rw [Placement.at_pc a _ pc]
  have run := copy4 a.data (.ofNat 32 first) (.ofNat 32 again)
    (regs ▸ size) (by simpa only [regs] using dest)
    (by simpa [mem,regs,ofNat_uint64] using read_word32 firstRead)
    (by simpa [mem,regs,BitVec.ofNat_add,ofNat_uint64] using firstMapped)
    (by simpa [firstMem,first4Memory,mem,regs,ofNat_uint64] using read_word32 againRead)
    (by simpa [firstMem,first4Memory,mem,regs,BitVec.ofNat_add,ofNat_uint64] using againMapped)
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r757_layout.agreement decoder.add) a.data _ run)
  rintro t ⟨endPC,finalMem,finalRegs⟩
  refine ⟨endPC,?_,?_⟩
  · rw [lastMem]
    simpa only [copied4Memory,first4Memory,mem,regs] using finalMem
  · rw [finalRegs,regs]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem copy128_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s memory} (bits : s.regs.rbp=128) (size : s.regs.rax=16)
    (dest : s.regs.rsi.toBitVec=s.regs.rbx.toBitVec+32)
    (checked : copy s s.dmem=.ok memory) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x4d6 ∧ t.data.dmem=memory ∧ CopyFrame s.regs t.data.regs)
      ⟨s,Add.entry+0x4ad⟩ := by
  unfold copy at checked
  simp only [bits,show ((128 : UInt64).toNat==32)=false from rfl,Bool.false_eq_true,ite_false] at checked
  obtain ⟨high,highRead,checked⟩ := bind_ok checked
  obtain ⟨middle,highStore,checked⟩ := bind_ok checked
  obtain ⟨low,lowRead,checked⟩ := bind_ok checked
  obtain ⟨last,lowStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  obtain ⟨highMapped,highEq⟩ := store_facts highStore
  obtain ⟨lowMapped,lowEq⟩ := store_facts lowStore
  rw [store_nat64] at highEq lowEq
  have highMem : middle=highMemory s (.ofNat 64 high) := by
    simpa [highMemory,BitVec.ofNat_add,ofNat_uint64] using highEq
  have first := copy_high s (.ofNat 64 high) size dest
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using Exact.read_word64 highRead)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using highMapped)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r4ad_layout.agreement decoder.add) s _ first)
  rintro a ⟨pc1,mem1,regs1⟩
  rw [Placement.at_pc a _ pc1]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r4bf_layout.agreement decoder.add) a.data _
      (copy_loop_setup a.data (by simp only [regs1])))
  rintro b ⟨pc2,mem2,regs2⟩
  rw [Placement.at_pc b _ pc2]
  have third := copy_low b.data (.ofNat 64 low)
    (by simp only [regs2]) (by simp only [regs2])
    (by simpa only [regs2,regs1] using dest)
    (by simpa [highMem,mem2,mem1,regs2,regs1,ofNat_uint64] using Exact.read_word64 lowRead)
    (by simpa [highMem,mem2,mem1,regs2,regs1,BitVec.ofNat_add,ofNat_uint64] using lowMapped)
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r4c4_layout.agreement decoder.add) b.data _ third)
  rintro t ⟨pc3,mem3,regs3⟩
  refine ⟨pc3,?_,?_⟩
  · rw [mem3]
    simpa [lowMemory,mem2,mem1,regs2,regs1,highMem,BitVec.ofNat_add,ofNat_uint64] using lowEq.symm
  · rw [regs3,regs2,regs1]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem copy_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s : MachineData} {memory : DataMem}
    (family : s.regs.rbp.toNat=32 ∨ s.regs.rbp.toNat=128)
    (size : s.regs.rax=.ofNat (s.regs.rbp.toNat/8))
    (dest : s.regs.rsi.toBitVec=s.regs.rbx.toBitVec+32)
    (checked : copy s s.dmem=.ok memory) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x4d6 ∧ t.data.dmem=memory ∧ CopyFrame s.regs t.data.regs)
      ⟨s,if s.regs.rbp.toNat==32 then Add.entry+0x51f else Add.entry+0x4ad⟩ := by
  rcases family with four|six
  · have bits : s.regs.rbp=32 := by rw [←UInt64.ofNat_toNat (x:=s.regs.rbp),four]; rfl
    simpa only [four,beq_self_eq_true,ite_true] using
      copy4_checked fetch decoder bits (by simpa [four] using size) dest checked
  · have bits : s.regs.rbp=128 := by rw [←UInt64.ofNat_toNat (x:=s.regs.rbp),six]; rfl
    simpa only [six,show (128==32)=false from rfl,Bool.false_eq_true,ite_false] using
      copy128_checked fetch decoder bits (by simpa [six] using size) dest checked

theorem copy_congr {s t : MachineData} {before after : DataMem}
    (base : s.regs.rbx=t.regs.rbx) (bits : s.regs.rbp=t.regs.rbp)
    (query : s.regs.r13=t.regs.r13) (memory : before=after) :
    copy s before=copy t after := by
  simp only [copy,readNat,base,bits,query,memory]

#print axioms copy4_checked
#print axioms copy128_checked
end Binary.Pair.Allowedips.Root
