import AllowedipsNodeCopyRegions
import AllowedipsRootCopyChecked

namespace Binary.Pair.Allowedips.NodeInit
open AllowedipsMutationImage Root
local instance : Labels := Image.linkedLabels

def copyView (s : MachineData) (width : Nat) : MachineData :=
  {s with regs:={s.regs with rbx:=s.regs.r8,rbp:=.ofNat width}}

structure CopyFrame (before after : Reg64s) : Prop where
  stack : after.rsp=before.rsp
  parent : after.rbx=before.rbx
  bytes : after.rbp=before.rbp
  kept12 : after.r12=before.r12
  query : after.r13=before.r13
  kept15 : after.r15=before.r15
  base : after.r8=before.r8
  dest : after.r14=before.r14

theorem copy4_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s memory} (bytes : s.regs.rbp=4)
    (dest : s.regs.r14.toBitVec=s.regs.r8.toBitVec+32)
    (checked : Root.copy (copyView s 32) s.dmem=.ok memory) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x1ff ∧ t.data.dmem=memory ∧ CopyFrame s.regs t.data.regs)
      ⟨s,Add.entry+0x1de⟩ := by
  unfold Root.copy copyView at checked
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
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r1de_layout.agreement decoder.add) s _ (copy4_branch s bytes))
  rintro a ⟨pcA,memA,regsA⟩
  rw [Placement.at_pc a _ pcA]
  have run := NodeInit.copy4 a.data (.ofNat 32 first) (.ofNat 32 again)
    (regsA ▸ bytes) (by simpa only [regsA] using dest)
    (by simpa [memA,regsA,ofNat_uint64] using read_word32 firstRead)
    (by simpa [memA,regsA,BitVec.ofNat_add,ofNat_uint64] using firstMapped)
    (by simpa [firstMem,first4Memory,memA,regsA,ofNat_uint64] using read_word32 againRead)
    (by simpa [firstMem,first4Memory,memA,regsA,BitVec.ofNat_add,ofNat_uint64] using againMapped)
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r740_layout.agreement decoder.add) a.data _ run)
  rintro t ⟨pcT,memT,regsT⟩
  refine ⟨pcT,?_,?_⟩
  · rw [memT]
    simpa [firstMem,first4Memory,memA,regsA,BitVec.ofNat_add,ofNat_uint64] using againEq.symm
  · rw [regsT,regsA]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem copy128_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s memory} (bytes : s.regs.rbp=16)
    (dest : s.regs.r14.toBitVec=s.regs.r8.toBitVec+32)
    (checked : Root.copy (copyView s 128) s.dmem=.ok memory) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x1ff ∧ t.data.dmem=memory ∧ CopyFrame s.regs t.data.regs)
      ⟨s,Add.entry+0x4ed⟩ := by
  unfold Root.copy copyView at checked
  obtain ⟨high,highRead,checked⟩ := bind_ok checked
  obtain ⟨middle,highStore,checked⟩ := bind_ok checked
  obtain ⟨low,lowRead,checked⟩ := bind_ok checked
  obtain ⟨last,lowStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  obtain ⟨highMapped,highEq⟩ := store_facts highStore
  obtain ⟨lowMapped,lowEq⟩ := store_facts lowStore
  rw [store_nat64] at highEq lowEq
  have first := copy6_high s (.ofNat 64 high) bytes
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using Exact.read_word64 highRead)
    (by simpa [dest,BitVec.add_assoc,BitVec.ofNat_add,ofNat_uint64] using highMapped)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r4ed_layout.agreement decoder.add) s _ first)
  rintro a ⟨pcA,memA,regsA⟩
  have memoryA : a.data.dmem=middle := by
    rw [memA]
    simpa [dest,BitVec.add_assoc,BitVec.ofNat_add,ofNat_uint64] using highEq.symm
  rw [Placement.at_pc a _ pcA]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r503_layout.agreement decoder.add) a.data _
      (copy6_setup a.data (by simp only [regsA])))
  rintro b ⟨pcB,memB,regsB⟩
  rw [Placement.at_pc b _ pcB]
  have third := copy6_low b.data (.ofNat 64 low)
    (by simp only [regsB]) (by simp only [regsB])
    (by simpa [memB,memoryA,regsB,regsA,ofNat_uint64] using Exact.read_word64 lowRead)
    (by simpa [memB,memoryA,regsB,regsA,dest,BitVec.ofNat_add,ofNat_uint64] using lowMapped)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r508_layout.agreement decoder.add) b.data _ third)
  rintro c ⟨pcC,memC,regsC⟩
  rw [Placement.at_pc c _ pcC]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r51a_layout.agreement decoder.add) c.data _ (copy6_finish c.data))
  rintro t ⟨pcT,dataT⟩
  refine ⟨pcT,?_,?_⟩
  · rw [dataT,memC]
    simpa [memB,memoryA,regsB,regsA,dest,BitVec.ofNat_add,ofNat_uint64] using lowEq.symm
  · rw [dataT,regsC,regsB,regsA]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem copy_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s memory width} (family : width=32 ∨ width=128)
    (bytes : s.regs.rbp=.ofNat (width/8))
    (dest : s.regs.r14.toBitVec=s.regs.r8.toBitVec+32)
    (checked : Root.copy (copyView s width) s.dmem=.ok memory) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x1ff ∧ t.data.dmem=memory ∧ CopyFrame s.regs t.data.regs)
      ⟨s,if width=32 then Add.entry+0x1de else Add.entry+0x4ed⟩ := by
  rcases family with rfl|rfl
  · exact copy4_checked fetch decoder bytes dest checked
  · exact copy128_checked fetch decoder bytes dest checked

#print axioms copy_checked
end Binary.Pair.Allowedips.NodeInit
