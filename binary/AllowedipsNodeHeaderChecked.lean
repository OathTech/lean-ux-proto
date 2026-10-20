import AllowedipsNodeHeaderFinish
import AllowedipsRootHeaderChecked

namespace Binary.Pair.Allowedips.NodeInit
open AllowedipsMutationImage Root
local instance : Labels := Image.linkedLabels

theorem low_byte_nat (value : Nat) :
    (UInt64.ofNat value).toBitVec.extractLsb' 0 8=BitVec.ofNat 8 value := by
  rw [UInt64.toBitVec_ofNat',←BitVec.setWidth_eq_extractLsb' (by decide),
    BitVec.setWidth_ofNat_of_le (by decide)]

def headerRegs (s : MachineData) (width cidr : Nat) : Reg64s :=
  {s.regs with
    rax:=.ofNat (headerWord width cidr),rdx:=.ofNat ((7-cidr%8)*65536),
    rcx:=.ofNat (width*16777216)}

theorem header_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s memory base width cidr} (family : width=32 ∨ width=128) (bound : cidr≤width)
    (node : s.regs.r8.toBitVec=.ofNat 64 base) (bits : s.regs.r15=.ofNat width)
    (bytes : s.regs.rbp=.ofNat (width/8)) (requested : s.regs.rdi=.ofNat cidr)
    (original : s.regs.r12=.ofNat cidr) (mask : s.regs.rax=.ofNat ((width/8-1)%8))
    (checked : header s.regs.rsp.toNat width base cidr s.dmem=.ok memory) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if width=32 then Add.entry+0x1de else Add.entry+0x4ed) ∧
      t.data.dmem=memory ∧ t.data.regs=headerRegs s width cidr) ⟨s,Add.entry+0x198⟩ := by
  unfold header at checked
  obtain ⟨m1,maskStore,checked⟩ := bind_ok checked
  obtain ⟨m2,indexStore,checked⟩ := bind_ok checked
  obtain ⟨m3,shiftStore,packedStore⟩ := bind_ok checked
  obtain ⟨maskMapped,maskEq⟩ := store_facts maskStore
  obtain ⟨indexMapped,indexEq⟩ := store_facts indexStore
  obtain ⟨shiftMapped,shiftEq⟩ := store_facts shiftStore
  obtain ⟨packedMapped,packedEq⟩ := store_facts packedStore
  rw [store_nat] at maskEq indexEq shiftEq packedEq
  have firstRun := header_first s width cidr family bound mask requested
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using maskMapped)
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r198_layout.agreement decoder.add) s _ firstRun)
  rintro a ⟨pcA,memA,regsA⟩
  have memoryA : a.data.dmem=m1 := by
    rw [memA]
    simpa [ofNat_uint64,BitVec.ofNat_add] using maskEq.symm
  have indexMemory : selectorMemory a.data=m2 := by
    have lowByte : a.data.regs.get (.low .rax .W8)=BitVec.ofNat 8 (selector width cidr) := by
      rw [regsA]
      simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
        Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self] using low_byte_nat (selector width cidr)
    rw [selectorMemory,memoryA,lowByte]
    have stack : a.data.regs.rsp=s.regs.rsp := by simp only [regsA]
    rw [stack]
    change m2=m1.storeInt (.ofNat 64 (s.regs.rsp.toNat+43)) 1
      (BitVec.ofNat 8 (selector width cidr)).toInt at indexEq
    rw [BitVec.ofNat_add,ofNat_uint64] at indexEq
    exact indexEq.symm
  have secondRun := header_second a.data width cidr family bound
    (by simp only [regsA]) (by simp only [regsA]) (by simp only [regsA])
    (by simpa only [regsA] using original)
    (by simpa [memoryA,regsA,ofNat_uint64,BitVec.ofNat_add] using indexMapped)
    (by simpa [indexMemory,regsA,ofNat_uint64,BitVec.ofNat_add] using shiftMapped)
  rw [Placement.at_pc a _ pcA]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r1ab_layout.agreement decoder.add) a.data _ secondRun)
  rintro b ⟨pcB,memB,regsB⟩
  have memoryB : b.data.dmem=m3 := by
    rw [memB,indexMemory]
    simpa [regsA,ofNat_uint64,BitVec.ofNat_add] using shiftEq.symm
  have thirdRun := NodeInit.header_pack b.data width cidr family bound
    (by simp only [regsB]) (by simp only [regsB]) (by simpa only [regsB,regsA] using bits)
  rw [Placement.at_pc b _ pcB]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually ((AllowedipsLoop.layout_take Add_r1c4_layout 5).agreement decoder.add) b.data _ thirdRun)
  rintro c ⟨pcC,memC,regsC⟩
  have wordReg : UInt64.ofBitVec ((BitVec.ofNat 32 (headerWord width cidr)).setWidth 64)=
      UInt64.ofNat (headerWord width cidr) := by
    rw [BitVec.setWidth_ofNat_of_le_of_lt (by decide) (header_bound family bound)]
    rfl
  have finish := NodeInit.header_finish c.data (.ofNat 32 (headerWord width cidr)) width family
    (by simpa only [regsC,regsB,regsA] using bytes) (by simp only [regsC,wordReg])
    (by simpa [memC,memoryB,regsC,regsB,regsA,node,BitVec.ofNat_add] using packedMapped)
  have layout : LaidOut Add.fetch (Add.entry+0x1d1) (Add.r1c4.drop 5) := by binary_layout
  rw [Placement.at_pc c _ pcC]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (layout.agreement decoder.add) c.data _ finish)
  rintro t ⟨position,memoryEq,registers⟩
  refine ⟨position,?_,?_⟩
  · rw [memoryEq]
    simpa [memC,memoryB,regsC,regsB,regsA,node,BitVec.ofNat_add] using packedEq.symm
  · simp only [registers,regsC,regsB,regsA,headerRegs]

#print axioms header_checked
end Binary.Pair.Allowedips.NodeInit
