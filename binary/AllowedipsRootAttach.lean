import AllowedipsRootStore

namespace Binary.Pair.Allowedips.Root
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def attachedRegs (s : MachineData) (cidr : Nat) : Reg64s :=
  {s.regs with
    rax:=.ofNat (s.regs.rbp.toNat/8),rcx:=.ofNat (s.regs.rbp.toNat/8-1),
    rdx:=.ofNat cidr,rsi:=.ofNat (cidr/8),rdi:=.ofNat cidr,
    r14:=.ofBitVec (s.regs.r14.toBitVec+1096)}

/-- Realize the tested attachment phase; all mapped-word premises come from
its successful executable reads and writes in their original order. -/
theorem attach_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s memory cidr} (checked : attach s=.ok (memory,cidr)) :
    (s.regs.rbp.toNat=32 ∨ s.regs.rbp.toNat=128) ∧ cidr≤s.regs.rbp.toNat ∧
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x481 ∧ t.data.dmem=memory ∧ t.data.regs=attachedRegs s cidr)
      ⟨s,Add.entry+0x443⟩ := by
  unfold attach at checked
  obtain ⟨_,familyCheck,checked⟩ := bind_ok checked
  obtain ⟨m1,ownerStore,checked⟩ := bind_ok checked
  obtain ⟨requested,cidrRead,checked⟩ := bind_ok checked
  obtain ⟨_,boundCheck,checked⟩ := bind_ok checked
  obtain ⟨last,tailRead,checked⟩ := bind_ok checked
  obtain ⟨m2,headStore,checked⟩ := bind_ok checked
  obtain ⟨m3,forwardStore,checked⟩ := bind_ok checked
  obtain ⟨m4,backStore,checked⟩ := bind_ok checked
  obtain ⟨m5,lastStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have family : s.regs.rbp.toNat=32 ∨ s.regs.rbp.toNat=128 := by
    simpa [Bool.or_eq_true,beq_iff_eq] using require_ok familyCheck
  have bound : cidr≤s.regs.rbp.toNat := by simpa using require_ok boundCheck
  have small : cidr<2^32 := by rcases family with h|h <;> omega
  have extended : (BitVec.ofNat 32 cidr).setWidth 64=BitVec.ofNat 64 cidr :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) small
  have cidrReg : UInt64.ofBitVec ((BitVec.ofNat 32 cidr).setWidth 64)=UInt64.ofNat cidr := by
    rw [extended]
    rfl
  obtain ⟨ownerMapped,ownerEq⟩ := store_facts ownerStore
  rw [store_nat64] at ownerEq
  have owner : m1=ownerMemory s := by
    simpa [ofNat_uint64,ownerMemory] using ownerEq
  obtain ⟨headMapped,headEq⟩ := store_facts headStore
  rw [store_nat64] at headEq
  have head : m2=headMemory s := by
    simpa [owner,ofNat_uint64,BitVec.ofNat_add,headMemory] using headEq
  obtain ⟨forwardMapped,forwardEq⟩ := store_facts forwardStore
  rw [store_nat64] at forwardEq
  have forward : m3=forwardMemory s := by
    simpa [head,ofNat_uint64,BitVec.ofNat_add,forwardMemory] using forwardEq
  obtain ⟨backMapped,backEq⟩ := store_facts backStore
  obtain ⟨lastMapped,lastEq⟩ := store_facts lastStore
  rw [store_nat64] at backEq lastEq
  have firstRun := attach_first s (.ofNat 32 cidr) (.ofNat 64 last)
    (by simpa [ofNat_uint64] using ownerMapped)
    (by simpa [owner,BitVec.ofNat_add,ofNat_uint64] using read_word32 cidrRead)
    (by simpa [owner,BitVec.ofNat_add,ofNat_uint64] using Exact.read_word64 tailRead)
    (by simpa [head,BitVec.ofNat_add,ofNat_uint64] using forwardMapped)
  refine ⟨family,bound,?_⟩
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r443_layout.agreement decoder.add) s _ firstRun)
  rintro t ⟨pc,mem,regs⟩
  have back : backwardMemory t.data=m4 := by
    simp only [backwardMemory,mem,regs]
    simpa [forward,ofNat_uint64,BitVec.ofNat_add] using backEq.symm
  have finalMemory : linkedMemory t.data=memory := by
    simp only [linkedMemory,back,regs]
    simpa [ofNat_uint64,BitVec.ofNat_add] using lastEq.symm
  have secondRun := attach_second t.data s.regs.rbp.toNat cidr family bound
    (by simp only [regs]; exact UInt64.ofNat_toNat.symm)
    (by simp only [regs,extended]; rfl)
    (by simp only [regs,extended]; rfl)
    (by simpa [mem,regs,forward,BitVec.ofNat_add,ofNat_uint64] using backMapped)
    (by simpa [back,regs] using lastMapped)
  rw [Placement.at_pc t _ pc]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r469_layout.agreement decoder.add) t.data _ secondRun)
  rintro result ⟨atEnd,memoryEq,registersEq⟩
  refine ⟨atEnd,memoryEq.trans finalMemory,?_⟩
  simpa only [regs,attachedRegs,cidrReg] using registersEq

#print axioms attach_checked
end Binary.Pair.Allowedips.Root
