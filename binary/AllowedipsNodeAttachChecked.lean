import AllowedipsNodeAttachRegions
import AllowedipsRootStore

namespace Binary.Pair.Allowedips.NodeInit
open AllowedipsMutationImage Root
local instance : Labels := Image.linkedLabels

def attachedRegs (s : MachineData) (base cidr : Nat) : Reg64s :=
  {s.regs with
    r8:=.ofNat base,r9:=.ofNat (s.regs.rbp.toNat/8),rdi:=.ofNat cidr,
    rax:=.ofNat ((s.regs.rbp.toNat/8-1)%8),rdx:=.ofBitVec (.ofNat 64 base+56),
    r14:=.ofBitVec (.ofNat 64 base+32),rbp:=.ofNat (s.regs.rbp.toNat/8)}

/-- The tested nonempty attachment phase executes the actual sixteen
instructions. No list update or successful intermediate store is assumed. -/
theorem attach_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s memory base cidr} (checked : NodeInit.attach s=.ok (memory,base,cidr)) :
    (s.regs.rbp.toNat=32 ∨ s.regs.rbp.toNat=128) ∧
    cidr≤s.regs.rbp.toNat ∧ s.regs.r12.toNat=cidr ∧ s.regs.r15.toNat=s.regs.rbp.toNat ∧
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x198 ∧ t.data.dmem=memory ∧ t.data.regs=attachedRegs s base cidr)
      ⟨s,Add.entry+0x156⟩ := by
  unfold NodeInit.attach at checked
  obtain ⟨allocation,baseRead,checked⟩ := bind_ok checked
  obtain ⟨requested,cidrRead,checked⟩ := bind_ok checked
  obtain ⟨last,tailRead,checked⟩ := bind_ok checked
  obtain ⟨_,familyCheck,checked⟩ := bind_ok checked
  obtain ⟨_,localsCheck,checked⟩ := bind_ok checked
  obtain ⟨m1,ownerStore,checked⟩ := bind_ok checked
  obtain ⟨m2,headStore,checked⟩ := bind_ok checked
  obtain ⟨m3,backStore,checked⟩ := bind_ok checked
  obtain ⟨m4,forwardStore,checked⟩ := bind_ok checked
  obtain ⟨m5,lastStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have family : s.regs.rbp.toNat=32 ∨ s.regs.rbp.toNat=128 := by
    simpa [Bool.or_eq_true,beq_iff_eq] using require_ok familyCheck
  have locals : (cidr≤s.regs.rbp.toNat ∧ s.regs.r12.toNat=cidr) ∧ s.regs.r15.toNat=s.regs.rbp.toNat := by
    simpa [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using require_ok localsCheck
  have small : cidr<2^32 := by rcases family with h|h <;> omega
  have extended : (BitVec.ofNat 32 cidr).setWidth 64=BitVec.ofNat 64 cidr :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) small
  obtain ⟨ownerMapped,ownerEq⟩ := store_facts ownerStore
  obtain ⟨headMapped,headEq⟩ := store_facts headStore
  obtain ⟨backMapped,backEq⟩ := store_facts backStore
  obtain ⟨forwardMapped,forwardEq⟩ := store_facts forwardStore
  obtain ⟨lastMapped,lastEq⟩ := store_facts lastStore
  rw [store_nat64] at ownerEq headEq backEq forwardEq lastEq
  have owner : m1=s.dmem.storeInt (.ofNat 64 base) 8 s.regs.r14.toBitVec.toInt := by
    simpa [ofNat_uint64] using ownerEq
  have firstRun := first s (.ofNat 64 base) (.ofNat 32 cidr) (.ofNat 64 last)
    s.regs.rbp.toNat family UInt64.ofNat_toNat.symm
    (by simpa [ofNat_uint64] using Exact.read_word64 baseRead)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using read_word32 cidrRead)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using Exact.read_word64 tailRead)
    ownerMapped
  refine ⟨family,locals.1.1,locals.1.2,locals.2,?_⟩
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r156_layout.agreement decoder.add) s _ firstRun)
  rintro a ⟨pcA,memA,regsA⟩
  have initialMemory : a.data.dmem=m1 := memA.trans owner.symm
  have head : headMemory a.data=m2 := by
    simp only [headMemory,initialMemory,regsA]
    simpa [ofNat_uint64,BitVec.ofNat_add,BitVec.add_assoc] using headEq.symm
  have back : backMemory a.data=m3 := by
    simp only [backMemory,head,regsA]
    simpa [BitVec.ofNat_add] using backEq.symm
  have forward : forwardMemory a.data=m4 := by
    simp only [forwardMemory,back,regsA]
    simpa [ofNat_uint64,BitVec.ofNat_add] using forwardEq.symm
  have linked : linkedMemory a.data=memory := by
    simp only [linkedMemory,forward,regsA]
    simpa [BitVec.ofNat_add] using lastEq.symm
  have secondRun := second a.data (s.regs.rbp.toNat/8)
    (by rcases family with h|h <;> simp [h]) (by simp only [regsA])
    (by simpa [initialMemory,regsA,BitVec.ofNat_add,ofNat_uint64,BitVec.add_assoc] using headMapped)
    (by simpa [head,regsA,BitVec.ofNat_add] using backMapped)
    (by simpa [back,regsA,BitVec.ofNat_add] using forwardMapped)
    (by simpa [forward,regsA] using lastMapped)
  rw [Placement.at_pc a _ pcA]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r17a_layout.agreement decoder.add) a.data _ secondRun)
  rintro t ⟨position,memoryEq,registers⟩
  refine ⟨position,memoryEq.trans linked,?_⟩
  simp only [registers,regsA,attachedRegs,extended]
  rfl

#print axioms attach_checked
end Binary.Pair.Allowedips.NodeInit
