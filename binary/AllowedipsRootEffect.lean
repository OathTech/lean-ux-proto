import AllowedipsRootHeaderChecked
import AllowedipsRootCopyChecked
import AllowedipsRootPublish

namespace Binary.Pair.Allowedips.Root
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

structure OutputRegisters (before after : Reg64s) : Prop where
  result : after.rbx=0
  stack : after.rsp=before.rsp
  bits : after.rbp=before.rbp
  kept12 : after.r12=before.r12
  query : after.r13=before.r13
  peerHead : after.r14=.ofBitVec (before.r14.toBitVec+1096)
  kept15 : after.r15=before.r15

/-- The complete tested empty-root tail, including both compiled key-copy
paths, realizes its executable memory effect. Allocation and reconstruction
before/after this segment are separate obligations. -/
theorem effect_segment (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s : MachineData} {memory : DataMem} (checked : effect s=.ok memory) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.dmem=memory ∧ OutputRegisters s.regs t.data.regs)
      ⟨s,Add.entry+0x443⟩ := by
  unfold effect at checked
  obtain ⟨⟨attached,cidr⟩,attachCheck,checked⟩ := bind_ok checked
  obtain ⟨withHeader,headerCheck,checked⟩ := bind_ok checked
  obtain ⟨copied,copyCheck,publishCheck⟩ := bind_ok checked
  obtain ⟨family,bound,attachment⟩ := attach_checked fetch decoder attachCheck
  apply eventually_trans (instructionStep fetch) _ _ _ attachment
  rintro a ⟨pcA,memA,regsA⟩
  rw [Placement.at_pc a _ pcA]
  have header := header_checked fetch decoder family bound
    (s:=a.data) (memory:=withHeader)
    (by simp only [regsA,attachedRegs]; exact UInt64.ofNat_toNat.symm)
    (by simp only [regsA,attachedRegs]) (by simp only [regsA,attachedRegs])
    (by simp only [regsA,attachedRegs]) (by simp only [regsA,attachedRegs])
    (by simp only [regsA,attachedRegs])
    (by simpa only [memA,regsA,attachedRegs] using headerCheck)
  apply eventually_trans (instructionStep fetch) _ _ _ header
  rintro h ⟨pcH,memH,regsH,carry⟩
  rw [Placement.at_pc h _ pcH]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r4ab_layout.agreement decoder.add) h.data _ (copy_branch h.data))
  rintro b ⟨dataB,pcB⟩
  have beforeCopy : copy b.data b.data.dmem=copy s withHeader := copy_congr
    (by simp only [dataB,regsH,headerRegs,regsA,attachedRegs])
    (by simp only [dataB,regsH,headerRegs,regsA,attachedRegs])
    (by simp only [dataB,regsH,headerRegs,regsA,attachedRegs])
    (by simp only [dataB,memH])
  have copiedRun := copy_checked fetch decoder
    (s:=b.data) (memory:=copied)
    (by simpa only [dataB,regsH,headerRegs,regsA,attachedRegs] using family)
    (by simp only [dataB,regsH,headerRegs,regsA,attachedRegs])
    (by simp only [dataB,regsH,headerRegs,regsA,attachedRegs])
    (beforeCopy.trans copyCheck)
  have copyPC : b.pc=(if b.data.regs.rbp.toNat==32 then Add.entry+0x51f else Add.entry+0x4ad) := by
    simpa only [carry,dataB,regsH,headerRegs,regsA,attachedRegs] using pcB
  rw [Placement.at_pc b _ copyPC]
  apply eventually_trans (instructionStep fetch) _ _ _ copiedRun
  rintro c ⟨pcC,memC,frame⟩
  rw [Placement.at_pc c _ pcC]
  have beforePublish : publish c.data c.data.dmem=publish s copied := publish_congr
    (by simpa only [dataB,regsH,headerRegs,regsA,attachedRegs] using frame.base)
    (by simpa only [dataB,regsH,headerRegs,regsA,attachedRegs] using frame.stack) memC
  obtain ⟨slot,published⟩ := publish_checked fetch decoder (beforePublish.trans publishCheck)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ published
  rintro t ⟨pcT,memT,regsT⟩
  refine ⟨pcT,memT,?_⟩
  rw [regsT]
  constructor
  · rfl
  · simpa only [dataB,regsH,headerRegs,regsA,attachedRegs] using frame.stack
  · simpa only [dataB,regsH,headerRegs,regsA,attachedRegs] using frame.bits
  · simpa only [dataB,regsH,headerRegs,regsA,attachedRegs] using frame.kept12
  · simpa only [dataB,regsH,headerRegs,regsA,attachedRegs] using frame.query
  · simpa only [dataB,regsH,headerRegs,regsA,attachedRegs] using frame.peer
  · simpa only [dataB,regsH,headerRegs,regsA,attachedRegs] using frame.kept15

#print axioms effect_segment
end Binary.Pair.Allowedips.Root
