import AllowedipsNodeCopyChecked

namespace Binary.Pair.Allowedips.NodeInit
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- The nonempty allocation tail executes its tested memory/register summary
through both address families. Publication and full-trie reconstruction are
separate obligations; successful summary evaluation is the local entry check. -/
theorem effect_segment (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s : MachineData} {memory : DataMem} {base : Nat}
    (checked : effect s=.ok (memory,base)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x1ff ∧ t.data.dmem=memory ∧ registers s.regs t.data.regs base=true)
      ⟨s,Add.entry+0x156⟩ := by
  unfold effect at checked
  obtain ⟨⟨attached,allocation,cidr⟩,attachCheck,checked⟩ := bind_ok checked
  obtain ⟨initialized,headerCheck,checked⟩ := bind_ok checked
  obtain ⟨copied,copyCheck,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  obtain ⟨family,bound,original,bits,attachment⟩ := attach_checked fetch decoder attachCheck
  have originalReg : s.regs.r12=.ofNat cidr := by
    rw [←UInt64.ofNat_toNat (x:=s.regs.r12),original]
  have bitsReg : s.regs.r15=.ofNat s.regs.rbp.toNat := by
    rw [←UInt64.ofNat_toNat (x:=s.regs.r15),bits]
  apply eventually_trans (instructionStep fetch) _ _ _ attachment
  rintro a ⟨pcA,memA,regsA⟩
  rw [Placement.at_pc a _ pcA]
  have header := header_checked fetch decoder family bound
    (s:=a.data) (memory:=initialized) (base:=base)
    (by simp only [regsA,attachedRegs]; exact UInt64.toBitVec_ofNat' base)
    (by simpa only [regsA,attachedRegs] using bitsReg)
    (by simp only [regsA,attachedRegs]) (by simp only [regsA,attachedRegs])
    (by simpa only [regsA,attachedRegs] using originalReg)
    (by simp only [regsA,attachedRegs])
    (by simpa only [memA,regsA,attachedRegs] using headerCheck)
  apply eventually_trans (instructionStep fetch) _ _ _ header
  rintro b ⟨pcB,memB,regsB⟩
  rw [Placement.at_pc b _ pcB]
  have beforeCopy : Root.copy (copyView b.data s.regs.rbp.toNat) b.data.dmem=
      Root.copy {s with regs:={s.regs with rbx:=.ofNat base}} initialized := Root.copy_congr
    (by simp only [copyView,regsB,headerRegs,regsA,attachedRegs])
    (by simp only [copyView]; exact UInt64.ofNat_toNat)
    (by simp only [copyView,regsB,headerRegs,regsA,attachedRegs]) memB
  have run := copy_checked fetch decoder family (s:=b.data) (memory:=memory)
    (by simp only [regsB,headerRegs,regsA,attachedRegs])
    (by simp only [regsB,headerRegs,regsA,attachedRegs]; rw [UInt64.toBitVec_ofNat'])
    (beforeCopy.trans copyCheck)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨pcT,memT,frame⟩
  refine ⟨pcT,memT,?_⟩
  simp only [registers,frame.stack,frame.parent,frame.kept12,frame.query,frame.kept15,
    frame.bytes,frame.base,frame.dest,regsB,headerRegs,regsA,attachedRegs]
  simp
  rfl

#print axioms effect_segment
end Binary.Pair.Allowedips.NodeInit
