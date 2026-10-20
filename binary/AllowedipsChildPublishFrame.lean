import AllowedipsChildPublishChecked

namespace Binary.Pair.Allowedips.ChildPublish
open AllowedipsMutationImage Root
local instance : Labels := Image.linkedLabels

/-- Only the two words actually written. The resulting registers name the
loaded node and index even when those words overlap other input locations. -/
def Writes (before after : Reg64s) (a : BitVec 64) : Prop :=
  InRange (after.r8.toBitVec+48) 8 a ∨
    InRange (before.rbx.toBitVec+after.rax.toBitVec*8+8) 8 a

theorem effect_frame {s memory registers} (checked : effect s=.ok (memory,registers)) :
    EqualOutside (Writes s.regs registers) s.dmem memory := by
  unfold effect at checked
  obtain ⟨direction,_,checked⟩ := bind_ok checked
  obtain ⟨base,_,checked⟩ := bind_ok checked
  obtain ⟨middle,parentStore,checked⟩ := bind_ok checked
  obtain ⟨index,_,checked⟩ := bind_ok checked
  obtain ⟨last,linkStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have firstFrame : EqualOutside (InRange (.ofNat 64 (base+48)) 8) s.dmem middle := by
    rw [(store_facts parentStore).2]
    exact storeInt_frame _ _ _ _
  have secondFrame : EqualOutside (InRange (.ofNat 64 (s.regs.rbx.toNat+index*8+8)) 8) middle memory := by
    rw [(store_facts linkStore).2]
    exact storeInt_frame _ _ _ _
  intro a outside
  apply (firstFrame a ?_).trans (secondFrame a ?_)
  · intro inside
    apply outside (.inl ?_)
    simpa [UInt64.toBitVec_ofNat',BitVec.ofNat_add] using inside
  · intro inside
    apply outside (.inr ?_)
    simpa [UInt64.toBitVec_ofNat',BitVec.ofNat_add,BitVec.ofNat_mul,ofNat_uint64] using inside

theorem publication_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s : MachineData} {memory : DataMem} {registers : Reg64s}
    (checked : effect s=.ok (memory,registers)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.dmem=memory ∧ t.data.regs=registers ∧
        EqualOutside (Writes s.regs t.data.regs) s.dmem t.data.dmem)
      ⟨s,Add.entry+0x6f2⟩ := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (effect_segment fetch decoder checked)
  rintro t ⟨position,mem,regs⟩
  refine ⟨position,mem,regs,?_⟩
  rw [mem,regs]
  exact effect_frame checked

#print axioms publication_checked
end Binary.Pair.Allowedips.ChildPublish
