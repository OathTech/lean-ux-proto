import AllowedipsRootStore

namespace Binary.Pair.Allowedips.Root
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem publish_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s memory} (checked : publish s s.dmem=.ok memory) :
    ∃ slot : BitVec 64,
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.dmem=memory ∧
      t.data.regs={s.regs with rax:=.ofBitVec (slot ||| 2),rdx:=.ofBitVec slot,rbx:=0})
      ⟨s,Add.entry+0x4d6⟩ := by
  unfold publish at checked
  obtain ⟨slot,saved,checked⟩ := bind_ok checked
  obtain ⟨middle,parentStore,rootStore⟩ := bind_ok checked
  obtain ⟨parentMapped,parentEq⟩ := store_facts parentStore
  obtain ⟨rootMapped,rootEq⟩ := store_facts rootStore
  rw [store_nat64] at parentEq rootEq
  have parent : middle=parentMemory s (.ofNat 64 slot) := by
    simpa [parentMemory,BitVec.ofNat_add,ofNat_uint64,BitVec.ofNat_or] using parentEq
  have root : memory=rootMemory s (.ofNat 64 slot) := by
    simpa [rootMemory,parent,ofNat_uint64] using rootEq
  refine ⟨.ofNat 64 slot,?_⟩
  rw [root]
  exact region_eventually (Add_r4d6_layout.agreement decoder.add) s _
    (connect s (.ofNat 64 slot)
      (by simpa [BitVec.ofNat_add,ofNat_uint64] using Exact.read_word64 saved)
      (by simpa [BitVec.ofNat_add,ofNat_uint64] using parentMapped)
      (by simpa only [parent] using rootMapped))

theorem publish_congr {s t : MachineData} {before after : DataMem}
    (base : s.regs.rbx=t.regs.rbx) (stack : s.regs.rsp=t.regs.rsp) (memory : before=after) :
    publish s before=publish t after := by
  simp only [publish,readNat,base,stack,memory]

#print axioms publish_checked
end Binary.Pair.Allowedips.Root
