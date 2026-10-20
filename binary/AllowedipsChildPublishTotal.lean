import AllowedipsChildPublishRecord
import AllowedipsRootTotalMemory

namespace Binary.Pair.Allowedips.ChildPublish
open Root

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- Saved inputs and mapped destinations suffice to execute publication. The
index is read after the first store, with its value derived by the byte frame. -/
theorem effect_total {s : MachineData} {base direction : Nat}
    (baseRead : word s.dmem "saved.base" s.regs.rsp.toNat 8=.ok base)
    (directionRead : word s.dmem "saved.direction" (s.regs.rsp.toNat+8) 1=.ok direction)
    (indexRead : word s.dmem "saved.index" (s.regs.rsp.toNat+16) 8=.ok direction)
    (parentMapped : (s.dmem.loadInt (.ofNat 64 (base+48)) 8).isSome=true)
    (childMapped : (s.dmem.loadInt (.ofNat 64 (s.regs.rbx.toNat+direction*8+8)) 8).isSome=true)
    (indexApart : ∀ a, InRange (.ofNat 64 (s.regs.rsp.toNat+16)) 8 a →
      ¬InRange (.ofNat 64 (base+48)) 8 a) :
    ∃ memory registers, effect s=.ok (memory,registers) ∧
      registers.rsp=s.regs.rsp ∧ registers.rbx=0 ∧ registers.r8.toNat=base ∧ registers.rax.toNat=direction := by
  let slot : BitVec 64 := s.regs.rbx.toBitVec+.ofNat 64 (((direction+1)%256)*8)
  let packed := slot ||| .ofNat 64 direction
  let middle := s.dmem.storeInt (.ofNat 64 (base+48)) 8 packed.toNat
  have first : store s.dmem (base+48) 8 packed.toNat=.ok middle := store_total parentMapped
  have savedAfter : word middle "saved.index" (s.regs.rsp.toNat+16) 8=.ok direction :=
    (Trie.word_frame (storeInt_frame _ _ _ _) _ _ _ indexApart).symm.trans indexRead
  let memory := middle.storeInt (.ofNat 64 (s.regs.rbx.toNat+direction*8+8)) 8 base
  have last : store middle (s.regs.rbx.toNat+direction*8+8) 8 base=.ok memory :=
    store_total ((MappedLe.store _ _ _ _) _ _ childMapped)
  let registers := {s.regs with
    rax:=UInt64.ofNat direction,rbx:=0,
    rcx:=UInt64.ofBitVec slot,rdx:=UInt64.ofBitVec packed,r8:=UInt64.ofNat base}
  have baseLoad : readNat ⟨s,0⟩ s.regs.rsp.toNat 8=.ok base := readNat_of_word baseRead
  have directionLoad : readNat ⟨s,0⟩ (s.regs.rsp.toNat+8) 1=.ok direction := readNat_of_word directionRead
  have indexLoad : readNat ⟨{s with dmem:=middle},0⟩ (s.regs.rsp.toNat+16) 8=.ok direction :=
    readNat_of_word savedAfter
  dsimp only [packed,slot] at first
  refine ⟨memory,registers,?_,rfl,rfl,?_,?_⟩
  · simp only [effect,baseLoad,directionLoad,indexLoad,first,last,ok_bind]
    rfl
  · exact UInt64.toNat_ofNat_of_lt' (by simpa using word_bound baseRead)
  · exact UInt64.toNat_ofNat_of_lt' (by simpa using word_bound indexRead)

theorem effect_mapped {s : MachineData} {memory registers}
    (checked : effect s=.ok (memory,registers)) : MappedLe s.dmem memory := by
  unfold effect at checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,first,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,last,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  exact (store_mapped first).trans (store_mapped last)

#print axioms effect_total
end Binary.Pair.Allowedips.ChildPublish
