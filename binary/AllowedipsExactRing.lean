import AllowedipsRingReassign
import AllowedipsExactWords

namespace Binary.Pair.Allowedips.Exact

private theorem uint_word (r : UInt64) : BitVec.ofNat 64 r.toNat=r.toBitVec :=
  (Trie.u64_of_nat rfl).symm

theorem removed_as_ring (s : MachineData) (previous next : Nat) :
    removedMemory s (.ofNat 64 previous) (.ofNat 64 next)=
      Ring.unlinkMemory (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) previous next := by
  simp only [removedMemory,nextMemory,ownerMemory,Ring.unlinkMemory,write64,
    BitVec.ofNat_add,uint_word]
  rfl

theorem added_as_ring (s : MachineData)
    (nodeLink : s.regs.rbx.toBitVec+56=s.regs.rdx.toBitVec) :
    addedMemory s=Ring.appendMemory s.dmem s.regs.r14.toNat s.regs.rax.toNat s.regs.rdx.toNat := by
  have nodeBack : s.regs.rbx.toBitVec+64=s.regs.rdx.toBitVec+8 := by
    rw [←nodeLink,BitVec.add_assoc]
    rfl
  simp only [addedMemory,backwardMemory,forwardMemory,headMemory,Ring.appendMemory,write64,
    BitVec.ofNat_add,uint_word,nodeLink,nodeBack]
  rfl

private theorem readNat_agrees {s a size value expected path}
    (read : readNat s a size=.ok value) (decoded : word s.data.dmem path a size=.ok expected) :
    value=expected :=
  Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt read).symm.trans (word_loadInt _ _ _ _ _ decoded)))

theorem removeEffect_ring {s memory regs head previous next}
    (headEq : head=s.regs.r14.toNat+1096) (headBound : head+16≤2^64)
    (back : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok previous)
    (forward : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok next)
    (checked : removeEffect s=.ok (memory,regs)) :
    ∃ last, word memory "peer.list.prev" (head+8) 8=.ok last ∧
      memory=Ring.unlinkMemory (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) previous next ∧
      regs={s.regs with
        rax := .ofBitVec (.ofNat 64 last),rcx := .ofBitVec (.ofNat 64 next),
        rdx := .ofBitVec (s.regs.rbx.toBitVec+56),r14 := .ofBitVec (s.regs.r14.toBitVec+1096)} := by
  unfold removeEffect at checked
  obtain ⟨p,pRead,checked⟩ := bind_ok checked
  obtain ⟨q,qRead,checked⟩ := bind_ok checked
  have peq := readNat_agrees pRead back
  have qeq := readNat_agrees qRead forward
  subst p; subst q
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨last,tailRead,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  refine ⟨last,?_,removed_as_ring s previous next,rfl⟩
  apply Trie.word_of_loadInt
  · omega
  · have read := Trie.readNat_loadInt tailRead
    simpa only [headEq,Nat.add_assoc] using read

theorem effect_ring {names o s memory regs head previous next}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (headSlot : LinkSlot names head) (nodeSlot : LinkSlot names (s.regs.rbx.toNat+56))
    (headEq : head=s.regs.r14.toNat+1096)
    (back : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok previous)
    (forward : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok next)
    (checked : effect s=.ok (memory,regs)) :
    ∃ last,
      word (Ring.unlinkMemory (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) previous next)
        "peer.list.prev" (head+8) 8=.ok last ∧
      memory=Ring.appendMemory
        (Ring.unlinkMemory (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) previous next)
        head last (s.regs.rbx.toNat+56) := by
  unfold effect at checked
  obtain ⟨⟨middle,registers⟩,removeCheck,appendCheck⟩ := bind_ok checked
  have headBound := (headSlot.word layout 8 (.inr rfl)).bounded g
  obtain ⟨last,tailRead,memoryEq,regsEq⟩ := removeEffect_ring headEq (by omega) back forward removeCheck
  unfold appendEffect at appendCheck
  obtain ⟨_,_,appendCheck⟩ := bind_ok appendCheck
  obtain ⟨_,_,appendCheck⟩ := bind_ok appendCheck
  obtain ⟨_,_,appendCheck⟩ := bind_ok appendCheck
  obtain ⟨_,_,appendCheck⟩ := bind_ok appendCheck
  cases Except.ok.inj appendCheck
  have lastBound : last<2^64 := word_bound tailRead
  have linkBound := Ring.link_bound nodeSlot g layout
  have r14 : registers.r14.toNat=head := by
    rw [regsEq]
    simp only [UInt64.toNat_ofBitVec,BitVec.toNat_add,UInt64.toNat_toBitVec]
    change (s.regs.r14.toNat+1096)%2^64=head
    rw [←headEq,Nat.mod_eq_of_lt (by omega)]
  have rax : registers.rax.toNat=last := by
    rw [regsEq]
    simp only [UInt64.toNat_ofBitVec,BitVec.toNat_ofNat,Nat.mod_eq_of_lt lastBound]
  have rdx : registers.rdx.toNat=s.regs.rbx.toNat+56 := by
    rw [regsEq]
    change (s.regs.rbx.toNat+56)%2^64=s.regs.rbx.toNat+56
    exact Nat.mod_eq_of_lt linkBound
  refine ⟨last,by simpa only [memoryEq] using tailRead,?_⟩
  rw [added_as_ring _ (by rw [regsEq])]
  simp only [r14,rax,rdx,memoryEq]

#print axioms effect_ring
end Binary.Pair.Allowedips.Exact
