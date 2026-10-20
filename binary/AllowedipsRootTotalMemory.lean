import PairMappedMemory
import AllowedipsRootStore

namespace Binary.Pair.Allowedips.Root

theorem store_total {memory address size value}
    (mapped : (memory.loadInt (.ofNat 64 address) size).isSome=true) :
    store memory address size value=.ok (memory.storeInt (.ofNat 64 address) size value) := by
  simp only [store,mapped,require,ite_true]
  rfl

theorem store_mapped {before after address size value} (run : store before address size value=.ok after) :
    MappedLe before after := by
  rw [(store_facts run).2]
  exact MappedLe.store _ _ _ _

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- The copy executes from readability alone, including overlapping sources.
Preservation of the intended key is a separate value/frame obligation. -/
theorem copy_total {s : MachineData} {memory : DataMem}
    (query : if s.regs.rbp.toNat=32 then
      (memory.loadInt (.ofNat 64 s.regs.r13.toNat) 4).isSome=true else
      (memory.loadInt (.ofNat 64 s.regs.r13.toNat) 8).isSome=true ∧
        (memory.loadInt (.ofNat 64 (s.regs.r13.toNat+8)) 8).isSome=true)
    (destination : ∀ offset size, offset+size≤16 →
      (memory.loadInt (.ofNat 64 (s.regs.rbx.toNat+32+offset)) size).isSome=true) :
    ∃ after, copy s memory=.ok after ∧ MappedLe memory after := by
  by_cases four : s.regs.rbp.toNat=32
  · rw [ite_eq_left four] at query
    obtain ⟨first,read⟩ := readNat_exists (s:=⟨{s with dmem:=memory},0⟩) query
    let middle := memory.storeInt (.ofNat 64 (s.regs.rbx.toNat+32)) 4 first
    have preserved : MappedLe memory middle := MappedLe.store _ _ _ _
    have firstStore : store memory (s.regs.rbx.toNat+32) 4 first=.ok middle :=
      store_total (by simpa only [Nat.add_zero] using destination 0 4 (by decide))
    obtain ⟨again,second⟩ := readNat_exists (s:=⟨{s with dmem:=middle},0⟩) (preserved _ _ query)
    let after := middle.storeInt (.ofNat 64 (s.regs.rbx.toNat+32)) 4 again
    have secondStore : store middle (s.regs.rbx.toNat+32) 4 again=.ok after :=
      store_total (preserved _ _ (by simpa only [Nat.add_zero] using destination 0 4 (by decide)))
    refine ⟨after,?_,preserved.trans (MappedLe.store _ _ _ _)⟩
    simp only [copy,beq_iff_eq,four,ite_true,read,firstStore,second,secondStore,ok_bind]
    rfl
  · rw [ite_eq_right four] at query
    obtain ⟨last,read⟩ := readNat_exists (s:=⟨{s with dmem:=memory},0⟩) query.2
    let middle := memory.storeInt (.ofNat 64 (s.regs.rbx.toNat+40)) 8 last
    have preserved : MappedLe memory middle := MappedLe.store _ _ _ _
    have firstStore : store memory (s.regs.rbx.toNat+40) 8 last=.ok middle :=
      store_total (by simpa only [Nat.add_assoc,Nat.reduceAdd] using destination 8 8 (by decide))
    obtain ⟨first,second⟩ := readNat_exists (s:=⟨{s with dmem:=middle},0⟩) (preserved _ _ query.1)
    let after := middle.storeInt (.ofNat 64 (s.regs.rbx.toNat+32)) 8 first
    have secondStore : store middle (s.regs.rbx.toNat+32) 8 first=.ok after :=
      store_total (preserved _ _ (by simpa only [Nat.add_zero] using destination 0 8 (by decide)))
    refine ⟨after,?_,preserved.trans (MappedLe.store _ _ _ _)⟩
    simp only [copy,beq_iff_eq,four,ite_false,read,firstStore,second,secondStore,ok_bind]
    rfl

theorem publish_total {s : MachineData} {memory : DataMem} {slot : Nat}
    (saved : readNat ⟨{s with dmem:=memory},0⟩ (s.regs.rsp.toNat+8) 8=.ok slot)
    (parent : (memory.loadInt (.ofNat 64 (s.regs.rbx.toNat+48)) 8).isSome=true)
    (root : (memory.loadInt (.ofNat 64 slot) 8).isSome=true) :
    ∃ after, publish s memory=.ok after ∧ MappedLe memory after := by
  let middle := memory.storeInt (.ofNat 64 (s.regs.rbx.toNat+48)) 8 ((slot ||| 2 : Nat) : Int)
  have first : store memory (s.regs.rbx.toNat+48) 8 (slot ||| 2)=.ok middle := store_total parent
  have preserved : MappedLe memory middle := MappedLe.store _ _ _ _
  let after := middle.storeInt (.ofNat 64 slot) 8 s.regs.rbx.toNat
  have last : store middle slot 8 s.regs.rbx.toNat=.ok after := store_total (preserved _ _ root)
  refine ⟨after,?_,preserved.trans (MappedLe.store _ _ _ _)⟩
  simp only [publish,saved,first,last,ok_bind]

#print axioms copy_total
#print axioms publish_total
end Binary.Pair.Allowedips.Root
