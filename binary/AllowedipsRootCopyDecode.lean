import AllowedipsHeaderDecode
import AllowedipsInternalFrame

namespace Binary.Pair.Allowedips.Root

theorem word_store_same (m : DataMem) (path : String) (address size value : Nat)
    (extent : address+size≤2^64) (small : value<2^(8*size)) :
    word (m.storeInt (.ofNat 64 address) size value) path address size=.ok value := by
  apply Trie.word_of_loadInt path extent
  have read := MemoryBytes.loadInt_store_subword m (.ofNat 64 address) size value
    (by omega) 0 size (by omega)
  have smallInt : (value : Int)<(2 : Int)^(8*size) := by exact_mod_cast small
  simpa [Int.emod_eq_of_lt (by omega : (0 : Int)≤value) smallInt] using read

theorem word_store_frame (m : DataMem) (path : String) (base offset size destination length value : Nat)
    (within : offset+size≤2^64) (writeBound : destination+length≤2^64)
    (apart : offset+size≤destination ∨ destination+length≤offset) :
    word (m.storeInt (.ofNat 64 (base+destination)) length value) path (base+offset) size=
      word m path (base+offset) size := by
  apply (Trie.word_frame (storeInt_frame m (.ofNat 64 (base+destination)) length value) path (base+offset) size _).symm
  simpa only [BitVec.ofNat_add] using InRange.offset_disjoint (.ofNat 64 base)
    offset size destination length within writeBound apart

private theorem read_agrees {s a size value expected path}
    (read : readNat s a size=.ok value) (decoded : word s.data.dmem path a size=.ok expected) :
    value=expected :=
  Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt read).symm.trans (word_loadInt _ _ _ _ _ decoded)))

/-- The duplicate IPv4 load is retained. Separation of the caller's query
from the destination is a local resource fact to be derived at allocation. -/
theorem copy4_key {s : MachineData} {before after : DataMem} {key : Nat}
    (width : s.regs.rbp.toNat=32) (extent : s.regs.rbx.toNat+36≤2^64)
    (query : word before "query" s.regs.r13.toNat 4=.ok key)
    (apart : ∀ a, InRange s.regs.r13.toBitVec 4 a →
      ¬InRange (.ofNat 64 (s.regs.rbx.toNat+32)) 4 a)
    (checked : copy s before=.ok after) :
    word after "node.key32" (s.regs.rbx.toNat+32) 4=.ok key ∧
      EqualOutside (InRange (.ofNat 64 (s.regs.rbx.toNat+32)) 4) before after := by
  unfold copy at checked
  simp only [width,beq_self_eq_true,ite_true] at checked
  obtain ⟨first,firstRead,checked⟩ := bind_ok checked
  obtain ⟨middle,firstStore,checked⟩ := bind_ok checked
  obtain ⟨again,againRead,checked⟩ := bind_ok checked
  obtain ⟨last,lastStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have firstKey : first=key := read_agrees firstRead query
  subst first
  have middleEq := (store_facts firstStore).2
  have firstFrame : EqualOutside (InRange (.ofNat 64 (s.regs.rbx.toNat+32)) 4) before middle := by
    rw [middleEq]; exact storeInt_frame _ _ _ _
  have queryAgain : word middle "query" s.regs.r13.toNat 4=.ok key := by
    rw [←Trie.word_frame firstFrame "query" s.regs.r13.toNat 4 (by
      simpa only [ofNat_uint64] using apart)]
    exact query
  have againKey : again=key := read_agrees againRead queryAgain
  subst again
  have afterEq := (store_facts lastStore).2
  refine ⟨?_,?_⟩
  · rw [afterEq]
    exact word_store_same _ _ _ _ _ extent (by simpa using word_bound query)
  · intro a outside
    rw [afterEq]
    exact (firstFrame a outside).trans (storeInt_frame _ _ _ _ a outside)

theorem copy128_key {s : MachineData} {before after : DataMem} {hi lo : Nat}
    (width : s.regs.rbp.toNat=128) (extent : s.regs.rbx.toNat+48≤2^64)
    (queryHi : word before "query.high" s.regs.r13.toNat 8=.ok hi)
    (queryLo : word before "query.low" (s.regs.r13.toNat+8) 8=.ok lo)
    (apart : ∀ a, InRange s.regs.r13.toBitVec 8 a →
      ¬InRange (.ofNat 64 (s.regs.rbx.toNat+40)) 8 a)
    (checked : copy s before=.ok after) :
    word after "node.key128.high" (s.regs.rbx.toNat+32) 8=.ok hi ∧
      word after "node.key128.low" (s.regs.rbx.toNat+40) 8=.ok lo ∧
      EqualOutside (InRange (.ofNat 64 (s.regs.rbx.toNat+32)) 16) before after := by
  unfold copy at checked
  simp only [width,show (128==32)=false from rfl,Bool.false_eq_true,ite_false] at checked
  obtain ⟨low,lowRead,checked⟩ := bind_ok checked
  obtain ⟨middle,lowStore,checked⟩ := bind_ok checked
  obtain ⟨high,highRead,checked⟩ := bind_ok checked
  obtain ⟨last,highStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have lowKey : low=lo := read_agrees lowRead queryLo
  subst low
  have middleEq := (store_facts lowStore).2
  have lowFrame : EqualOutside (InRange (.ofNat 64 (s.regs.rbx.toNat+40)) 8) before middle := by
    rw [middleEq]; exact storeInt_frame _ _ _ _
  have queryAgain : word middle "query.high" s.regs.r13.toNat 8=.ok hi := by
    rw [←Trie.word_frame lowFrame "query.high" s.regs.r13.toNat 8 (by
      simpa only [ofNat_uint64] using apart)]
    exact queryHi
  have highKey : high=hi := read_agrees highRead queryAgain
  subst high
  have afterEq := (store_facts highStore).2
  refine ⟨?_,?_,?_⟩
  · rw [afterEq]
    exact word_store_same _ _ _ _ _ (by omega) (by simpa using word_bound queryHi)
  · rw [afterEq,word_store_frame middle "node.key128.low" s.regs.rbx.toNat 40 8 32 8 hi
      (by decide) (by decide) (.inr (by decide)),middleEq]
    exact word_store_same _ _ _ _ _ extent (by simpa using word_bound queryLo)
  · intro a outside
    have outsideLow : ¬InRange (.ofNat 64 (s.regs.rbx.toNat+40)) 8 a := by
      rintro ⟨i,small,equal⟩
      apply outside
      refine ⟨8+i,by omega,?_⟩
      rw [←BitVec.ofNat_add]
      have sum : s.regs.rbx.toNat+32+(8+i)=s.regs.rbx.toNat+40+i := by omega
      rw [sum]
      simpa only [←BitVec.ofNat_add] using equal
    have outsideHigh : ¬InRange (.ofNat 64 (s.regs.rbx.toNat+32)) 8 a := by
      rintro ⟨i,small,equal⟩; exact outside ⟨i,by omega,equal⟩
    rw [afterEq]
    exact (lowFrame a outsideLow).trans (storeInt_frame _ _ _ _ a outsideHigh)

#print axioms copy4_key
#print axioms copy128_key
end Binary.Pair.Allowedips.Root
