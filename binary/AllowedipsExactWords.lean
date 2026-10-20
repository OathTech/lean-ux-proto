import AllowedipsExactEffect
import PairWordWrites

namespace Binary.Pair.Allowedips.Exact

private theorem uint_word (r : UInt64) : BitVec.ofNat 64 r.toNat=r.toBitVec :=
  (Trie.u64_of_nat rfl).symm

def removeWrites (s : MachineData) (previous next : BitVec 64) : List (Nat × Nat) :=
  [(s.regs.rbx.toNat,s.regs.r14.toNat),((next+8).toNat,previous.toNat),(previous.toNat,next.toNat)]

def appendWrites (s : MachineData) : List (Nat × Nat) :=
  [((s.regs.r14.toBitVec+8).toNat,s.regs.rdx.toNat),
    ((s.regs.rbx.toBitVec+56).toNat,s.regs.r14.toNat),
    ((s.regs.rbx.toBitVec+64).toNat,s.regs.rax.toNat),(s.regs.rax.toNat,s.regs.rdx.toNat)]

theorem removed_as_words (s : MachineData) (previous next : BitVec 64) :
    removedMemory s previous next=writeWords s.dmem (removeWrites s previous next) := by
  simp only [removedMemory,nextMemory,ownerMemory,writeWords,removeWrites,List.foldl_cons,List.foldl_nil,
    write64,uint_word,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem added_as_words (s : MachineData) : addedMemory s=writeWords s.dmem (appendWrites s) := by
  simp only [addedMemory,backwardMemory,forwardMemory,headMemory,writeWords,appendWrites,
    List.foldl_cons,List.foldl_nil,write64,uint_word,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem remove_values (s : MachineData) (previous next : BitVec 64) :
    ∀ p ∈ removeWrites s previous next, p.2<2^64 := by
  intro p member
  simp only [removeWrites,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact s.regs.r14.toBitVec.isLt
  · exact previous.isLt
  · exact next.isLt

theorem append_values (s : MachineData) : ∀ p ∈ appendWrites s, p.2<2^64 := by
  intro p member
  simp only [appendWrites,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact s.regs.rdx.toBitVec.isLt
  · exact s.regs.r14.toBitVec.isLt
  · exact s.regs.rax.toBitVec.isLt
  · exact s.regs.rdx.toBitVec.isLt

/-- The three actual unlink/owner stores, with every destination alias kept. -/
theorem removed_word (s : MachineData) (previous next : BitVec 64) (path : String) (address : Nat)
    (bound : address+8≤2^64)
    (apart : ∀ p ∈ removeWrites s previous next, address≠p.1 → ∀ a,
      InRange (.ofNat 64 address) 8 a → ¬InRange (.ofNat 64 p.1) 8 a) :
    word (removedMemory s previous next) path address 8=
      readWords (removeWrites s previous next) address (word s.dmem path address 8) := by
  rw [removed_as_words]
  exact word_writeWords s.dmem _ path address bound (remove_values s previous next) apart

/-- The four append stores use the same finite ordered-write theorem. -/
theorem added_word (s : MachineData) (path : String) (address : Nat)
    (bound : address+8≤2^64)
    (apart : ∀ p ∈ appendWrites s, address≠p.1 → ∀ a,
      InRange (.ofNat 64 address) 8 a → ¬InRange (.ofNat 64 p.1) 8 a) :
    word (addedMemory s) path address 8=
      readWords (appendWrites s) address (word s.dmem path address 8) := by
  rw [added_as_words]
  exact word_writeWords s.dmem _ path address bound (append_values s) apart

theorem removed_frame (s : MachineData) (previous next : BitVec 64) :
    EqualOutside (WordWrites (removeWrites s previous next)) s.dmem (removedMemory s previous next) := by
  rw [removed_as_words]
  exact writeWords_frame _ _

theorem added_frame (s : MachineData) :
    EqualOutside (WordWrites (appendWrites s)) s.dmem (addedMemory s) := by
  rw [added_as_words]
  exact writeWords_frame _ _

#print axioms removed_word
#print axioms added_word
end Binary.Pair.Allowedips.Exact
