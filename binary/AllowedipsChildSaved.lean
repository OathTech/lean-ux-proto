import AllowedipsChildSetupChecked
import AllowedipsRootCopyDecode

namespace Binary.Pair.Allowedips.ChildSetup
open Root

/-- The image saves the allocation and both copies of the selected direction.
These are consequences of the executed stores, not post-call assumptions. -/
theorem save_words {s : MachineData} {memory : DataMem} {direction : Nat}
    (extent : s.regs.rsp.toNat+24≤2^64) (bit : direction<2)
    (index : s.regs.rax.toNat=direction) (byte : s.regs.rdx.toNat=direction)
    (checked : saveEffect s=.ok memory) :
    word memory "saved.base" s.regs.rsp.toNat 8=.ok s.regs.r8.toNat ∧
    word memory "saved.direction" (s.regs.rsp.toNat+8) 1=.ok direction ∧
    word memory "saved.index" (s.regs.rsp.toNat+16) 8=.ok direction := by
  unfold saveEffect at checked
  obtain ⟨first,stored0,checked⟩ := bind_ok checked
  obtain ⟨second,stored1,stored2⟩ := bind_ok checked
  have firstEq := (store_facts stored0).2
  have secondEq := (store_facts stored1).2
  have memoryEq := (store_facts stored2).2
  have small : direction%256=direction := Nat.mod_eq_of_lt (by omega)
  rw [index] at firstEq
  rw [byte,small] at secondEq
  refine ⟨?_,?_,?_⟩
  · rw [memoryEq]
    exact word_store_same _ _ _ _ _ (by omega) s.regs.r8.toBitVec.isLt
  · rw [memoryEq]
    have frame := word_store_frame second "saved.direction" s.regs.rsp.toNat
      8 1 0 8 s.regs.r8.toNat (by decide) (by decide) (.inr (by decide))
    simp only [Nat.add_zero] at frame
    rw [frame,secondEq]
    exact word_store_same _ _ _ _ _ (by omega) (by change direction<256; omega)
  · rw [memoryEq]
    have frame := word_store_frame second "saved.index" s.regs.rsp.toNat
      16 8 0 8 s.regs.r8.toNat (by decide) (by decide) (.inr (by decide))
    simp only [Nat.add_zero] at frame
    rw [frame,secondEq,word_store_frame first "saved.index" s.regs.rsp.toNat
      16 8 8 1 direction (by decide) (by decide) (.inr (by decide)),firstEq]
    exact word_store_same _ _ _ _ _ extent (by change direction<2^64; omega)

#print axioms save_words
end Binary.Pair.Allowedips.ChildSetup
