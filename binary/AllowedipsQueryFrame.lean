import AllowedipsPlacementLocals
import PairTrieFrame
import AllowedipsRootCopyDecode
import AllowedipsRootStore

namespace Binary.Pair.Allowedips.Placement
open Root

/-- Turn the tested query locals into decoder reads after a byte frame.
Root and nonempty allocation paths use the same family/byte interpretation. -/
theorem query_words_preserved {s : MachineState} {key : Nat} {after : DataMem}
    (query : queryLocals s key s.data.regs.rbp.toNat=.ok ())
    (family : s.data.regs.rbp.toNat=32 ∨ s.data.regs.rbp.toNat=128)
    (extent : s.data.regs.r13.toNat+s.data.regs.rbp.toNat/8≤2^64)
    (keep : ∀ offset size, offset+size≤s.data.regs.rbp.toNat/8 → ∀ path,
      word after path (s.data.regs.r13.toNat+offset) size=
        word s.data.dmem path (s.data.regs.r13.toNat+offset) size) :
    if s.data.regs.rbp.toNat=32 then word after "query" s.data.regs.r13.toNat 4=.ok key else
      ∃ hi lo,word after "query.high" s.data.regs.r13.toNat 8=.ok hi ∧
        word after "query.low" (s.data.regs.r13.toNat+8) 8=.ok lo ∧ key=hi*2^64+lo := by
  have input := queryLocals_fields query
  have address : BitVec.ofNat 64 s.data.regs.r13.toNat=s.data.regs.r13.toBitVec := ofNat_uint64 _
  rcases family with four|six
  · rw [ite_eq_left four]
    have first := keep 0 4 (by simp [four]) "query"
    simp only [Nat.add_zero] at first
    rw [first]
    apply Trie.word_of_loadInt _ (by simpa only [four,Nat.reduceDiv] using extent)
    simpa only [AllowedipsChild.QueryWords,four,ite_true,address] using input
  · have not4 : s.data.regs.rbp.toNat≠32 := by omega
    rw [ite_eq_right not4]
    have input : s.data.dmem.loadInt s.data.regs.r13.toBitVec 8=some ((key/2^64 : Nat) : Int) ∧
        s.data.dmem.loadInt (s.data.regs.r13.toBitVec+8) 8=some ((key%2^64 : Nat) : Int) := by
      simpa only [AllowedipsChild.QueryWords,ite_eq_right not4] using input
    have extent : s.data.regs.r13.toNat+16≤2^64 := by simpa only [six,Nat.reduceDiv] using extent
    refine ⟨key/2^64,key%2^64,?_,?_,by omega⟩
    · have first := keep 0 8 (by simp [six]) "query.high"
      simp only [Nat.add_zero] at first
      rw [first]
      apply Trie.word_of_loadInt _ (by omega)
      simpa only [address] using input.1
    · rw [keep 8 8 (by simp [six]) "query.low"]
      apply Trie.word_of_loadInt _ (by omega)
      simpa only [BitVec.ofNat_add,address,show BitVec.ofNat 64 8=(8 : BitVec 64) from rfl] using input.2

end Binary.Pair.Allowedips.Placement
