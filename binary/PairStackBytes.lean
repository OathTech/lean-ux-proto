import PairStack

namespace Binary.Pair.Stack

/-- Turn a word-wise stack reservation into byte-wise service readiness.
No address nonwrapping premise is needed: both views use modular addresses. -/
theorem bytes_mapped (m : DataMem) (sp : BitVec 64) (words : Nat)
    (mapped : ∀ i<words, (m.loadInt (slot sp (i+1)) 8).isSome=true) :
    ∀ offset<8*words, (m.get? (slot sp words+.ofNat 64 offset)).isSome=true := by
  intro offset bound
  let i := words-1-offset/8
  have divBound : offset/8<words := by omega
  have iBound : i<words := by dsimp [i]; omega
  have part := (loadInt_defined _ _ _).mp (mapped i iBound) (offset%8) (by omega)
  rw [window sp words (i+1) (by omega)] at part
  have number : 8*(words-(i+1))+offset%8=offset := by dsimp [i]; omega
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add,number] using part

#print axioms bytes_mapped

theorem reserve_mono (sp : BitVec 64) (small large extra : Nat) (bound : small≤large)
    (a : BitVec 64) (inside : InRange (slot sp small) (8*small+extra) a) :
    InRange (slot sp large) (8*large+extra) a := by
  obtain ⟨i,hi,eq⟩ := inside
  refine ⟨8*(large-small)+i,by omega,?_⟩
  simpa only [window sp large small bound,BitVec.ofNat_add,BitVec.add_assoc] using eq

#print axioms reserve_mono
end Binary.Pair.Stack
