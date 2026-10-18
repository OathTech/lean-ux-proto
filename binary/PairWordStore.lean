import PairCountUpdate
import StackFrame

namespace Binary.Pair

/-- The exact byte store used by an x86-64 MOV, with unsigned input names. -/
def write64 (m : DataMem) (address value : Nat) : DataMem :=
  m.storeInt (.ofNat 64 address) 8 (BitVec.ofNat 64 value).toInt

theorem word_write64_same (m : DataMem) (path : String) (address value : Nat)
    (bounded : address+8≤2^64) (small : value<2^64) :
    word (write64 m address value) path address 8=.ok value := by
  apply Trie.word_of_loadInt path bounded
  simpa only [write64,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using
    load64_store m (.ofNat 64 address) (.ofNat 64 value)

theorem word_write64_frame (m : DataMem) (path : String) (address size destination value : Nat)
    (apart : ∀ a, InRange (.ofNat 64 address) size a → ¬InRange (.ofNat 64 destination) 8 a) :
    word (write64 m destination value) path address size=word m path address size :=
  (Trie.word_frame (storeInt_frame m (.ofNat 64 destination) 8 _) path address size apart).symm

theorem word_write64 (m : DataMem) (path : String) (address destination value : Nat)
    (bounded : address+8≤2^64) (small : value<2^64)
    (apart : address≠destination → ∀ a, InRange (.ofNat 64 address) 8 a →
      ¬InRange (.ofNat 64 destination) 8 a) :
    word (write64 m destination value) path address 8 =
      if address=destination then .ok value else word m path address 8 := by
  by_cases same : address=destination
  · subst address
    simpa only [↓reduceIte] using word_write64_same m path destination value bounded small
  · rw [ite_eq_right same]
    exact word_write64_frame m path address 8 destination value (apart same)

theorem write64_frame (m : DataMem) (address value : Nat) :
    EqualOutside (InRange (.ofNat 64 address) 8) m (write64 m address value) :=
  storeInt_frame _ _ _ _

#print axioms word_write64
end Binary.Pair
