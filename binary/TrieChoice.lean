import TrieHeap

namespace Binary.AllowedipsRelation

def byteSelector (bits cidr : Nat) : Nat := cidr / 8 ^^^ ((bits / 8 - 1) % 8)
def byteShift (bits offset : Nat) : Nat :=
  if bits = 32 then 8*offset else if offset < 8 then 64+8*offset else 8*(offset-8)

private theorem selector32 : ∀ cidr : Fin 32,
    byteShift 32 (byteSelector 32 cidr.val) + (7-cidr.val%8) = 31-cidr.val ∧
    byteSelector 32 cidr.val < 4 := by decide

private theorem selector128 : ∀ cidr : Fin 128,
    byteShift 128 (byteSelector 128 cidr.val) + (7-cidr.val%8) = 127-cidr.val ∧
    byteSelector 128 cidr.val < 16 := by decide

/-- The two precomputed selector bytes implement the mirror's bit index.
    The finite width calculation is kernel-reduced, with no native oracle. -/
theorem selector_position (bits cidr : Nat) (family : bits = 32 ∨ bits = 128)
    (short : cidr < bits) :
    byteShift bits (byteSelector bits cidr) + (7-cidr%8) = bits-1-cidr ∧
    byteSelector bits cidr < bits/8 := by
  rcases family with rfl | rfl
  · exact selector32 ⟨cidr, short⟩
  · exact selector128 ⟨cidr, short⟩

/-- Reading the selected byte and testing its selected bit is the same
    logical query bit, for either address family. -/
theorem selected_bit (bits cidr query : Nat) (family : bits = 32 ∨ bits = 128)
    (short : cidr < bits) :
    ((query / 2^(byteShift bits (byteSelector bits cidr))) % 2^8).testBit (7-cidr%8) =
      query.testBit (bits-1-cidr) := by
  have bitBound : 7-cidr%8 < 8 := by omega
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [bitBound, decide_true, Bool.true_and]
  rw [Nat.add_comm, (selector_position bits cidr family short).1]

#print axioms selector_position
#print axioms selected_bit
end Binary.AllowedipsRelation
