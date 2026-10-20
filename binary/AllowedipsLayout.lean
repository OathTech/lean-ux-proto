import Memory
namespace Binary.AllowedipsLayout
-- Generated DWARF record layout. Pointer structure lives in TrieHeap.
def nodeSize : Nat := 72
def peer : Nat := 0
def bit : Nat := 8
def cidr : Nat := 24
def bit_at_a : Nat := 25
def bit_at_b : Nat := 26
def bitlen : Nat := 27
def bits : Nat := 32
def ScalarFields (m : Mem 64) (a : BitVec 64)
    (cidrValue byteSelector bitSelector : Nat) : Prop :=
  m.loadInt (a + .ofNat 64 cidr) 1 = some cidrValue ∧
  m.loadInt (a + .ofNat 64 bit_at_a) 1 = some byteSelector ∧
  m.loadInt (a + .ofNat 64 bit_at_b) 1 = some bitSelector
end Binary.AllowedipsLayout
