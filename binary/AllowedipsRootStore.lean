import AllowedipsRootHeader
import AllowedipsRootCopy128

namespace Binary.Pair.Allowedips.Root

theorem store_facts {m address size value after} (checked : store m address size value=.ok after) :
    (m.loadInt (.ofNat 64 address) size).isSome=true ∧
      after=m.storeInt (.ofNat 64 address) size value := by
  unfold store at checked
  obtain ⟨_,mapped,checked⟩ := bind_ok checked
  exact ⟨require_ok mapped,(Except.ok.inj checked).symm⟩

/-- The physical store uses a signed integer representation, while the
executable summary uses an unsigned word. Their stored bytes are identical. -/
theorem store_unsigned (m : DataMem) (address : BitVec 64) (size : Nat) (word : BitVec (8*size)) :
    m.storeInt address size word.toNat=m.storeInt address size word.toInt := by
  unfold Mem.storeInt
  congr 1
  rw [←Int.toBytes_emod size (word.toNat : Int),←Int.toBytes_emod size word.toInt]
  simp only [Int.take,BitVec.toInt_eq_toNat_bmod]
  change Int.toBytes size ((word.toNat : Int)%((2^(8*size) : Nat) : Int))=
    Int.toBytes size (((word.toNat : Int).bmod (2^(8*size)))%((2^(8*size) : Nat) : Int))
  rw [Int.bmod_emod]

theorem read_word32 {s a n} (read : readNat s a 4=.ok n) :
    s.data.dmem.loadInt (.ofNat 64 a) 4=some ((BitVec.ofNat 32 n).toNat : Int) := by
  have loaded := Trie.readNat_loadInt read
  have bound := (loadInt_range _ _ _ _ loaded).2
  change (n : Int)<4294967296 at bound
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : n<2^32)] using loaded

theorem store_nat (m : DataMem) (address size value : Nat) :
    m.storeInt (.ofNat 64 address) size value=
      m.storeInt (.ofNat 64 address) size (BitVec.ofNat (8*size) value).toInt := by
  unfold Mem.storeInt
  congr 1
  rw [←Int.toBytes_emod size (value : Int),←Int.toBytes_emod size (BitVec.ofNat (8*size) value).toInt]
  simp only [Int.take,BitVec.toInt_ofNat']
  change Int.toBytes size ((value : Int)%((2^(8*size) : Nat) : Int))=
    Int.toBytes size (((value : Int).bmod (2^(8*size)))%((2^(8*size) : Nat) : Int))
  rw [Int.bmod_emod]

theorem store_nat64 (m : DataMem) (address value : Nat) :
    m.storeInt (.ofNat 64 address) 8 value=m.storeInt (.ofNat 64 address) 8 (BitVec.ofNat 64 value).toInt :=
  store_nat m address 8 value

theorem store_nat32 (m : DataMem) (address value : Nat) :
    m.storeInt (.ofNat 64 address) 4 value=m.storeInt (.ofNat 64 address) 4 (BitVec.ofNat 32 value).toInt :=
  store_nat m address 4 value

theorem ofNat_uint64 (v : UInt64) : BitVec.ofNat 64 v.toNat=v.toBitVec :=
  BitVec.ofNat_toNat 64 v.toBitVec

#print axioms store_unsigned
end Binary.Pair.Allowedips.Root
