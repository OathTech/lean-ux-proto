import AllowedipsRootHeaderChecked

namespace Binary.Pair.Allowedips.Root

def headerByte (width cidr : Nat) (byte : Fin 4) : Nat :=
  match byte.val with
  | 0 => cidr
  | 1 => cidr/8 ^^^ ((width/8-1)%8)
  | 2 => 7-cidr%8
  | _ => width

private theorem bytes_finite : ∀ family : Bool, ∀ cidr : Fin 129, ∀ byte : Fin 4,
    headerWord (if family then 32 else 128) cidr.val / 256^byte.val % 256=
      headerByte (if family then 32 else 128) cidr.val byte := by
  decide +kernel

theorem header_bytes {width cidr : Nat} (family : width=32 ∨ width=128) (bound : cidr≤width)
    (byte : Fin 4) :
    headerWord width cidr / 256^byte.val % 256=headerByte width cidr byte := by
  rcases family with rfl|rfl
  · exact bytes_finite true ⟨cidr,by omega⟩ byte
  · exact bytes_finite false ⟨cidr,by omega⟩ byte

/-- The four-byte store is read by reconstruction as four separate fields.
This lemma connects the tested packed word to those actual byte reads. -/
theorem header_field (m : DataMem) (base width cidr : Nat) (path : String)
    (family : width=32 ∨ width=128) (bound : cidr≤width) (extent : base+28≤2^64)
    (byte : Fin 4) :
    word (m.storeInt (.ofNat 64 (base+24)) 4 (headerWord width cidr)) path (base+24+byte.val) 1=
      .ok (headerByte width cidr byte) := by
  apply Trie.word_of_loadInt path (by have := byte.isLt; omega)
  have read := MemoryBytes.loadInt_store_byte m (.ofNat 64 (base+24)) 4 (headerWord width cidr)
    (by decide) byte.val byte.isLt
  have value : (((headerWord width cidr : Nat) : Int)/256^byte.val)%256=
      (headerByte width cidr byte : Int) := by
    have cast := congrArg (fun n : Nat => (n : Int)) (header_bytes family bound byte)
    simpa [Int.natCast_ediv,Int.natCast_emod,Int.natCast_pow] using cast
  simpa only [BitVec.ofNat_add,value] using read

#print axioms header_field
end Binary.Pair.Allowedips.Root
