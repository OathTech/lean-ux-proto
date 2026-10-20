import Memory

namespace Binary.MemoryBytes

private theorem allSome_eq_some (xs : List (Option α)) (ys : List α) :
    xs.allSome = some ys ↔ xs = ys.map some := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [List.allSome]
  | cons x xs ih =>
    cases x with
    | none => cases ys <;> simp [List.allSome, List.mapM_cons]
    | some x =>
      cases ys with
      | nil =>
        cases h : xs.allSome <;> simp [List.allSome, List.mapM_cons] at h ⊢ <;> simp [h]
      | cons y ys =>
        cases h : xs.allSome with
        | none =>
          have absent : xs ≠ ys.map some := fun he => by
            have := (ih ys).mpr he
            simp [h] at this
          simp [List.allSome, List.mapM_cons] at h ⊢
          simp [h, absent]
        | some zs =>
          have he := (ih zs).mp h
          simp [List.allSome, List.mapM_cons] at h ⊢
          simp only [h, Option.bind_some, Option.some.injEq, List.cons.injEq]
          rw [he]
          constructor
          · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
          · rintro ⟨hxy, hzs⟩
            exact ⟨hxy, (List.map_inj_right (fun _ _ h => Option.some.inj h)).mp hzs⟩

/-- A successful byte read determines every byte of the loaded interval.
The addresses are modular; no assumption on the allocation's base is needed. -/
theorem loadBytes_iff (memory : Mem 64) (address : BitVec 64) (width : Nat)
    (bytes : List UInt8) :
    memory.loadBytes address width = some bytes ↔
      bytes.length = width ∧
      ∀ i (hi : i < bytes.length),
        memory.get? (address + .ofNat 64 i) = some bytes[i] := by
  rw [Mem.loadBytes, allSome_eq_some]
  constructor
  · intro he
    have len := congrArg List.length he
    simp only [List.length_map, List.length_range] at len
    refine ⟨len.symm, ?_⟩
    intro i hi
    have he' := congrArg (fun xs => xs[i]?) he
    simpa [List.getElem?_map, List.getElem?_range, hi, len] using he'
  · rintro ⟨len, reads⟩
    apply List.ext_getElem
    · simp [len]
    · intro i hl hr
      simpa using reads i (by simpa using hr)

/-- A successful integer load fixes its complete little-endian byte list. -/
theorem loadInt_bytes (memory : Mem 64) (address : BitVec 64) (width : Nat)
    (value : Int) (read : memory.loadInt address width = some value) :
    memory.loadBytes address width = some (Int.toBytes width value) := by
  cases bytesRead : memory.loadBytes address width with
  | none => simp [Mem.loadInt, bytesRead] at read
  | some bytes =>
    have size := ((loadBytes_iff memory address width bytes).mp bytesRead).1
    have valueEq : Int.ofBytes bytes = value := by
      simpa [Mem.loadInt, bytesRead] using read
    rw [← valueEq, ← size, Int.toBytes_ofBytes_all]

/-- Byte lookup inside a successful integer load, with no additional
readability assumption and no assumption that the integer was canonical. -/
theorem get_of_loadInt (memory : Mem 64) (address : BitVec 64) (width : Nat)
    (value : Int) (read : memory.loadInt address width = some value)
    (i : Nat) (bound : i < width) :
    memory.get? (address + .ofNat 64 i) = (Int.toBytes width value)[i]? := by
  have reads := ((loadBytes_iff memory address width _).mp
    (loadInt_bytes memory address width value read)).2
  have hi : i < (Int.toBytes width value).length := by simpa [Int.toBytes_length] using bound
  simpa only [List.getElem?_eq_getElem hi] using reads i hi

/-- Dropping low bytes is integer division by the corresponding power of 256,
including signed store operands. -/
theorem toBytes_drop (width offset : Nat) (value : Int) :
    (Int.toBytes width value).drop offset =
      Int.toBytes (width - offset) (value / 256 ^ offset) := by
  induction offset generalizing width value with
  | zero => simp
  | succ offset ih =>
    cases width with
    | zero => simp [Int.toBytes]
    | succ width =>
      simp only [Int.toBytes, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
      rw [ih, Int.ediv_ediv_of_nonneg (by decide : (0 : Int) ≤ 256)]
      rw [Int.pow_succ, Int.mul_comm (256 : Int)]

theorem toBytes_take (width length : Nat) (value : Int) (bound : length ≤ width) :
    (Int.toBytes width value).take length = Int.toBytes length value := by
  induction length generalizing width value with
  | zero => rfl
  | succ length ih =>
    cases width with
    | zero => omega
    | succ width => simpa [Int.toBytes] using ih width (value / 256) (by omega)

/-- A contained subword read follows from the full read. This is an exact
little-endian extraction, not an added byte-level hypothesis. -/
theorem loadInt_subword (memory : Mem 64) (address : BitVec 64) (width : Nat)
    (value : Int) (read : memory.loadInt address width = some value)
    (offset length : Nat) (bound : offset + length ≤ width) :
    memory.loadInt (address + .ofNat 64 offset) length =
      some ((value / 256 ^ offset) % (2 : Int) ^ (8 * length)) := by
  have bytesRead := loadInt_bytes memory address width value read
  have readEach := ((loadBytes_iff memory address width _).mp bytesRead).2
  have sliceRead : memory.loadBytes (address + .ofNat 64 offset) length =
      some (((Int.toBytes width value).drop offset).take length) := by
    apply (loadBytes_iff memory _ length _).mpr
    constructor
    · simp [Int.toBytes_length]; omega
    · intro i hi
      have valid : offset + i < (Int.toBytes width value).length := by
        simp only [List.length_take, List.length_drop, Int.toBytes_length] at hi ⊢
        omega
      simpa only [List.getElem_take, List.getElem_drop, BitVec.add_assoc,
        ← BitVec.ofNat_add] using readEach (offset+i) valid
  rw [Mem.loadInt, sliceRead, Option.map_some, toBytes_drop,
    toBytes_take _ _ _ (by omega), ofBytes_toBytes]

/-- One-byte specialization, in the usual quotient/remainder form. -/
theorem loadInt_byte (memory : Mem 64) (address : BitVec 64) (width : Nat)
    (value : Int) (read : memory.loadInt address width = some value)
    (offset : Nat) (bound : offset < width) :
    memory.loadInt (address + .ofNat 64 offset) 1 =
      some ((value / 256 ^ offset) % 256) :=
  loadInt_subword memory address width value read offset 1 (by omega)

/-- Each in-range byte of a store has the supplied value. The sole address
bound prevents a list longer than the architectural address space from
overwriting its own earlier bytes; wrapping the base address is permitted. -/
theorem get_storeBytes (memory : Mem 64) (address : BitVec 64)
    (bytes : List UInt8) (size : bytes.length ≤ 2^64)
    (offset : Nat) (bound : offset < bytes.length) :
    (memory.storeBytes address bytes).get? (address + .ofNat 64 offset) =
      some bytes[offset] := by
  have byte := get?_At_idx bytes address offset (by omega) size
  simp only [List.getElem?_eq_getElem bound] at byte
  simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union] at byte ⊢
  rw [byte]
  rfl

theorem loadBytes_store_slice (memory : Mem 64) (address : BitVec 64)
    (bytes : List UInt8) (size : bytes.length ≤ 2^64)
    (offset length : Nat) (bound : offset + length ≤ bytes.length) :
    (memory.storeBytes address bytes).loadBytes (address + .ofNat 64 offset) length =
      some ((bytes.drop offset).take length) := by
  apply (loadBytes_iff _ _ _ _).mpr
  constructor
  · simp; omega
  · intro i hi
    have valid : offset + i < bytes.length := by
      simp only [List.length_take, List.length_drop] at hi
      omega
    simpa only [List.getElem_take, List.getElem_drop, BitVec.add_assoc,
      ← BitVec.ofNat_add] using get_storeBytes memory address bytes size (offset+i) valid

/-- Exact little-endian subword readback from any integer store, including
negative operands and a store whose address interval crosses zero. -/
theorem loadInt_store_subword (memory : Mem 64) (address : BitVec 64)
    (width : Nat) (value : Int) (size : width ≤ 2^64)
    (offset length : Nat) (bound : offset + length ≤ width) :
    (memory.storeInt address width value).loadInt (address + .ofNat 64 offset) length =
      some ((value / 256 ^ offset) % (2 : Int) ^ (8 * length)) := by
  have sliceRead := loadBytes_store_slice memory address (Int.toBytes width value)
    (by simpa [Int.toBytes_length] using size) offset length
    (by simpa [Int.toBytes_length] using bound)
  rw [Mem.storeInt, Mem.loadInt, sliceRead, Option.map_some, toBytes_drop,
    toBytes_take _ _ _ (by omega), ofBytes_toBytes]

theorem loadInt_store_byte (memory : Mem 64) (address : BitVec 64)
    (width : Nat) (value : Int) (size : width ≤ 2^64)
    (offset : Nat) (bound : offset < width) :
    (memory.storeInt address width value).loadInt (address + .ofNat 64 offset) 1 =
      some ((value / 256 ^ offset) % 256) :=
  loadInt_store_subword memory address width value size offset 1 (by omega)

#print axioms loadInt_bytes
#print axioms get_of_loadInt
#print axioms loadInt_subword
#print axioms loadInt_byte
#print axioms loadBytes_store_slice
#print axioms loadInt_store_subword
#print axioms loadInt_store_byte

end Binary.MemoryBytes
