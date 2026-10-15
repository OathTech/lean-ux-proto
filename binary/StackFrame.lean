import Memory
import PeerPrologue

set_option maxRecDepth 4096

namespace Binary

/-- Reading back an overwrite uses its actual bytes even when the previous
    contents were arbitrary. Address arithmetic is architectural modular
    arithmetic; only a length exceeding the address space is excluded. -/
theorem loadBytes_store_self (memory : Mem 64) (address : BitVec 64)
    (bytes : List UInt8) (size : bytes.length ≤ 2^64) :
    (memory.storeBytes address bytes).loadBytes address bytes.length = some bytes := by
  have reads (i : Nat) (bound : i < bytes.length) :
      (memory.storeBytes address bytes).get? (address + .ofNat 64 i) = some bytes[i] := by
    have hi : i < 2^64 := Nat.lt_of_lt_of_le bound size
    have stored := get?_At_idx bytes address i hi size
    simp only [List.getElem?_eq_getElem bound] at stored
    simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
      Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union] at stored ⊢
    rw [stored]
    rfl
  have mapped : (List.range bytes.length).map
      (fun i => (memory.storeBytes address bytes).get? (address + .ofNat 64 i)) = bytes.map some := by
    apply List.ext_getElem
    · simp
    · intro i hleft hright
      simp only [List.getElem_map, List.getElem_range]
      exact reads i (by simpa using hright)
  simp only [Mem.loadBytes, mapped]
  clear size reads mapped
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    simp [List.allSome, List.mapM_cons] at ih ⊢
    rw [ih]
    rfl

/-- Exact 64-bit readback, including values with the sign bit set. -/
theorem load64_store (memory : Mem 64) (address : BitVec 64) (value : BitVec 64) :
    (memory.storeInt address 8 value.toInt).loadInt address 8 = some (value.toNat : Int) := by
  have self := loadBytes_store_self memory address (Int.toBytes 8 value.toInt)
    (by simp [Int.toBytes_length])
  simp only [Int.toBytes_length] at self
  simp only [Mem.storeInt, Mem.loadInt, self, Option.map_some, ofBytes_toBytes]
  simp only [Int.take, BitVec.toInt_eq_toNat_bmod]
  apply congrArg some
  change (value.toNat : Int).bmod (2^64) % ((2^64 : Nat) : Int) = value.toNat
  rw [Int.bmod_emod]
  have bound := value.isLt
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- The refcount update has the same unsigned readback rule at 32 bits. -/
theorem load32_store (memory : Mem 64) (address : BitVec 64) (value : BitVec 32) :
    (memory.storeInt address 4 value.toInt).loadInt address 4 = some (value.toNat : Int) := by
  have self := loadBytes_store_self memory address (Int.toBytes 4 value.toInt)
    (by simp [Int.toBytes_length])
  simp only [Int.toBytes_length] at self
  simp only [Mem.storeInt, Mem.loadInt, self, Option.map_some, ofBytes_toBytes]
  simp only [Int.take, BitVec.toInt_eq_toNat_bmod]
  apply congrArg some
  change (value.toNat : Int).bmod (2^32) % ((2^32 : Nat) : Int) = value.toNat
  rw [Int.bmod_emod]
  have bound := value.isLt
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Distinct eight-byte slots in the helper's 64-byte stack window do not
    alias, including when the window straddles address zero. -/
theorem stack_slots_disjoint (base : BitVec 64) (i j : Nat)
    (hi : i ≤ 7) (hj : j ≤ 7) (different : i ≠ j) (address : BitVec 64)
    (atI : InRange (base + .ofNat 64 (8*i)) 8 address) :
    ¬InRange (base + .ofNat 64 (8*j)) 8 address := by
  rintro ⟨b, hb, atJ⟩
  obtain ⟨a, ha, atI⟩ := atI
  have equal : base + .ofNat 64 (8*i+a) = base + .ofNat 64 (8*j+b) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using atI.symm.trans atJ
  have nums := congrArg (fun x : BitVec 64 => (x-base).toNat) equal
  simp only [BitVec.add_comm base, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at nums
  omega

theorem stack_tail_inside (base address : BitVec 64)
    (inside : InRange (base+8) 56 address) : InRange base 64 address := by
  obtain ⟨byte, bound, atByte⟩ := inside
  refine ⟨8+byte, by omega, ?_⟩
  simpa [BitVec.ofNat_add, BitVec.add_assoc] using atByte

theorem stack_tail_disjoint_header (base address : BitVec 64)
    (inside : InRange (base+8) 56 address) : ¬InRange base 8 address := by
  rintro ⟨a, ha, atA⟩
  obtain ⟨b, hb, atB⟩ := inside
  have same : base + .ofNat 64 (8+b) = base + .ofNat 64 a := by
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using atB.symm.trans atA
  have numbers := congrArg (fun x : BitVec 64 => (x-base).toNat) same
  simp only [BitVec.add_comm base, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at numbers
  omega

namespace PeerGet

def slot (s : MachineData) (i : Nat) : BitVec 64 :=
  s.regs.rsp.toBitVec - .ofNat 64 ((i+1)*8)

theorem slot_window (s : MachineData) (i : Nat) (hi : i < 7) :
    slot s i = (s.regs.rsp.toBitVec - 56) + .ofNat 64 (8*(6-i)) := by
  have number : 56 = (i+1)*8 + 8*(6-i) := by omega
  rw [show (56 : BitVec 64) = .ofNat 64 56 from rfl, number, BitVec.ofNat_add,
    ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rfl

theorem slot_restore_window (s : MachineData) (i : Nat) (hi : i < 6) :
    slot s i = (s.regs.rsp.toBitVec - 48) + .ofNat 64 (8*(5-i)) := by
  have number : 48 = (i+1)*8 + 8*(5-i) := by omega
  rw [show (48 : BitVec 64) = .ofNat 64 48 from rfl, number, BitVec.ofNat_add,
    ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rfl

/-- Each pushed word is recovered exactly after all later pushes. This is
    the saved-register/return-word fact needed by the helper's epilogue. -/
theorem saveMemory_read (s : MachineData) (n i : Nat) (bound : n ≤ 7) (saved : i < n) :
    (saveMemory s n).loadInt (slot s i) 8 =
      some (((savedWords s)[i]?.getD 0).toNat : Int) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases last : i = n
    · subst i
      exact load64_store (saveMemory s n) (slot s n) ((savedWords s)[n]?.getD 0).toBitVec
    · have earlier : i < n := by omega
      have old := ih (by omega) earlier
      have frame := storeInt_frame (saveMemory s n) (slot s n) 8
        ((savedWords s)[n]?.getD 0).toBitVec.toInt
      have read := frame.loadInt (slot s i) 8 (by
        intro byte hb
        rw [slot_window s i (by omega), slot_window s n (by omega)]
        exact stack_slots_disjoint (s.regs.rsp.toBitVec-56) (6-i) (6-n)
          (by omega) (by omega) (by omega) _ ⟨byte, hb, rfl⟩)
      exact read.symm.trans old

theorem saveMemory_frame (s : MachineData) (n : Nat) (bound : n ≤ 7) :
    EqualOutside (InRange (s.regs.rsp.toBitVec - 56) 56) s.dmem (saveMemory s n) := by
  induction n with
  | zero => intro address outside; rfl
  | succ n ih =>
    intro address outside
    have previous := ih (by omega) address outside
    have disjoint : ¬InRange (slot s n) 8 address := by
      rintro ⟨byte, byteBound, atByte⟩
      apply outside
      refine ⟨8*(6-n)+byte, by omega, ?_⟩
      simpa only [slot_window s n (by omega), BitVec.ofNat_add, BitVec.add_assoc] using atByte
    exact previous.trans (storeInt_frame (saveMemory s n) (slot s n) 8
      ((savedWords s)[n]?.getD 0).toBitVec.toInt address disjoint)

/-- The seven pushes never overwrite the caller's original return word. -/
theorem saveMemory_return (s : MachineData) (n : Nat) (bound : n ≤ 7) :
    (saveMemory s n).loadInt s.regs.rsp.toBitVec 8 = s.dmem.loadInt s.regs.rsp.toBitVec 8 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have frame := storeInt_frame (saveMemory s n) (slot s n) 8
      ((savedWords s)[n]?.getD 0).toBitVec.toInt
    have read := frame.loadInt s.regs.rsp.toBitVec 8 (by
      intro byte byteBound
      rw [slot_window s n (by omega)]
      apply stack_slots_disjoint (s.regs.rsp.toBitVec-56) 7 (6-n)
        (by decide) (by omega) (by omega)
      refine ⟨byte, byteBound, ?_⟩
      change s.regs.rsp.toBitVec + .ofNat 64 byte =
        (s.regs.rsp.toBitVec-56+56) + .ofNat 64 byte
      rw [BitVec.sub_add_cancel])
    exact read.symm.trans (ih (by omega))

#print axioms saveMemory_read
#print axioms saveMemory_frame
#print axioms saveMemory_return
end PeerGet

#print axioms loadBytes_store_self
#print axioms load64_store
#print axioms load32_store
end Binary
