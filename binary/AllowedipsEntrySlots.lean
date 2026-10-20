import AllowedipsEntryContext
namespace Binary.AllowedipsEntry
open TrustBase

/-- Positive indices name successive eight-byte words below entry RSP;
index zero is the caller's return word. -/
def slot (s : MachineState) (n : Nat) : BitVec 64 :=
  s.data.regs.rsp.toBitVec - .ofNat 64 (n*8)

theorem slot_window (s : MachineState) (n : Nat) (bound : n ≤ 18) :
    slot s n = s.data.regs.rsp.toBitVec-144 + .ofNat 64 (144-n*8) := by
  have number : 144 = n*8 + (144-n*8) := by omega
  unfold slot
  have word : (144 : BitVec 64) = .ofNat 64 (n*8) + .ofNat 64 (144-n*8) := by
    rw [← BitVec.ofNat_add, ← number]
    rfl
  rw [word, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem slot_apart (s : MachineState) (n m : Nat) (hn : n ≤ 18) (hm : m ≤ 18)
    (different : n ≠ m) (a : BitVec 64) (inside : InRange (slot s n) 8 a) :
    ¬InRange (slot s m) 8 a := by
  rw [slot_window s n hn] at inside
  rw [slot_window s m hm]
  exact InRange.offset_disjoint _ _ _ _ _ (by omega) (by omega) (by omega) a inside

theorem slot_live (s : MachineState) (n : Nat) (bound : n ≤ 18)
    (a : BitVec 64) (inside : InRange (slot s n) 8 a) : AllowedipsLiveStack s a := by
  obtain ⟨i,hi,eq⟩ := inside
  rw [slot_window s n bound] at eq
  exact ⟨144-n*8+i, by omega, by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq⟩

theorem slot_writes (s : MachineState) (n : Nat) (lower : 1 ≤ n) (upper : n ≤ 18)
    (a : BitVec 64) (inside : InRange (slot s n) 8 a) : AllowedipsStackWrites s a := by
  obtain ⟨i,hi,eq⟩ := inside
  rw [slot_window s n upper] at eq
  exact ⟨144-n*8+i, by omega, by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq⟩

theorem saved_slot (s : MachineState) (i : Nat) (bound : i < 7) :
    Allowedips.entrySlot s.data i = slot s (if i < 6 then i+1 else 9) := by
  unfold Allowedips.entrySlot slot
  split
  · rfl
  · have eq : i = 6 := by omega
    subst i
    rfl

theorem saved_live (s : MachineState) (i : Nat) (bound : i < 7)
    (a : BitVec 64) (inside : InRange (Allowedips.entrySlot s.data i) 8 a) :
    AllowedipsLiveStack s a := by
  rw [saved_slot s i bound] at inside
  exact slot_live s _ (by split <;> omega) a inside

theorem saved_call_apart (s : MachineState) (i : Nat) (bound : i < 7)
    (a : BitVec 64) (inside : InRange (Allowedips.entrySlot s.data i) 8 a) :
    ¬InRange (slot s 11) 8 a := by
  rw [saved_slot s i bound] at inside
  exact slot_apart s _ 11 (by split <;> omega) (by decide) (by split <;> omega) a inside

#print axioms slot_apart
#print axioms saved_call_apart
end Binary.AllowedipsEntry
