import Kraken.Mem

namespace Binary

private theorem allSome_defined (xs : List (Option UInt8)) :
    xs.allSome.isSome = true ↔ ∀ x ∈ xs, x.isSome = true := by
  induction xs with
  | nil => simp [List.allSome]
  | cons x xs ih =>
    simp only [List.allSome, List.mapM_cons]
    cases x <;> simp_all [List.allSome]
    cases h : List.mapM id xs <;> simp_all

theorem loadInt_defined (m : Mem 64) (a : BitVec 64) (n : Nat) :
    (m.loadInt a n).isSome = true ↔
      ∀ i < n, (m.get? (a + .ofNat 64 i)).isSome = true := by
  simp [Mem.loadInt, Mem.loadBytes, allSome_defined]

/-- A store changes values but never removes a mapped byte. This is used
    only for readability; disjoint frames prove preservation of values. -/
theorem storeInt_defined (m : Mem 64) (a b : BitVec 64) (n k : Nat) (v : Int)
    (h : (m.loadInt a n).isSome = true) :
    ((m.storeInt b k v).loadInt a n).isSome = true := by
  rw [loadInt_defined] at h ⊢
  intro i hi
  specialize h i hi
  simp only [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases hnew : ((Int.toBytes k v).At b)[a + .ofNat 64 i]? with
  | some x => rfl
  | none => exact h

/-- Byte-level footprint; arithmetic is modulo the architectural address width. -/
def InRange (base : BitVec 64) (length : Nat) (address : BitVec 64) : Prop :=
  ∃ i < length, address = base + .ofNat 64 i

/-- Exact equality of every byte outside a stated write footprint. -/
def EqualOutside (writes : BitVec 64 → Prop) (before after : Mem 64) : Prop :=
  ∀ address, ¬ writes address → before.get? address = after.get? address

/-- Disjoint offsets in one allocation remain disjoint even when its base
    wraps modulo the architectural address width. -/
theorem InRange.offset_disjoint (base : BitVec 64) (i ni j nj : Nat)
    (ibound : i+ni ≤ 2^64) (jbound : j+nj ≤ 2^64)
    (apart : i+ni ≤ j ∨ j+nj ≤ i) (a : BitVec 64)
    (inside : InRange (base + .ofNat 64 i) ni a) :
    ¬InRange (base + .ofNat 64 j) nj a := by
  rintro ⟨y, hy, ey⟩
  obtain ⟨x, hx, ex⟩ := inside
  have same : base + .ofNat 64 (i+x) = base + .ofNat 64 (j+y) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using ex.symm.trans ey
  have words := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp same)
  simp only [BitVec.toNat_ofNat] at words
  rw [Nat.mod_eq_of_lt (show i+x < 2^64 by omega),
    Nat.mod_eq_of_lt (show j+y < 2^64 by omega)] at words
  rcases apart with h | h <;> omega

theorem storeInt_frame (m : Mem 64) (base : BitVec 64) (length : Nat) (v : Int) :
    EqualOutside (InRange base length) m (m.storeInt base length v) := by
  intro address outside
  have absent : address ∉ (Int.toBytes length v).At base := by
    intro present
    rw [mem_At_iff] at present
    apply outside
    simpa only [Int.toBytes_length, InRange] using present
  have missing := Std.ExtHashMap.getElem?_eq_none absent
  simp only [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union, missing, Option.none_or]

theorem EqualOutside.trans {a b c : Mem 64} {p q : BitVec 64 → Prop}
    (ab : EqualOutside p a b) (bc : EqualOutside q b c) :
    EqualOutside (fun x => p x ∨ q x) a c := by
  intro x hx
  exact (ab x (fun hp => hx (.inl hp))).trans (bc x (fun hq => hx (.inr hq)))

/-- A read disjoint from the actual writes has the identical result, including
    unmapped bytes. This is the physical frame rule, not a ghost-world axiom. -/
theorem EqualOutside.loadBytes {before after : Mem 64} {writes : BitVec 64 → Prop}
    (eq : EqualOutside writes before after) (base : BitVec 64) (length : Nat)
    (disjoint : ∀ i < length, ¬ writes (base + .ofNat 64 i)) :
    before.loadBytes base length = after.loadBytes base length := by
  unfold Mem.loadBytes
  congr 1
  apply List.map_congr_left
  intro i hi
  exact eq _ (disjoint i (List.mem_range.mp hi))

theorem EqualOutside.loadInt {before after : Mem 64} {writes : BitVec 64 → Prop}
    (eq : EqualOutside writes before after) (base : BitVec 64) (length : Nat)
    (disjoint : ∀ i < length, ¬ writes (base + .ofNat 64 i)) :
    before.loadInt base length = after.loadInt base length := by
  unfold Mem.loadInt
  rw [eq.loadBytes base length disjoint]

#print axioms storeInt_frame
#print axioms EqualOutside.loadInt

#print axioms storeInt_defined
#print axioms InRange.offset_disjoint
end Binary
