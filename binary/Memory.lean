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

#print axioms storeInt_defined
end Binary
