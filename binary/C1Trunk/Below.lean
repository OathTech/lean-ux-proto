import C1Trunk.WrapperRegions
/-! Result C1, package 2: addresses below a stack pointer, in the one form
`sp - n`, with readability, inclusion and separation of such ranges. -/
namespace C1Trunk
open Binary Binary.Pair

/-- The `n` bytes below `sp` are mapped. -/
def Below (m : Mem 64) (sp : BitVec 64) (n : Nat) : Prop :=
  ∀ i < n, (m.get? (sp - .ofNat 64 (i+1))).isSome = true

theorem sub_add_ofNat (sp : BitVec 64) (n i : Nat) (h : i ≤ n) :
    sp - .ofNat 64 n + .ofNat 64 i = sp - .ofNat 64 (n-i) := by
  have e : BitVec.ofNat 64 n = BitVec.ofNat 64 (n-i) + BitVec.ofNat 64 i := by
    rw [← BitVec.ofNat_add]; congr; omega
  rw [e, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem Below.load {m : Mem 64} {sp : BitVec 64} {n : Nat} (below : Below m sp n)
    (k len : Nat) (hk : len ≤ k) (hn : k ≤ n) :
    (m.loadInt (sp - .ofNat 64 k) len).isSome = true := by
  rw [loadInt_defined]
  intro i hi
  rw [sub_add_ofNat sp k i (by omega)]
  have h := below (k-i-1) (by omega)
  rwa [show k-i-1+1 = k-i by omega] at h

theorem Below.mono {m m' : Mem 64} {sp : BitVec 64} {n : Nat} (below : Below m sp n)
    (mapped : ∀ a k, (m.loadInt a k).isSome = true → (m'.loadInt a k).isSome = true) :
    Below m' sp n := by
  intro i hi
  have one : (m.loadInt (sp - .ofNat 64 (i+1)) 1).isSome = true := by
    rw [loadInt_defined]
    intro j hj
    have : j = 0 := by omega
    subst this
    simpa using below i hi
  have after := (loadInt_defined _ _ _).mp (mapped _ _ one) 0 (by omega)
  simpa using after

/-- Inclusion of one range below `sp` in another. -/
theorem below_sub (sp : BitVec 64) (c1 n1 c2 n2 : Nat) (h : c1 ≤ c2) (fit : c2 - c1 + n1 ≤ n2)
    (a : BitVec 64) (inside : InRange (sp - .ofNat 64 c1) n1 a) :
    InRange (sp - .ofNat 64 c2) n2 a := by
  obtain ⟨i,hi,eq⟩ := inside
  refine ⟨c2-c1+i, by omega, ?_⟩
  rw [eq, BitVec.ofNat_add, ← BitVec.add_assoc, sub_add_ofNat sp c2 (c2-c1) (by omega)]
  congr 3
  omega

/-- Separation of two ranges below (or straddling) `sp`. -/
theorem below_disjoint (sp : BitVec 64) (c1 n1 c2 n2 : Nat)
    (b1 : c1 + n1 < 2^63) (b2 : c2 + n2 < 2^63)
    (apart : c2 + n1 ≤ c1 ∨ c1 + n2 ≤ c2) (a : BitVec 64)
    (inside : InRange (sp - .ofNat 64 c1) n1 a) : ¬InRange (sp - .ofNat 64 c2) n2 a := by
  have e1 : sp - .ofNat 64 c1 = sp - .ofNat 64 (c1+c2) + .ofNat 64 c2 := by
    rw [sub_add_ofNat sp (c1+c2) c2 (by omega)]; congr 2; omega
  have e2 : sp - .ofNat 64 c2 = sp - .ofNat 64 (c1+c2) + .ofNat 64 c1 := by
    rw [sub_add_ofNat sp (c1+c2) c1 (by omega)]; congr 2; omega
  rw [e1] at inside
  rw [e2]
  exact InRange.offset_disjoint _ c2 n1 c1 n2 (by omega) (by omega) (by omega) a inside

theorem below_load_store (m : Mem 64) (sp : BitVec 64) (c1 n1 c2 n2 : Nat) (v : Int)
    (b1 : c1 + n1 < 2^63) (b2 : c2 + n2 < 2^63) (apart : c2 + n1 ≤ c1 ∨ c1 + n2 ≤ c2) :
    (m.storeInt (sp - .ofNat 64 c2) n2 v).loadInt (sp - .ofNat 64 c1) n1 =
      m.loadInt (sp - .ofNat 64 c1) n1 :=
  ((storeInt_frame m _ n2 v).loadInt _ n1 (fun k hk h =>
    below_disjoint sp c1 n1 c2 n2 b1 b2 apart _ ⟨k,hk,rfl⟩ h)).symm

/-- A load apart from a store sees the old memory. -/
theorem load_store_apart (m : Mem 64) (a b : BitVec 64) (n k : Nat) (v : Int)
    (apart : ∀ x, InRange a n x → ¬InRange b k x) :
    (m.storeInt b k v).loadInt a n = m.loadInt a n :=
  ((storeInt_frame m b k v).loadInt a n (fun i hi h => apart _ ⟨i,hi,rfl⟩ h)).symm

/-- The return word and above: `sp + i` as a range starting below. -/
theorem above_in (sp : BitVec 64) (c n : Nat) (i : Nat) (hi : c + i < n) :
    InRange (sp - .ofNat 64 c) n (sp + .ofNat 64 i) := by
  refine ⟨c+i, hi, ?_⟩
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

#print axioms Below.load
#print axioms below_sub
#print axioms below_disjoint
#print axioms below_load_store
end C1Trunk
