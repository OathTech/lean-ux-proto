import PairDecodeProof
import TrieHeap

namespace Binary.Pair.Trie

/-- Total interpretation for the old physical lemmas. Only named identities
are used: successful pointer decoding supplies membership before this is read. -/
def interpretation (names : List (Nat×Nat)) (id : Nat) : BitVec 64 :=
  .ofNat 64 (((names.find? (·.1 == id)).map Prod.snd).getD 0)

theorem find_identity {names : List (Nat×Nat)} {id a : Nat}
    (unique : (names.map Prod.fst).Nodup) (member : (id,a) ∈ names) :
    names.find? (·.1 == id) = some (id,a) := by
  induction names with
  | nil => cases member
  | cons pair names ih =>
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have different : pair.1 ≠ id := by
        intro eq
        exact parts.1 (eq ▸ List.mem_map.mpr ⟨(id,a),member,rfl⟩)
      simpa only [List.find?_cons,show (pair.1 == id) = false from by simp [different]] using ih parts.2 member

theorem interpretation_of_mem {names : List (Nat×Nat)} {id a : Nat}
    (unique : (names.map Prod.fst).Nodup) (member : (id,a) ∈ names) :
    interpretation names id = .ofNat 64 a := by
  simp only [interpretation,find_identity unique member,Option.map_some,Option.getD_some]

theorem interpretation_nonnull {names : List (Nat×Nat)} {id a : Nat}
    (unique : (names.map Prod.fst).Nodup) (member : (id,a) ∈ names)
    (positive : 0 < a) (bounded : a < 2^64) : interpretation names id ≠ 0 := by
  rw [interpretation_of_mem unique member]
  intro eq
  have raw := congrArg BitVec.toNat eq
  change a % 2^64 = 0 at raw
  rw [Nat.mod_eq_of_lt bounded] at raw
  omega

theorem pointer_value {names : List (Nat×Nat)} {path : String} {raw : Nat} {id : Option Nat}
    (unique : (names.map Prod.fst).Nodup) (bounded : raw < 2^64)
    (ok : pointer names path raw = .ok id) :
    (AllowedipsRelation.pointer (interpretation names) id).toNat = raw ∧
    (∀ x, id = some x → interpretation names x ≠ 0) := by
  unfold pointer at ok
  by_cases zero : raw = 0
  · subst raw
    have eq : none = id := Except.ok.inj ok
    subst id
    exact ⟨rfl,by intros; contradiction⟩
  · simp only [beq_iff_eq,zero,↓reduceIte] at ok
    cases found : names.find? (·.2 == raw) with
    | none => rw [found] at ok; cases ok
    | some pair =>
      rw [found] at ok
      have eq : some pair.1 = id := Except.ok.inj ok
      subst id
      have member := List.mem_of_find?_eq_some found
      have address : pair.2 = raw := by simpa using List.find?_some found
      refine ⟨?_,?_⟩
      · simp only [AllowedipsRelation.pointer,Option.map_some,Option.getD_some,
          interpretation_of_mem unique member,address,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded]
      · intro x eq
        cases Option.some.inj eq
        exact interpretation_nonnull unique member (by omega) (by omega)

theorem address_value {names : List (Nat×Nat)} {id : Option Nat} {raw : Nat}
    (ok : address names id = .ok raw) :
    AllowedipsRelation.pointer (interpretation names) id = .ofNat 64 raw := by
  cases id with
  | none => cases ok; rfl
  | some id =>
    simp only [address] at ok
    cases found : names.find? (·.1 == id) with
    | none => rw [found] at ok; cases ok
    | some pair =>
      rw [found] at ok
      have eq : pair.2 = raw := Except.ok.inj ok
      simp only [AllowedipsRelation.pointer,Option.map_some,Option.getD_some,interpretation,
        found,eq]

#print axioms pointer_value
end Binary.Pair.Trie
