import PairWordStore
import PairIndexStorageProof

namespace Binary.Pair.Index

/-- Combined effect of the actual three unlink stores; the successor store
is skipped on NULL. Full reconstruction is needed only after this segment. -/
def unlinkMemory (m : DataMem) (o : Offsets) (removed previous next : Nat) : DataMem :=
  let first := write64 m previous next
  let second := if next=0 then first else write64 first (next+o.pprev) previous
  write64 second (removed+o.pprev) 0

def UnlinkWrites (o : Offsets) (removed previous next : Nat) (a : BitVec 64) : Prop :=
  InRange (.ofNat 64 previous) 8 a ∨
    (next≠0 ∧ InRange (.ofNat 64 (next+o.pprev)) 8 a) ∨
    InRange (.ofNat 64 (removed+o.pprev)) 8 a

theorem unlink_word_frame (m : DataMem) (o : Offsets) (removed previous next : Nat)
    (path : String) (address size : Nat)
    (apart : ∀ a, InRange (.ofNat 64 address) size a → ¬UnlinkWrites o removed previous next a) :
    word (unlinkMemory m o removed previous next) path address size=word m path address size := by
  unfold unlinkMemory
  rw [word_write64_frame _ _ _ _ _ _ (fun a inside h => apart a inside (.inr (.inr h)))]
  split
  · exact word_write64_frame _ _ _ _ _ _ (fun a inside h => apart a inside (.inl h))
  · rename_i nonzero
    rw [word_write64_frame _ _ _ _ _ _ (fun a inside h => apart a inside (.inr (.inl ⟨nonzero,h⟩)))]
    exact word_write64_frame _ _ _ _ _ _ (fun a inside h => apart a inside (.inl h))

/-- Exact word effect, with byte separation used only when the read is not
the destination of a store. This covers both neighbour words and unhashing. -/
theorem unlink_word (m : DataMem) (o : Offsets) (removed previous next : Nat)
    (path : String) (address : Nat)
    (bounded : address+8≤2^64) (prevBound : previous<2^64) (nextBound : next<2^64)
    (apart : ∀ destination ∈ previous::(removed+o.pprev)::(if next=0 then [] else [next+o.pprev]), address≠destination →
      ∀ a, InRange (.ofNat 64 address) 8 a → ¬InRange (.ofNat 64 destination) 8 a) :
    word (unlinkMemory m o removed previous next) path address 8 =
      if address=removed+o.pprev then .ok 0 else
      if next≠0 ∧ address=next+o.pprev then .ok previous else
      if address=previous then .ok next else word m path address 8 := by
  unfold unlinkMemory
  rw [word_write64 _ _ _ _ _ bounded (by decide) (apart _ (by simp))]
  by_cases cleared : address=removed+o.pprev
  · simp only [cleared,↓reduceIte]
  · simp only [cleared,↓reduceIte]
    by_cases zero : next=0
    · simp only [zero,↓reduceIte,ne_eq,not_true_eq_false,false_and]
      exact word_write64 _ _ _ _ _ bounded (by decide) (apart _ (by simp [zero]))
    · simp only [zero,↓reduceIte,ne_eq,not_false_eq_true,true_and]
      rw [word_write64 _ _ _ _ _ bounded prevBound (apart _ (by simp [zero]))]
      by_cases successor : address=next+o.pprev
      · simp only [successor,↓reduceIte]
      · simp only [successor,↓reduceIte]
        exact word_write64 _ _ _ _ _ bounded nextBound (apart _ (by simp))

#print axioms unlink_word
end Binary.Pair.Index
