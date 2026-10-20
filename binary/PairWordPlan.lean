import PairWordStore

namespace Binary.Pair

def write32 (m : DataMem) (address value : Nat) : DataMem :=
  m.storeInt (.ofNat 64 address) 4 (BitVec.ofNat 32 value).toInt

theorem word_write32_same (m : DataMem) (path : String) (address value : Nat)
    (bounded : address+4≤2^64) (small : value<2^32) :
    word (write32 m address value) path address 4=.ok value := by
  apply Trie.word_of_loadInt path bounded
  simpa only [write32,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using
    load32_store m (.ofNat 64 address) (.ofNat 32 value)

theorem word_write32_frame (m : DataMem) (path : String) (address size destination value : Nat)
    (apart : ∀ a, InRange (.ofNat 64 address) size a → ¬InRange (.ofNat 64 destination) 4 a) :
    word (write32 m destination value) path address size=word m path address size :=
  (Trie.word_frame (storeInt_frame m (.ofNat 64 destination) 4 _) path address size apart).symm

/-- Concrete stores in execution order. Repeated destinations are retained,
including overwritten poison values; the theorem computes the last effect. -/
def write64s : DataMem → List (Nat×Nat) → DataMem
  | m, [] => m
  | m, (address,value)::rest => write64s (write64 m address value) rest

def wordEffect (address : Nat) (before : Decode Nat) : List (Nat×Nat) → Decode Nat
  | [] => before
  | (destination,value)::rest =>
    wordEffect address (if address=destination then .ok value else before) rest

theorem word_write64s (m : DataMem) (stores : List (Nat×Nat))
    (path : String) (address : Nat) (bounded : address+8≤2^64)
    (small : ∀ destination value, (destination,value) ∈ stores → value<2^64)
    (apart : ∀ destination value, (destination,value) ∈ stores → address≠destination →
      ∀ a, InRange (.ofNat 64 address) 8 a → ¬InRange (.ofNat 64 destination) 8 a) :
    word (write64s m stores) path address 8=wordEffect address (word m path address 8) stores := by
  induction stores generalizing m with
  | nil => rfl
  | cons store rest ih =>
    rw [write64s,ih _ (fun a v member => small a v (by simp [member]))
      (fun a v member => apart a v (by simp [member]))]
    rw [word_write64 _ _ _ _ _ bounded (small store.1 store.2 (by simp)) (apart store.1 store.2 (by simp))]
    rfl

theorem word_write64s_frame (m : DataMem) (stores : List (Nat×Nat))
    (path : String) (address size : Nat)
    (apart : ∀ destination value, (destination,value) ∈ stores →
      ∀ a, InRange (.ofNat 64 address) size a → ¬InRange (.ofNat 64 destination) 8 a) :
    word (write64s m stores) path address size=word m path address size := by
  induction stores generalizing m with
  | nil => rfl
  | cons store rest ih =>
    rw [write64s,ih _ (fun a v member => apart a v (by simp [member]))]
    exact word_write64_frame _ _ _ _ _ _ (apart store.1 store.2 (by simp))

theorem write64s_frame (m : DataMem) (stores : List (Nat×Nat)) :
    EqualOutside (fun a => ∃ destination value, (destination,value) ∈ stores ∧
      InRange (.ofNat 64 destination) 8 a) m (write64s m stores) := by
  induction stores generalizing m with
  | nil => intro a _; rfl
  | cons store rest ih =>
    intro a outside
    have first := write64_frame m store.1 store.2 a (fun inside => outside ⟨store.1,store.2,by simp,inside⟩)
    have remaining := ih (write64 m store.1 store.2) a (by
      rintro ⟨address,value,member,inside⟩
      exact outside ⟨address,value,by simp [member],inside⟩)
    exact first.trans remaining

#print axioms word_write64s
#print axioms write64s_frame
end Binary.Pair
