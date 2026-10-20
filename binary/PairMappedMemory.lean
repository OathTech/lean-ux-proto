import PairSpan
import PairTrieFields

namespace Binary.Pair

/-- Defined bytes survive stores. This says nothing about their values. -/
def MappedLe (before after : DataMem) : Prop :=
  ∀ address size, (before.loadInt address size).isSome=true →
    (after.loadInt address size).isSome=true

theorem MappedLe.refl (memory : DataMem) : MappedLe memory memory := fun _ _ h => h

theorem MappedLe.trans {before middle after : DataMem}
    (first : MappedLe before middle) (second : MappedLe middle after) : MappedLe before after :=
  fun address size read => second address size (first address size read)

theorem MappedLe.store (memory : DataMem) (address : BitVec 64) (size : Nat) (value : Int) :
    MappedLe memory (memory.storeInt address size value) :=
  fun a n read => storeInt_defined memory a address n size value read

theorem readNat_exists {s : MachineState} {address size}
    (mapped : (s.data.dmem.loadInt (.ofNat 64 address) size).isSome=true) :
    ∃ value, readNat s address size=.ok value := by
  cases bytes : s.data.dmem.loadBytes (.ofNat 64 address) size with
  | none => simp only [Mem.loadInt,bytes,Option.map_none,Option.isSome_none,Bool.false_eq_true] at mapped
  | some data => exact ⟨_,by simp only [readNat,bytes]; rfl⟩

theorem MappedLe.of_word {before after path address size value}
    (mapped : MappedLe before after) (read : word before path address size=.ok value) :
    (after.loadInt (.ofNat 64 address) size).isSome=true :=
  mapped _ _ (by rw [word_loadInt _ _ _ _ _ read]; rfl)

end Binary.Pair
