import LookupOwnerRelation
import LookupOwnerSource

namespace Binary.Sequential
open Leanux Leanux.WG TrustBase LookupRelation

/-- Endpoint representation: ordinary current bytes only. No decisions,
execution history, pending update, or source logging fields occur here. -/
def At (c : Config) (memory : Mem 64) (v : View) : Prop :=
  selected c v.bucket = c.focus.owner ∧
  (∃ head : Address,
    memory.loadInt (c.table + .ofNat 64 (8 * (c.query % 8192))) 8 = some (head.toNat : Int) ∧
    BucketShape memory head (v.bucket.map fun e => (ownerAddress c e.owner, e))) ∧
  (match c.focus.owner with
   | none => v.ownerWord = none
   | some owner => ∃ word, v.ownerWord = some word ∧
       OwnerWord.Field c.peers memory (ownerAddress c owner) word) ∧
  (match c.focus.peer with
   | none => v.count = none
   | some pid => ∃ count, v.count = some count ∧ c.peers pid ≠ 0 ∧
       memory.loadInt (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 = some (count : Int))

def Related (c : Config) (s : MachineState) (world : World) : Prop :=
  ∃ v, project c world = some v ∧ At c s.data.dmem v

/-- A bridge for reusing physical frame lemmas; the histories are empty,
so no pending-phase or trace-alignment obligation is introduced. -/
theorem at_iff (c : Config) (s : MachineState) (v : View) :
    At c s.data.dmem v ↔ Physical c [] [] s v := by
  have ordinary : ownerPending [] s = none := ownerPending_none _ _ rfl
  cases ho : c.focus.owner <;> cases hp : c.focus.peer <;>
    simp only [At, Physical, ho, hp, OwnerFieldAt, ordinary, countPhase, helperActive,
      List.foldl_nil, Bool.false_eq_true, ite_false, PeerCountPhase.At] <;> rfl

theorem of_physical {c raw seen s v} (physical : Physical c raw seen s v)
    (count : countPhase raw seen = none) (owner : ownerPending seen s = none) :
    At c s.data.dmem v := by
  cases ho : c.focus.owner <;> cases hp : c.focus.peer <;>
    simpa only [At, Physical, ho, hp, OwnerFieldAt, owner, count, PeerCountPhase.At] using physical

theorem At.frame {c : Config} {s t : MachineState} {v : View} {writes : Address → Prop} (represented : At c s.data.dmem v)
    (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ a, Reads c v a → ¬writes a) : At c t.data.dmem v := by
  apply (at_iff c t v).mpr
  exact ((at_iff c s v).mp represented).frame_inactive c [] [] [] [] s t v rfl rfl
    (ownerPending_none _ _ rfl) (ownerPending_none _ _ rfl) writes frame apart

theorem At.count_update {c : Config} {s t : MachineState} {v : View} {writes : Address → Prop} (represented : At c s.data.dmem v)
    (pid : PeerId) (focused : c.focus.peer = some pid) (number : Nat)
    (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (bucketApart : ∀ a, LookupBucketBytes c v a → ¬writes a)
    (ownerApart : ∀ a, LookupOwnerBytes c a → ¬writes a)
    (countAt : t.data.dmem.loadInt (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 = some (number : Int)) :
    At c t.data.dmem {v with count := some number} := by
  apply (at_iff c t _).mpr
  exact ((at_iff c s v).mp represented).frame_count_updated c [] [] [] [] s t v pid focused number
    (ownerPending_none _ _ rfl) (ownerPending_none _ _ rfl) writes frame bucketApart ownerApart countAt

theorem At.owner_update {c : Config} {s t : MachineState} {v : View} {writes : Address → Prop} (represented : At c s.data.dmem v)
    (owner : IndexOwner) (focused : c.focus.owner = some owner) (word : Option PeerId)
    (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (bucketApart : ∀ a, LookupBucketBytes c v a → ¬writes a)
    (countApart : ∀ a, LookupCountBytes c a → ¬writes a)
    (ownerAt : OwnerWord.Field c.peers t.data.dmem (ownerAddress c owner) word) :
    At c t.data.dmem {v with ownerWord := some word} := by
  apply (at_iff c t _).mpr
  apply ((at_iff c s v).mp represented).frame_owner c [] [] [] [] s t v owner focused word
    rfl rfl writes frame bucketApart countApart
  simpa only [OwnerFieldAt, ownerPending_none [] t rfl] using ownerAt

theorem Related.frame {c : Config} {s t : MachineState} {world : World} {writes : Address → Prop}
    (related : Related c s world) (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬writes a) :
    Related c t world := by
  obtain ⟨v, projected, physical⟩ := related
  exact ⟨v, projected, physical.frame frame (apart v projected)⟩

#print axioms At.count_update
#print axioms At.owner_update
end Binary.Sequential
