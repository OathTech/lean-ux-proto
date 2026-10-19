import SourceAdapter
import PairIndexFrame
import PairUnlinkOwnership

namespace Binary.Pair.Index
open Leanux Leanux.WG
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]
local instance : LawfulBEq IndexEntry where
  eq_of_beq := by
    rintro ⟨i,o⟩ ⟨j,p⟩ h
    change (i==j && o==p)=true at h
    have parts : i=j ∧ o=p := by simpa only [Bool.and_eq_true,beq_iff_eq] using h
    cases parts.1
    cases parts.2
    rfl
  rfl := by rintro ⟨i,o⟩; change (i==i && o==o)=true; simp

theorem compareState_self (state : LookupState) : compareState state state=.ok () := by
  simp [compareState]
  rfl

theorem assertMemory_of_result {n o m w d expected} (device : w.wg.dev=some d)
    (decoded : reconstruct n o m=.ok expected)
    (compared : compareState expected (target d)=.ok ()) : assertMemory n o m w=.ok () := by
  unfold assertMemory
  rw [device,decoded]
  exact compared

theorem assertMemory_of_related {n o m w d} (device : w.wg.dev=some d)
    (related : Corresponds n o m d) : assertMemory n o m w=.ok () :=
  assertMemory_of_result device related (compareState_self _)

theorem remove_assert_of_parts {n o m w d} (device : w.wg.dev=some d)
    (storage : storageCheck n o=true) (related : Corresponds n o m d)
    (owners : Remove.ownership n o m=.ok (Remove.targetOwnership d)) :
    Remove.assertAt n o m w=.ok () := by
  have asserted := assertMemory_of_related device related
  unfold Remove.assertAt
  rw [storage]
  simp only [↓reduceIte,asserted,device,owners]
  change (if Remove.targetOwnership d==Remove.targetOwnership d then (Except.ok () : Except String Unit)
    else Except.error "remove: owner hashed state differs")=.ok ()
  rw [beq_self_eq_true]
  rfl

theorem compareState_ok {actual expected : LookupState} (checked : compareState actual expected=.ok ()) : actual=expected := by
  unfold compareState at checked
  obtain ⟨sizes,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,buckets,checked⟩ := bind_ok checked
  obtain ⟨owners,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨counts,_⟩ := check_ok _ _ _ _ checked
  have sizeEq : actual.buckets.size=expected.buckets.size := by simpa using sizes
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    show ([:actual.buckets.size] : Std.Legacy.Range).size=actual.buckets.size from by simp [Std.Legacy.Range.size],
    ←List.range_eq_range'] at buckets
  have each := forIn_ok (P := fun i => actual.buckets[i]! = expected.buckets[i]!) (by
    intro i _ before after run
    obtain ⟨equal,run⟩ := check_ok _ _ _ _ run
    exact ⟨(),(Except.ok.inj run).symm,eq_of_beq equal⟩) buckets
  have bucketEq : actual.buckets=expected.buckets := by
    apply Array.ext sizeEq
    intro i left right
    have equal := each i (List.mem_range.mpr left)
    simpa only [getElem!_pos actual.buckets i left,getElem!_pos expected.buckets i right] using equal
  have ownerEq := eq_of_beq owners
  have countEq := eq_of_beq counts
  cases actual
  cases expected
  cases bucketEq
  cases ownerEq
  cases countEq
  rfl

theorem assertMemory_ok {n o m w} (checked : assertMemory n o m w=.ok ()) :
    ∃ d, w.wg.dev=some d ∧ Corresponds n o m d := by
  unfold assertMemory at checked
  cases device : w.wg.dev with
  | none => rw [device] at checked; cases checked
  | some d =>
    rw [device] at checked
    obtain ⟨actual,decoded,checked⟩ := bind_ok checked
    have equal := compareState_ok checked
    subst actual
    exact ⟨d,rfl,mapError_ok decoded⟩

theorem remove_assert_ok {n o m w} (checked : Remove.assertAt n o m w=.ok ()) :
    ∃ d, w.wg.dev=some d ∧ Corresponds n o m d ∧ storageCheck n o=true ∧
      Remove.ownership n o m=.ok (Remove.targetOwnership d) := by
  unfold Remove.assertAt at checked
  obtain ⟨storage,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,related,checked⟩ := bind_ok checked
  obtain ⟨d,device,related⟩ := assertMemory_ok related
  rw [device] at checked
  obtain ⟨owners,decoded,checked⟩ := bind_ok checked
  obtain ⟨equal,_⟩ := check_ok _ _ _ _ checked
  have ownerEq := eq_of_beq equal
  rw [ownerEq] at decoded
  exact ⟨d,device,related,storage,mapError_ok decoded⟩

#print axioms remove_assert_ok
end Binary.Pair.Index
