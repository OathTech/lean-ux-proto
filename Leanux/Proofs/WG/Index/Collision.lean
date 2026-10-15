import Leanux.Proofs.WG.Index.Lookup

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

abbrev bucketHas := noise_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas

def bucketWalk (walk collide : Decision) (index : Nat) (entries : List IndexEntry) : M Bool := do
  for e in entries do
    _ ← branch walk true
    if ← branch collide (e.index == index) then return true
  _ ← branch walk false
  return false

theorem bucketHas_source (walk collide : Decision) (index : Nat) :
    bucketHas walk collide index = (do
      let entries ← indexBucket index
      bucketWalk walk collide index entries) := rfl

theorem bucketWalk_cons (walk collide : Decision) (index : Nat) (e : IndexEntry)
    (es : List IndexEntry) :
    bucketWalk walk collide index (e :: es) = (do
      _ ← branch walk true
      let equal ← branch collide (e.index == index)
      if equal then pure true else bucketWalk walk collide index es) := by
  simp [bucketWalk, List.forIn_cons, branch, bind_assoc]
  split <;> simp [bind_assoc]

theorem bucketWalk_returns (walk collide : Decision) (index : Nat)
    (entries : List IndexEntry) (k : Kernel) :
    Returns (bucketWalk walk collide index entries) (fun w => w.k = k)
      (fun result w => result = entries.any (·.index == index) ∧ w.k = k) := by
  induction entries with
  | nil =>
    rw [returns_iff]
    simp only [bucketWalk, List.forIn_nil, bind_pure_comp, pure_bind]
    mvcgen [branch]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
  | cons e es ih =>
    have ht := (returns_iff _ _ _).mp ih
    rw [returns_iff, bucketWalk_cons]
    mvcgen [branch, ht]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
    all_goals grind

theorem bucket_any (index : Nat) (table : List IndexEntry) :
    (bucket index table).any (·.index == index) = table.any (·.index == index) := by
  simp only [bucket, List.any_filter]
  congr 1
  funext e
  by_cases same : e.index = index <;> simp [same]

theorem bucketHas_returns (walk collide : Decision) (index : Nat) (d : Device) :
    Returns (bucketHas walk collide index) (fun w => w.k.wg = some d)
      (fun result w => result = d.indexTable.any (·.index == index) ∧ w.k.wg = some d) := by
  have hg : Returns (indexBucket index) (fun w => w.k.wg = some d)
      (fun entries w => entries = bucket index d.indexTable ∧ w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [indexBucket, getDev, getK, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [bucket]
  rw [bucketHas_source]
  apply returns_bind _ _ hg
  intro entries w pre
  obtain ⟨he, hd⟩ := pre
  subst entries
  obtain ⟨result, final, run, found, kernel⟩ :=
    bucketWalk_returns walk collide index (bucket index d.indexTable) w.k w rfl
  exact ⟨result, final, run, by simpa [bucket_any] using found, by rw [kernel]; exact hd⟩

end Leanux.Proofs.WG.Index
