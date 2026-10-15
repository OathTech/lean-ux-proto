import Leanux.Proofs.WG.Config.QueuedHandshake

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def withKeypair (d : Device) (id : KeypairId) (k : Keypair) : Device :=
  { d with keypairs := d.keypairs.insert id k }

theorem keypairGet_none (d : Device) :
    Returns (keypairGet none) (fun w => w.k.wg = some d)
      (fun result w => result = none ∧ w.k.wg = some d) := by
  rw [returns_iff]
  mvcgen [keypairGet, branch]

theorem keypairGet_present (id : KeypairId) (d : Device) (k : Keypair)
    (resident : d.keypairs[id]? = some k) :
    Ensures (keypairGet (some id)) (fun w => w.k.wg = some d)
      (fun result w => if k.refcount = 0 then result = none ∧ w.k.wg = some d
        else result = some id ∧ w.k.wg = some (withKeypair d id { k with refcount := k.refcount + 1 })) := by
  rw [ensures_iff]
  mvcgen [keypairGet, refcountIncNotZero, branch, branchCmp, getKeypair, getDev, getK,
    setKeypair, modifyDev, modifyK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withKeypair]
  all_goals grind only

theorem keypairPut_none (d : Device) :
    Returns (keypairPut none false) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some d) := by
  rw [returns_iff]
  mvcgen [keypairPut, branch]

theorem keypairPut_retained (id : KeypairId) (d : Device) (k : Keypair)
    (resident : d.keypairs[id]? = some k) (retained : 1 < k.refcount) :
    Returns (keypairPut (some id) false) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (withKeypair d id { k with refcount := k.refcount - 1 })) := by
  rw [returns_iff]
  mvcgen [keypairPut, refcountDecAndTest, branch, branchCmp, getKeypair, getDev, getK,
    setKeypair, modifyDev, modifyK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withKeypair]
  all_goals omega

/-- Exact ordered writes for a successful get followed by a non-releasing put.
The missing-target arm only totalizes this pure post-state description; the
original get stops if its target is missing. -/
def keyReferenceRoundTrip (d : Device) (kp : Option KeypairId) : Device :=
  match kp with
  | none => d
  | some id => match d.keypairs[id]? with
    | none => d
    | some k => if k.refcount = 0 then d
      else withKeypair (withKeypair d id { k with refcount := k.refcount + 1 }) id k

theorem keyReferenceRoundTrip_lookup (d : Device) (kp : Option KeypairId) (q : KeypairId) :
    (keyReferenceRoundTrip d kp).keypairs[q]? = d.keypairs[q]? := by
  cases kp with
  | none => rfl
  | some id =>
    cases found : d.keypairs[id]? with
    | none => simp [keyReferenceRoundTrip, found]
    | some k =>
      by_cases zero : k.refcount = 0
      · simp [keyReferenceRoundTrip, found, zero]
      · by_cases same : q = id
        · subst q; simp [keyReferenceRoundTrip, found, zero, withKeypair]
        · simp [keyReferenceRoundTrip, found, zero, withKeypair, Std.TreeMap.getElem?_insert, same, Ne.symm same]

end Leanux.Proofs.WG.Config
