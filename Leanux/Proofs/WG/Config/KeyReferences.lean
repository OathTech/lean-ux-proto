import Leanux.Proofs.WG.Config.QueuedHandshake

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def withKeypair (d : Device) (id : KeypairId) (k : Keypair) : Device :=
  { d with keypairs := d.keypairs.insert id k }

theorem keypairGet_none (d : Device) :
    Returns (keypairGet none) (fun w => w.dev = some d)
      (fun result w => result = none ∧ w.dev = some d) := by
  intro g ambient device
  refine ⟨none, g, {ambient with steps := ambient.steps.push {
    decision := .keypairGetNull, outcome := true, netRx := ambient.netRxSection}}, ?_, rfl, device⟩
  simp [keypairGet, branch, AmbientM.branch]
  rfl

theorem keypairGet_present (id : KeypairId) (d : Device) (k : Keypair)
    (resident : d.keypairs[id]? = some k) :
    Ensures (keypairGet (some id)) (fun w => w.dev = some d)
      (fun result w => if k.refcount = 0 then result = none ∧ w.dev = some d
        else result = some id ∧ w.dev = some (withKeypair d id { k with refcount := k.refcount + 1 })) := by
  intro g ambient result final after device run
  by_cases zero : k.refcount = 0
  · simp [keypairGet, branch, AmbientM.branch, getKeypair, getDev, device,
      resident, refcountIncNotZero, branchCmp, AmbientM.branchCmp, zero] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    simp [zero, device]
  · by_cases overflow : 2147483647 ≤ k.refcount
    · simp [keypairGet, branch, AmbientM.branch, getKeypair, getDev, device,
        resident, refcountIncNotZero, branchCmp, AmbientM.branchCmp, zero,
        overflow, unsupported, AmbientM.unsupported] at run
      cases run
    · simp [keypairGet, branch, AmbientM.branch, getKeypair, getDev, device,
        resident, refcountIncNotZero, branchCmp, AmbientM.branchCmp, zero,
        overflow, setKeypair, modifyDev] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      simp [zero, withKeypair]

theorem keypairPut_none (d : Device) :
    Returns (keypairPut none false) (fun w => w.dev = some d)
      (fun _ w => w.dev = some d) := by
  intro g ambient device
  refine ⟨(), g, {ambient with steps := ambient.steps.push {
    decision := .keypairPutNull, outcome := true, netRx := ambient.netRxSection}}, ?_, device⟩
  simp [keypairPut, branch, AmbientM.branch]
  rfl

theorem keypairPut_retained (id : KeypairId) (d : Device) (k : Keypair)
    (resident : d.keypairs[id]? = some k) (retained : 1 < k.refcount) :
    Returns (keypairPut (some id) false) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (withKeypair d id { k with refcount := k.refcount - 1 })) := by
  intro g ambient device
  let first := {ambient with steps := (ambient.steps.push {
    decision := .keypairPutNull, outcome := false, netRx := ambient.netRxSection}).push {
    decision := .keypairPutUnreferenceNow, outcome := false, netRx := ambient.netRxSection}}
  let second := {first with steps := (first.steps.push {
    decision := .refcountSubPositive, outcome := true, operands := some (k.refcount, 0), netRx := first.netRxSection}).push {
    decision := .refcountSubToZero, outcome := false, operands := some (k.refcount, 1), netRx := first.netRxSection}}
  let ending := {second with steps := ((second.steps.push {
    decision := .refcountSubNonpositive, outcome := false, netRx := second.netRxSection}).push {
    decision := .refcountSubUnderflow, outcome := false, netRx := second.netRxSection}).push {
    decision := .keypairKrefPutReleased, outcome := false, netRx := second.netRxSection}}
  refine ⟨(), {g with dev := some (withKeypair d id {k with refcount := k.refcount - 1})}, ending, ?_, rfl⟩
  have live : 0 < k.refcount := by omega
  have notZero : k.refcount ≠ 0 := by omega
  have notLast : k.refcount ≠ 1 := by omega
  have zeroTest : (k.refcount == 0) = false := by simpa using notZero
  have lastTest : (k.refcount == 1) = false := by simpa using notLast
  simp [keypairPut, getKeypair, getDev, device, resident, branch, AmbientM.branch,
    refcountDecAndTest, branchCmp, AmbientM.branchCmp, live, notZero, notLast, zeroTest, lastTest,
    setKeypair, modifyDev, withKeypair, first, second, ending]
  rfl

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
        · simp [keyReferenceRoundTrip, found, zero, withKeypair, Std.TreeMap.getElem?_insert, Ne.symm same]

end Leanux.Proofs.WG.Config
