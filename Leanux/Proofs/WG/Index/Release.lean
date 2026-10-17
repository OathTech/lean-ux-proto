import Leanux.Proofs.WG.Index.ReleaseModel
import Leanux.Proofs.WG.Index.Allocation
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Config Std.Do

/-- A non-NULL peer word suffices for the mirror's device dereference here;
this does not assert residency of the peer it names or reachable ownership. -/
theorem keypairPut_exact (id : KeypairId) (now : Bool) (d : Device) (k : Keypair)
    (resident : d.keypairs[id]? = some k) (live : 0 < k.refcount)
    (word : k.peer ≠ none) :
    Returns (keypairPut (some id) now) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (releasedDevice d id k now)) := by
  intro g ambient device
  let first := recordStep (recordStep ambient .keypairPutNull false) .keypairPutUnreferenceNow now
  let unhashed := if now then unhashKeypair d id else d
  let second := if now then recordStep first .idxRemoveHashed (d.indexTable.any (·.owner == .keypair id)) else first
  let positive := {second with steps := second.steps.push {
    decision := .refcountSubPositive, outcome := true, operands := some (k.refcount, 0),
    netRx := second.netRxSection}}
  let tested := {positive with steps := positive.steps.push {
    decision := .refcountSubToZero, outcome := k.refcount == 1, operands := some (k.refcount, 1),
    netRx := positive.netRxSection}}
  let refdone := if k.refcount = 1 then tested else
    recordStep (recordStep tested .refcountSubNonpositive false) .refcountSubUnderflow false
  let released := recordStep refdone .keypairKrefPutReleased (k.refcount == 1)
  let after := if k.refcount = 1 then
    recordStep released .idxRemoveHashed (unhashed.indexTable.any (·.owner == .keypair id))
    else released
  refine ⟨(), {g with dev := some (releasedDevice d id k now)}, after, ?_, rfl⟩
  have nonzero : k.refcount ≠ 0 := by omega
  have testZero : (k.refcount == 0) = false := by simp [nonzero]
  have testLast : (k.refcount == 1) = decide (k.refcount = 1) := by
    by_cases h : k.refcount = 1 <;> simp [h]
  have removeForm : indexRemove (.keypair id) = (do
    _ ← branch .idxRemoveHashed ((← get).any (·.owner == .keypair id))
    modify fun table => table.filter fun e => !(e.owner == .keypair id) : IndexM Unit) := rfl
  change (((do
    if ← branch .keypairPutNull false then return
    let k ← getKeypair id
    let removeEntry : WG.M Unit := do
      _ ← IndexOwner.peerDeref (.keypair id)
      liftIndex (indexRemove (.keypair id))
    if ← branch .keypairPutUnreferenceNow now then removeEntry
    setKeypair id {k with refcount := k.refcount - 1}
    if ← branch .keypairKrefPutReleased (← refcountDecAndTest k.refcount) then
      removeEntry
      modifyDev fun d => {d with keypairs := d.keypairs.erase id}) : WG.M Unit).run g).run ambient = _
  cases now <;> by_cases last : k.refcount = 1
  all_goals cases hp : k.peer
  all_goals try simp [hp] at word
  all_goals simp [IndexOwner.peerDeref, IndexOwner.peerWord, getKeypair, getDev,
    device, resident, hp, setKeypair, modifyDev, refcountDecAndTest,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, removeForm, liftIndex,
    first, unhashed, second, positive, tested, refdone, released, after, recordStep,
    releasedDevice, unhashKeypair, removeOwner, live, nonzero, testZero, testLast, last]
  all_goals rfl

end Leanux.Proofs.WG.Index
