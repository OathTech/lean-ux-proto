import Leanux.Proofs.WG.Noise.RestartModel
import Leanux.Proofs.WG.Noise.StateEdges
import Leanux.Proofs.WG.Index.ConsumeFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

def RestartKernel (tracked : PeerId) (cursor : Nat) (allowed : Option KeypairId → Prop)
    (k : WGWorld) : Prop :=
  ∃ d, k.dev = some d ∧ RestartDevice tracked cursor allowed d

theorem restartDevice_insert (tracked pid : PeerId) (cursor : Nat)
    (allowed : Option KeypairId → Prop) (d : Device) (old replacement : Peer)
    (valid : RestartDevice tracked cursor allowed d)
    (read : d.peers[pid]? = some old) (same : replacement.keypairNext = old.keypairNext) :
    RestartDevice tracked cursor allowed { d with peers := d.peers.insert pid replacement } := by
  refine ⟨valid.1, ?_⟩
  intro p found
  by_cases h : pid = tracked
  · subst pid
    simp only [Std.TreeMap.getElem?_insert_self, Option.some.injEq] at found
    subst p
    rw [same]
    exact valid.2 old read
  · simp [Std.TreeMap.getElem?_insert, h] at found
    exact valid.2 p found

theorem restartDevice_erase (tracked pid : PeerId) (cursor : Nat)
    (allowed : Option KeypairId → Prop) (d : Device)
    (valid : RestartDevice tracked cursor allowed d) :
    RestartDevice tracked cursor allowed { d with peers := d.peers.erase pid } := by
  refine ⟨valid.1, ?_⟩
  intro p found
  by_cases h : pid = tracked
  · subst pid
    simp at found
  · simp [Std.TreeMap.getElem?_erase, h] at found
    exact valid.2 p found

/-- Local variant of Keypairs.Frames.WGBase.setPeer_spec for next-slot state,
which the shared snapshot omits. The replacement must retain the read next slot. -/
theorem setPeer_spec_restart_variant (tracked pid : PeerId) (cursor : Nat)
    (allowed : Option KeypairId → Prop) (replacement : Peer) :
    ⦃fun w => ⌜RestartKernel tracked cursor allowed w ∧
      ∃ old, peerAt w pid = some old ∧ replacement.keypairNext = old.keypairNext⌝⦄
      setPeer pid replacement
    ⦃⇓? _ w => ⌜RestartKernel tracked cursor allowed w⌝⦄ := by
  rw [← ensures_iff]
  intro w ambient u out after pre run
  obtain ⟨⟨d, device, valid⟩, old, read, same⟩ := pre
  have result := restartDevice_insert tracked pid cursor allowed d old replacement valid
    (by simpa [peerAt, device] using read) same
  cases run
  exact ⟨_, by simp [device], result⟩

/-- Local variant of Keypairs.Frames.WGBase.peerGetMaybeZero_spec. -/
theorem peerGetMaybeZero_spec_restart_variant (tracked : PeerId) (cursor : Nat)
    (allowed : Option KeypairId → Prop) (peer : Option PeerId) :
    ⦃fun w => ⌜RestartKernel tracked cursor allowed w⌝⦄ peerGetMaybeZero peer
      ⦃⇓? _ w => ⌜RestartKernel tracked cursor allowed w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨d, device, valid⟩ := pre
  cases peer with
  | none =>
    simp [peerGetMaybeZero, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨d, device, valid⟩
  | some pid =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, device, resident,
        branch, AmbientM.branch, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      by_cases zero : p.refcount = 0
      · simp [peerGetMaybeZero, requireNotPending, refcountIncNotZero,
          getDev, device, getPeer, resident, zero, branch, branchCmp,
          AmbientM.branch, AmbientM.branchCmp] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨d, device, valid⟩
      · by_cases overflow : 2147483647 ≤ p.refcount
        · simp [peerGetMaybeZero, requireNotPending, refcountIncNotZero,
            getDev, device, getPeer, resident, zero, overflow, branch, branchCmp,
            AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported] at run
          cases run
        · simp [peerGetMaybeZero, requireNotPending, refcountIncNotZero,
            getDev, device, getPeer, resident, zero, overflow, branch, branchCmp,
            AmbientM.branch, AmbientM.branchCmp, setPeer, modifyDev] at run
          rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
          exact ⟨_, rfl, restartDevice_insert tracked pid cursor allowed d p _ valid resident rfl⟩

/-- Local variant of Keypairs.Frames.WGBase.pubkeyLookup_spec. -/
theorem pubkeyLookup_spec_restart_variant (tracked : PeerId) (cursor : Nat)
    (allowed : Option KeypairId → Prop) (key : Key) :
    ⦃fun w => ⌜RestartKernel tracked cursor allowed w⌝⦄ pubkeyLookup key
      ⦃⇓? _ w => ⌜RestartKernel tracked cursor allowed w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨d, device, valid⟩ := pre
  simp [pubkeyLookup, getDev, device, branch, AmbientM.branch] at run
  exact (ensures_iff _ _ _).mpr (peerGetMaybeZero_spec_restart_variant tracked cursor allowed _)
    g _ result final after ⟨d, device, valid⟩ run

end Leanux.Proofs.WG.Noise
