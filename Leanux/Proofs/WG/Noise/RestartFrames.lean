import Leanux.Proofs.WG.Noise.RestartModel
import Leanux.Proofs.WG.Noise.StateEdges
import Leanux.Proofs.WG.Index.ConsumeFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

def RestartKernel (tracked : PeerId) (cursor : Nat) (allowed : Option KeypairId → Prop)
    (k : Kernel) : Prop :=
  ∃ d, k.wg = some d ∧ RestartDevice tracked cursor allowed d

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
    ⦃fun w => ⌜RestartKernel tracked cursor allowed w.k ∧
      ∃ old, peerAt w pid = some old ∧ replacement.keypairNext = old.keypairNext⌝⦄
      setPeer pid replacement
    ⦃⇓? _ w => ⌜RestartKernel tracked cursor allowed w.k⌝⦄ := by
  rw [← ensures_iff]
  intro w u out pre run
  obtain ⟨⟨d, device, valid⟩, old, read, same⟩ := pre
  have result := restartDevice_insert tracked pid cursor allowed d old replacement valid
    (by simpa [peerAt, device] using read) same
  simp [setPeer, modifyDev, modifyK, device, StateT.run_bind] at run
  cases run
  exact ⟨_, rfl, result⟩

/-- Local variant of Keypairs.Frames.WGBase.peerGetMaybeZero_spec. -/
theorem peerGetMaybeZero_spec_restart_variant (tracked : PeerId) (cursor : Nat)
    (allowed : Option KeypairId → Prop) (peer : Option PeerId) :
    ⦃fun w => ⌜RestartKernel tracked cursor allowed w.k⌝⦄ peerGetMaybeZero peer
      ⦃⇓? _ w => ⌜RestartKernel tracked cursor allowed w.k⌝⦄ := by
  have hs := setPeer_spec_restart_variant tracked
  mvcgen [peerGetMaybeZero, requireNotPending, getPeer, getDev, getK,
    refcountIncNotZero, branchCmp, unsupported, branch, invariant, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [peerAt]
  all_goals grind

/-- Local variant of Keypairs.Frames.WGBase.pubkeyLookup_spec. -/
theorem pubkeyLookup_spec_restart_variant (tracked : PeerId) (cursor : Nat)
    (allowed : Option KeypairId → Prop) (key : Key) :
    ⦃fun w => ⌜RestartKernel tracked cursor allowed w.k⌝⦄ pubkeyLookup key
      ⦃⇓? _ w => ⌜RestartKernel tracked cursor allowed w.k⌝⦄ := by
  have hg := peerGetMaybeZero_spec_restart_variant tracked cursor allowed
  mvcgen [pubkeyLookup, getDev, getK, branch, invariant, hg]

end Leanux.Proofs.WG.Noise
