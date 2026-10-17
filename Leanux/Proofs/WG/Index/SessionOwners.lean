import Leanux.Proofs.WG.Index.OwnerFrames
import Leanux.Proofs.WG.Index.SessionOperations

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

def allocatedOwners (created : Option KeypairId) (w : World) : Prop :=
  match created with
  | none => OwnersBoundedSafe w
  | some kp => OwnersFresh kp w

theorem keypairCreate_owners_spec (peer : Option PeerId) :
    ⦃fun w => ⌜OwnersBoundedSafe w⌝⦄ keypairCreate peer
      ⦃⇓? result w => ⌜allocatedOwners result w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  obtain ⟨d, device, unique, bounded⟩ := pre
  have effect := keypairCreate_exact peer d w.k.keypairCounter w result final ⟨device, rfl⟩ run
  cases result with
  | none => exact ⟨d, effect.1, unique, bounded⟩
  | some kp =>
    obtain ⟨rfl, hd, hc⟩ := effect
    exact ⟨_, hd, unique, created_bounded d _ peer bounded, Nat.lt_succ_self _, bounded_fresh d bounded⟩

theorem sessionAfterAllocation_owners (pid : PeerId) (st : Nat) (kp : KeypairId) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ sessionAfterAllocation pid st kp
      ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  have hs := setKeypair_ownersFresh kp
  have hd := deriveKeys_ownersFresh kp
  have hz := handshakeZero_ownersFresh kp
  have ha := addNewKeypair_ownersFresh pid kp
  have hr := indexReplace_ownersFresh pid kp
  mvcgen [sessionAfterAllocation, IndexOwner.peerWord, IndexOwner.peerDeref,
    getPeer, getDev, getK, getKeypair, branch, invariant, unsupported, hs, hd, hz, ha, hr]

theorem sessionAfterCreate_owners (pid : PeerId) (st : Nat) (created : Option KeypairId) :
    ⦃fun w => ⌜allocatedOwners created w⌝⦄ sessionAfterCreate pid st created
      ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  have ht := sessionAfterAllocation_owners pid st
  cases created <;> simp only [sessionAfterCreate, allocatedOwners]
  all_goals mvcgen [branch, invariant, ht]

theorem beginSession_owners_spec (pid : PeerId) :
    ⦃fun w => ⌜OwnersBoundedSafe w⌝⦄ beginSession pid ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  have hc := keypairCreate_owners_spec
  have ht := sessionAfterCreate_owners pid
  rw [beginSession_owner_source]
  mvcgen [IndexOwner.peerWord, WG.andM, getPeer, getDev, getK, branch, invariant, hc, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [OwnersBoundedSafe]
  all_goals grind

end Leanux.Proofs.WG.Index
