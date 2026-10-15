import Leanux.Proofs.WG.Index.OwnerFieldFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem indexRemove_ownersFresh (kp : KeypairId) (owner : IndexOwner) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ indexRemove owner ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  obtain ⟨d, device, unique, bounded, small, fresh⟩ := pre
  obtain ⟨r, v, hr, hd⟩ := indexRemove_exact owner d w device
  rw [run] at hr
  cases hr
  refine ⟨_, hd, remove_owners owner _ unique, ?_, small, ?_⟩
  · intro e member id own
    exact bounded e (List.mem_filter.mp member).1 id own
  · intro e member
    exact fresh e (List.mem_filter.mp member).1

theorem keypairPut_ownersFresh (kp : KeypairId) (id : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ keypairPut id now ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  have hr := indexRemove_ownersFresh kp
  have hs := setKeypair_ownersFresh kp
  mvcgen [keypairPut, IndexOwner.peerDeref, IndexOwner.peerWord, getKeypair, getDev,
    getK, refcountDecAndTest, branch, branchCmp, invariant, unsupported,
    modifyDev, modifyK, hr, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [OwnersFresh, KeypairOwnersBounded]
  all_goals grind

theorem addNewKeypair_ownersFresh (pid : PeerId) (kp : KeypairId) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ addNewKeypair pid kp ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  have hp := keypairPut_ownersFresh kp
  have hs := setPeer_ownersFresh kp
  noise_vcgen [addNewKeypair, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
    getPeer, getKeypair, getDev, getK, branch, invariant, hp, hs]

theorem replace_owners_bounded (d : Device) (pid : PeerId) (kp : KeypairId)
    (bounded : KeypairOwnersBounded d) (small : kp < d.nextKeypairId) :
    KeypairOwnersBounded { d with indexTable := replaceOwner pid kp d.indexTable } := by
  intro e member id own
  change e ∈ replaceOwner pid kp d.indexTable at member
  unfold replaceOwner at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  subst e
  by_cases replaced : old.owner = .handshake pid
  · simp [replaced] at own
    subst id
    exact small
  · simp [replaced] at own
    exact bounded old oldMember id own

theorem indexReplace_ownersFresh (pid : PeerId) (kp : KeypairId) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ indexReplaceHandshake pid kp ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  obtain ⟨d, device, unique, bounded, small, fresh⟩ := pre
  obtain ⟨r, v, hr, value, hd⟩ := indexReplace_exact pid kp d w device
  rw [run] at hr
  cases hr
  refine ⟨_, hd, ?_⟩
  cases result
  · exact ⟨unique, bounded⟩
  · exact ⟨replace_owners pid kp _ unique fresh, replace_owners_bounded d pid kp bounded small⟩

end Leanux.Proofs.WG.Index
