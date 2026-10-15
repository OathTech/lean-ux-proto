import Leanux.Proofs.WG.Index.HandshakeFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Owner uniqueness and allocation bounds, with a designated unhashed identity.
This predicate does not assert keypair-store residency or slot safety. -/
def OwnersFresh (kp : KeypairId) (w : World) : Prop :=
  ∃ d, w.k.wg = some d ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d ∧
    kp < d.nextKeypairId ∧ ∀ e ∈ d.indexTable, e.owner ≠ .keypair kp

def OwnersSafe (w : World) : Prop :=
  ∃ d, w.k.wg = some d ∧ UniqueOwners d.indexTable

def OwnersBoundedSafe (w : World) : Prop :=
  ∃ d, w.k.wg = some d ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d

theorem setPeer_ownersFresh (kp : KeypairId) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  mvcgen [setPeer, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [OwnersFresh, KeypairOwnersBounded]
  all_goals grind

theorem setKeypair_ownersFresh (kp id : KeypairId) (k : Keypair) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ setKeypair id k ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  mvcgen [setKeypair, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [OwnersFresh, KeypairOwnersBounded]
  all_goals grind

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

theorem handshakeZero_ownersFresh (kp : KeypairId) (pid : PeerId) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ handshakeZero pid ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  have hs := setPeer_ownersFresh kp
  mvcgen [handshakeZero, getPeer, getDev, getK, invariant, hs]

theorem deriveKeys_ownersFresh (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ deriveKeys kp initiator ck ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  let P := fun k : Kernel => ∃ d, k.wg = some d ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d ∧
    kp < d.nextKeypairId ∧ ∀ e ∈ d.indexTable, e.owner ≠ .keypair kp
  have hh := hiddenClock64_kernel_spec P
  have hk := kdf_kernel_spec P
  have ho := kdfOut_kernel_spec P
  have hs := setKeypair_ownersFresh kp
  mvcgen [deriveKeys, getKeypair, getDev, getK, invariant, hh, hk, ho, hs]

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
