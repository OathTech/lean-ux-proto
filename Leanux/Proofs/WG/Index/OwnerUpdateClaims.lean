import Leanux.Proofs.WG.Index.OwnerIndexFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

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

end Leanux.Proofs.WG.Index
