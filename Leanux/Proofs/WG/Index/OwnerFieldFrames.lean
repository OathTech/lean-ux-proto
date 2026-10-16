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

theorem handshakeZero_ownersFresh (kp : KeypairId) (pid : PeerId) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ handshakeZero pid ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  have hs := setPeer_ownersFresh kp
  mvcgen [handshakeZero, getPeer, getDev, getK, invariant, hs]

theorem deriveKeys_ownersFresh (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ deriveKeys kp initiator ck ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  let P := fun k : Kernel => ∃ d, k.wg = some d ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d ∧
    kp < d.nextKeypairId ∧ ∀ e ∈ d.indexTable, e.owner ≠ .keypair kp
  have hh := hiddenClock64_kernel_spec P
  have hk := kdf_wg_spec P
  have ho := kdfOut_wg_spec P
  have hs := setKeypair_ownersFresh kp
  mvcgen [deriveKeys, getKeypair, getDev, getK, invariant, hh, hk, ho, hs]

theorem setPeer_ownersBounded (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜OwnersBoundedSafe w⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  mvcgen [setPeer, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [OwnersBoundedSafe, KeypairOwnersBounded]
  all_goals grind

end Leanux.Proofs.WG.Index
