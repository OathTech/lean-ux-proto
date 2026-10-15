import Leanux.Proofs.WG.Noise.RotationSource
import Leanux.Proofs.WG.Index.SendFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem keypairPut_counter (key : Option KeypairId) (now : Bool) (counter : Nat) :
    ⦃fun w => ⌜w.k.keypairCounter = counter⌝⦄ keypairPut key now
      ⦃⇓? _ w => ⌜w.k.keypairCounter = counter⌝⦄ := by
  have hr := Index.refcountDecAndTest_kernel_variant (fun k => k.keypairCounter = counter)
  noise_vcgen [keypairPut, indexRemove, IndexOwner.peerDeref, IndexOwner.peerWord,
    _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry, getPeer, getKeypair, getDev, getK,
    setKeypair, modifyDev, modifyK, branch, invariant, unsupported, hr]

theorem rotationExecute_counter (pid : PeerId) (actions : List RotationAction) (counter : Nat) :
    ⦃fun w => ⌜w.k.keypairCounter = counter⌝⦄ rotationExecute pid actions
      ⦃⇓? _ w => ⌜w.k.keypairCounter = counter⌝⦄ := by
  induction actions with
  | nil => mvcgen [rotationExecute]
  | cons action rest ih =>
    cases action with
    | write change =>
      noise_vcgen [rotationExecute, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
        getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, ih]
    | put key =>
      have hp := keypairPut_counter key true counter
      mvcgen [rotationExecute, hp, ih]

theorem addNewKeypair_counter (pid : PeerId) (kp : KeypairId) (counter : Nat) :
    ⦃fun w => ⌜w.k.keypairCounter = counter⌝⦄ addNewKeypair pid kp
      ⦃⇓? _ w => ⌜w.k.keypairCounter = counter⌝⦄ := by
  have he := fun actions => rotationExecute_counter pid actions counter
  rw [addNewKeypair_rotation_source]
  mvcgen [rotationSource, getPeer, getKeypair, getDev, getK, branch, invariant, he]

theorem rotationPeer_word (actions : List RotationAction) (p : Peer) :
    (rotationPeer actions p).handshakeEntryPeer = p.handshakeEntryPeer := by
  induction actions generalizing p with
  | nil => rfl
  | cons action rest ih =>
    cases action with
    | put key => exact ih p
    | write change =>
      simp only [rotationPeer, ih]
      cases change <;> rfl

end Leanux.Proofs.WG.Noise
