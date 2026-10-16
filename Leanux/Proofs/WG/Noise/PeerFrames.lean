import Leanux.Proofs.WG.Noise.Slots
import Leanux.Proofs.WG.Noise.CryptoFrames

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem bucketHas_kernel_spec (P : Kernel → Prop) (walk collide : Decision) (index : Nat) :
    ⦃fun w => ⌜P w.k⌝⦄
      (noise_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas) walk collide index
    ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  noise_vcgen [_private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas,
    indexBucket, getDev, getK, branch, invariant]
  case inv1 => exact ((⇓? _ w => ⌜P w.k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals try trivial

theorem keypairCreate_peers_spec (P : (PeerId → Option Peer) → Prop) (pid : Option PeerId) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ keypairCreate pid
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  have hh := keypairAllocation_kernel_spec (fun k => P (fun i => k.wg.bind fun d => d.peers[i]?))
  mvcgen [keypairCreate, getDev, getK, setKeypair, modifyDev, modifyK, branch, invariant, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try dsimp [peerAt] at *
  all_goals simp_all [peerAt, Option.bind_map, Function.comp_def]
  all_goals assumption

theorem deriveKeys_peers_spec (P : (PeerId → Option Peer) → Prop)
    (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ deriveKeys kp initiator ck
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  let PK := fun k : Kernel => P (fun i => k.wg.bind fun d => d.peers[i]?)
  have hh := hiddenClock64_kernel_spec PK
  have hk := kdf_wg_spec PK
  have ho := kdfOut_wg_spec PK
  mvcgen [deriveKeys, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    invariant, hh, hk, ho]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try dsimp [peerAt] at *
  all_goals simp_all [PK, peerAt, Option.bind_map, Function.comp_def]
  all_goals assumption

end Leanux.Proofs.WG.Noise
