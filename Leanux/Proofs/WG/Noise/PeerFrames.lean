import Leanux.Proofs.WG.Noise.Slots
import Leanux.Proofs.WG.Noise.KernelFrames

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem indexRemove_peers_spec (P : (PeerId → Option Peer) → Prop)
    (pid : PeerId) (kind : IndexKind) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ indexRemove pid kind
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  have hm := modifyDev_peers_spec P
  noise_vcgen [indexRemove, _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry,
    getDev, getK, branch, invariant, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals try dsimp [peerAt] at *
  all_goals try simp_all
  all_goals try trivial

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

theorem indexInsert_peers_spec (P : (PeerId → Option Peer) → Prop)
    (pid : PeerId) (kind : IndexKind) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ indexInsert pid kind
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  have hm := modifyDev_peers_spec P
  have hh := hidden_kernel_spec (fun k => P (fun i => k.wg.bind fun d => d.peers[i]?))
  have hb := bucketHas_kernel_spec (fun k => P (fun i => k.wg.bind fun d => d.peers[i]?))
  noise_vcgen [indexInsert, _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry,
    getDev, getK, branch, invariant, unsupported, recordBudget, budgetExhausted, hh, hb, hm]
  case inv1 => exact ((⇓? _ w => ⌜P (peerAt w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try dsimp [peerAt] at *
  all_goals try simp_all
  all_goals try trivial

theorem keypairCreate_peers_spec (P : (PeerId → Option Peer) → Prop) (pid : PeerId) :
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
  have hk := kdf_kernel_spec PK
  have ho := kdfOut_kernel_spec PK
  mvcgen [deriveKeys, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    invariant, hh, hk, ho]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try dsimp [peerAt] at *
  all_goals simp_all [PK, peerAt, Option.bind_map, Function.comp_def]
  all_goals assumption

theorem indexReplaceHandshake_peers_spec (P : (PeerId → Option Peer) → Prop)
    (pid : PeerId) (kp : KeypairId) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ indexReplaceHandshake pid kp
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  have hm := modifyDev_peers_spec P
  mvcgen [indexReplaceHandshake, indexHashed, getDev, getK, branch, invariant, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [peerAt]

end Leanux.Proofs.WG.Noise
