import Leanux.Proofs.WG.Index.IndexOperationFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem keypairPut_indices_spec (kp : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ keypairPut kp now ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  have hr := indexRemove_indices_spec
  have hs := setKeypair_indices_spec
  mvcgen [keypairPut, IndexOwner.peerDeref, IndexOwner.peerWord, getKeypair, getDev,
    getK, refcountDecAndTest, branch, branchCmp, invariant, unsupported,
    modifyDev, modifyK, hr, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [IndicesSafe]
  all_goals grind

theorem addNewKeypair_indices_spec (pid : PeerId) (newKey : KeypairId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ addNewKeypair pid newKey ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  have hp := keypairPut_indices_spec
  have hs := setPeer_indices_spec
  noise_vcgen [addNewKeypair, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
    getPeer, getKeypair, getDev, getK, branch, invariant, hp, hs]

theorem beginSession_indices_spec (pid : PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ beginSession pid ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  have hc := keypairCreate_indices_spec
  have hs := setKeypair_indices_spec
  have hd := deriveKeys_indices_spec
  have hz := handshakeZero_indices_spec
  have ha := addNewKeypair_indices_spec
  have hr := indexReplace_indices_spec
  mvcgen [beginSession, IndexOwner.peerWord, IndexOwner.peerDeref, Leanux.WG.andM,
    getPeer, getDev, getK, getKeypair, branch, invariant, unsupported, hc, hs, hd, hz, ha, hr]

theorem createInitiation_indices_spec (pid : PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ createInitiation pid ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  let P := fun k : Kernel => ∃ d, k.wg = some d ∧ UniqueIndices d.indexTable
  have hh := hidden_kernel_spec P
  have hg := generatePublic_wg_spec P
  have he := messageEphemeral_wg_spec P
  have hd := mixDh_wg_spec P
  have hs := mixPrecomputedDh_wg_spec P
  have hi := indexInsert_indices_spec
  have hp := setPeer_indices_spec
  noise_vcgen [createInitiation, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, getPeer, getDev, getK,
    branch, invariant, hh, hg, he, hd, hs, hi, hp]

theorem createResponse_indices_spec (pid : PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ createResponse pid ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  let P := fun k : Kernel => ∃ d, k.wg = some d ∧ UniqueIndices d.indexTable
  have hh := hidden_kernel_spec P
  have hg := generatePublic_wg_spec P
  have he := messageEphemeral_wg_spec P
  have hd := mixDh_wg_spec P
  have hk := kdf_wg_spec P
  have ho := kdfOut_wg_spec P
  have hi := indexInsert_indices_spec
  have hp := setPeer_indices_spec
  noise_vcgen [createResponse, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, getPeer, getDev, getK,
    branch, invariant, hh, hg, he, hd, hk, ho, hi, hp]

end Leanux.Proofs.WG.Index
