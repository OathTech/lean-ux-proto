import Leanux.Proofs.WG.Noise.StateEdges
import Leanux.Proofs.WG.Index.Allocation
import Leanux.Proofs.WG.Index.Insert

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Device residency and numeric uniqueness of its index table. -/
def IndicesSafe (w : World) : Prop :=
  ∃ d, w.k.wg = some d ∧ UniqueIndices d.indexTable

theorem setPeer_indices_spec (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  mvcgen [setPeer, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [IndicesSafe]
  all_goals grind

theorem setKeypair_indices_spec (id : KeypairId) (kp : Keypair) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ setKeypair id kp ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  mvcgen [setKeypair, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [IndicesSafe]
  all_goals grind

theorem indexRemove_indices_spec (owner : IndexOwner) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ indexRemove owner ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  obtain ⟨d, device, unique⟩ := pre
  obtain ⟨r, v, hr, hd⟩ := indexRemove_exact owner d w device
  rw [run] at hr
  cases hr
  exact ⟨_, hd, remove_indices owner _ unique⟩

theorem indexInsert_indices_spec (owner : IndexOwner) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ indexInsert owner ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  obtain ⟨d, device, unique⟩ := pre
  obtain ⟨hd, fresh⟩ := indexInsert_exact owner d w result final device run
  refine ⟨_, hd, insert_indices owner result _ unique ?_⟩
  intro e member
  have absent := List.any_eq_false.mp fresh e member
  have different : e.index ≠ result := by simpa using absent
  exact Ne.symm different

theorem indexReplace_indices_spec (pid : PeerId) (kp : KeypairId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ indexReplaceHandshake pid kp ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  obtain ⟨d, device, unique⟩ := pre
  obtain ⟨r, v, hr, value, hd⟩ := indexReplace_exact pid kp d w device
  rw [run] at hr
  cases hr
  refine ⟨_, hd, ?_⟩
  cases result
  · exact unique
  · exact replace_indices pid kp _ unique

theorem keypairCreate_indices_spec (peer : Option PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ keypairCreate peer ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  obtain ⟨d, device, unique⟩ := pre
  have effect := keypairCreate_exact peer d w.k.keypairCounter w result final ⟨device, rfl⟩ run
  cases result with
  | none => exact ⟨d, effect.1, unique⟩
  | some id => exact ⟨_, effect.2.1, unique⟩

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

theorem handshakeZero_indices_spec (pid : PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ handshakeZero pid ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  have hs := setPeer_indices_spec
  mvcgen [handshakeZero, getPeer, getDev, getK, invariant, hs]

theorem deriveKeys_indices_spec (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ deriveKeys kp initiator ck ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  let P := fun k : Kernel => ∃ d, k.wg = some d ∧ UniqueIndices d.indexTable
  have hh := hiddenClock64_kernel_spec P
  have hk := kdf_kernel_spec P
  have ho := kdfOut_kernel_spec P
  have hs := setKeypair_indices_spec
  mvcgen [deriveKeys, getKeypair, getDev, getK, invariant, hh, hk, ho, hs]

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
  have hg := generatePublic_kernel_spec P
  have he := messageEphemeral_kernel_spec P
  have hd := mixDh_kernel_spec P
  have hs := mixPrecomputedDh_kernel_spec P
  have hi := indexInsert_indices_spec
  have hp := setPeer_indices_spec
  noise_vcgen [createInitiation, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, getPeer, getDev, getK,
    branch, invariant, hh, hg, he, hd, hs, hi, hp]

theorem createResponse_indices_spec (pid : PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ createResponse pid ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  let P := fun k : Kernel => ∃ d, k.wg = some d ∧ UniqueIndices d.indexTable
  have hh := hidden_kernel_spec P
  have hg := generatePublic_kernel_spec P
  have he := messageEphemeral_kernel_spec P
  have hd := mixDh_kernel_spec P
  have hk := kdf_kernel_spec P
  have ho := kdfOut_kernel_spec P
  have hi := indexInsert_indices_spec
  have hp := setPeer_indices_spec
  noise_vcgen [createResponse, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, getPeer, getDev, getK,
    branch, invariant, hh, hg, he, hd, hk, ho, hi, hp]

end Leanux.Proofs.WG.Index
