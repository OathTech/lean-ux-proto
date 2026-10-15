import Leanux.Proofs.WG.Index.SessionOwners

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem indexInsert_handshake_ownersBounded (pid : PeerId) :
    ⦃fun w => ⌜OwnersBoundedSafe w⌝⦄ indexInsert (.handshake pid) ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  obtain ⟨d, device, unique, bounded⟩ := pre
  obtain ⟨hd, fresh⟩ := indexInsert_exact (.handshake pid) d w result final device run
  refine ⟨_, hd, insert_owners (.handshake pid) result _ unique, ?_⟩
  intro e member id own
  simp only [List.mem_cons] at member
  rcases member with same | member
  · subst e
    cases own
  · exact bounded e (List.mem_filter.mp member).1 id own

theorem createInitiation_owners_spec (pid : PeerId) :
    ⦃fun w => ⌜OwnersBoundedSafe w⌝⦄ createInitiation pid ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  let P := fun k : Kernel => ∃ d, k.wg = some d ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d
  have hh := hidden_kernel_spec P
  have hg := generatePublic_kernel_spec P
  have he := messageEphemeral_kernel_spec P
  have hd := mixDh_kernel_spec P
  have hs := mixPrecomputedDh_kernel_spec P
  have hi := indexInsert_handshake_ownersBounded
  have hp := setPeer_ownersBounded
  noise_vcgen [createInitiation, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, getPeer, getDev, getK,
    branch, invariant, hh, hg, he, hd, hs, hi, hp]

theorem createResponse_owners_spec (pid : PeerId) :
    ⦃fun w => ⌜OwnersBoundedSafe w⌝⦄ createResponse pid ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  let P := fun k : Kernel => ∃ d, k.wg = some d ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d
  have hh := hidden_kernel_spec P
  have hg := generatePublic_kernel_spec P
  have he := messageEphemeral_kernel_spec P
  have hd := mixDh_kernel_spec P
  have hk := kdf_kernel_spec P
  have ho := kdfOut_kernel_spec P
  have hi := indexInsert_handshake_ownersBounded
  have hp := setPeer_ownersBounded
  noise_vcgen [createResponse, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, getPeer, getDev, getK,
    branch, invariant, hh, hg, he, hd, hk, ho, hi, hp]

end Leanux.Proofs.WG.Index
