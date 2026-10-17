import Leanux.Proofs.WG.Index.OwnerFieldFrames

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Config Std.Do

theorem indexRemove_ownersFresh (kp : KeypairId) (owner : IndexOwner) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ liftIndex (indexRemove owner)
    ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  obtain ⟨d, device, unique, bounded, small, fresh⟩ := pre
  obtain ⟨r, v, next, hr, hd⟩ := indexRemove_exact owner d w ambient device
  rw [run] at hr
  cases hr
  refine ⟨_, hd, remove_owners owner _ unique, ?_, small, ?_⟩
  · intro e member id own
    exact bounded e (List.mem_filter.mp member).1 id own
  · intro e member
    exact fresh e (List.mem_filter.mp member).1

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
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ liftIndex (indexReplaceHandshake pid kp)
    ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  obtain ⟨d, device, unique, bounded, small, fresh⟩ := pre
  obtain ⟨r, v, next, hr, value, hd⟩ := indexReplace_exact pid kp d w ambient device
  rw [run] at hr
  cases hr
  refine ⟨_, hd, ?_⟩
  cases result
  · exact ⟨unique, bounded⟩
  · exact ⟨replace_owners pid kp _ unique fresh, replace_owners_bounded d pid kp bounded small⟩

end Leanux.Proofs.WG.Index
