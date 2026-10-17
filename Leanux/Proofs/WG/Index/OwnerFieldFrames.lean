import Leanux.Proofs.WG.Index.IndexFieldFrames

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Config Std.Do

/-- Owner uniqueness and allocation bounds, with a designated unhashed identity.
This predicate does not assert keypair-store residency or slot safety. -/
def OwnersFresh (kp : KeypairId) (w : WGWorld) : Prop :=
  ∃ d, w.dev = some d ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d ∧
    kp < d.nextKeypairId ∧ ∀ e ∈ d.indexTable, e.owner ≠ .keypair kp

def OwnersSafe (w : WGWorld) : Prop :=
  ∃ d, w.dev = some d ∧ UniqueOwners d.indexTable

def OwnersBoundedSafe (w : WGWorld) : Prop :=
  ∃ d, w.dev = some d ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d

theorem setPeer_ownersFresh (kp : KeypairId) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨d, device, unique, bounded, small, fresh⟩ := pre
  simp [setPeer, modifyDev, device] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨_, rfl, unique, bounded, small, fresh⟩

theorem setKeypair_ownersFresh (kp id : KeypairId) (k : Keypair) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ setKeypair id k ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨d, device, unique, bounded, small, fresh⟩ := pre
  simp [setKeypair, modifyDev, device] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨_, rfl, unique, bounded, small, fresh⟩

theorem handshakeZero_ownersFresh (kp : KeypairId) (pid : PeerId) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ handshakeZero pid ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold handshakeZero
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid (OwnersFresh kp))) ?_
  intro p g ambient result final after pre run
  exact (ensures_iff _ _ _).mpr (setPeer_ownersFresh kp pid _)
    g ambient result final after pre.1 run

theorem deriveKeys_ownersFresh (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ deriveKeys kp initiator ck ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  let Q : WGWorld → Prop := OwnersFresh kp
  have hread : Ensures (getKeypair kp) Q (fun _ => Q) := by
    intro g ambient k g' ambient' hp hr
    cases hd : g.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[kp]? with
      | none =>
        simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
        cases hr
      | some k =>
        simp [getKeypair, getDev, hd, hk] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hp
  apply (ensures_iff _ _ _).mp
  unfold deriveKeys
  refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
  · exact (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .deriveKeysBirthdate) Q)
  · intro birthdate
    refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (kdf_wg_spec Q true false ck [])
    · intro outs
      refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
      · exact (ensures_iff _ _ _).mpr (kdfOut_wg_spec Q outs 0)
      · intro first
        refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
        · exact (ensures_iff _ _ _).mpr (kdfOut_wg_spec Q outs 1)
        · intro second
          refine ensures_bind (Q := fun _ => Q) _ _ hread ?_
          intro key
          exact (ensures_iff _ _ _).mpr (setKeypair_ownersFresh kp kp _)

theorem setPeer_ownersBounded (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜OwnersBoundedSafe w⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨d, device, unique, bounded⟩ := pre
  simp [setPeer, modifyDev, device] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨_, rfl, unique, bounded⟩

end Leanux.Proofs.WG.Index
