import Leanux.Proofs.WG.Noise.StateEdges
import Leanux.Proofs.WG.Index.Allocation
import Leanux.Proofs.WG.Index.Insert

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Device residency and numeric uniqueness of its index table. -/
def IndicesSafe (w : WGWorld) : Prop :=
  ∃ d, w.dev = some d ∧ UniqueIndices d.indexTable

theorem setPeer_indices_spec (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨d, device, unique⟩ := pre
  simp [setPeer, modifyDev, device] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨_, rfl, unique⟩

theorem setKeypair_indices_spec (id : KeypairId) (kp : Keypair) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ setKeypair id kp ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨d, device, unique⟩ := pre
  simp [setKeypair, modifyDev, device] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨_, rfl, unique⟩

theorem handshakeZero_indices_spec (pid : PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ handshakeZero pid ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold handshakeZero
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid IndicesSafe)) ?_
  intro p g ambient result final after pre run
  exact (ensures_iff _ _ _).mpr (setPeer_indices_spec pid _) g ambient result final after pre.1 run

theorem deriveKeys_indices_spec (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ deriveKeys kp initiator ck ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  let Q : WGWorld → Prop := IndicesSafe
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
          exact (ensures_iff _ _ _).mpr (setKeypair_indices_spec kp _)


theorem keypairCreate_indices_spec (peer : Option PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ keypairCreate peer ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  obtain ⟨d, device, unique⟩ := pre
  have effect := keypairCreate_exact peer d w.keypairCounter w ambient result final after ⟨device, rfl⟩ run
  cases result with
  | none => exact ⟨d, effect.1, unique⟩
  | some id => exact ⟨_, effect.2.1, unique⟩

end Leanux.Proofs.WG.Index
