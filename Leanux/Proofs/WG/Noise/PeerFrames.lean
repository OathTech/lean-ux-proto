import Leanux.Proofs.WG.Noise.Slots
import Leanux.Proofs.WG.Noise.CryptoFrames
import Leanux.Proofs.WG.Index.Collision

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem bucketHas_index_spec (P : List IndexEntry → Prop) (walk collide : Decision) (index : Nat) :
    ⦃fun table => ⌜P table⌝⦄
      (noise_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas) walk collide index
    ⦃⇓? _ table => ⌜P table⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro table ambient result table' ambient' hp hr
  obtain ⟨found, final, after, run, _, same⟩ :=
    Index.bucketWalk_returns walk collide index (Index.bucket index table)
      table table ambient rfl
  have exactRun : (((Index.bucketHas walk collide index).run table).run ambient) =
      .ok ((found, final), after) := by
    rw [Index.bucketHas_source]
    simpa [indexBucket, Index.bucket, StateT.run_bind] using run
  rw [exactRun] at hr
  cases hr
  exact same ▸ hp

theorem keypairCreate_peers_spec (P : (PeerId → Option Peer) → Prop) (pid : Option PeerId) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ keypairCreate pid
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  let Q : WGWorld → Prop := fun g => P (peerAt g)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) Q (fun _ => Q) := by
    intro g ambient y g' ambient' hp hr
    cases hr
    exact hp
  have hget : Ensures (get : WG.M WGWorld) Q (fun _ => Q) := by
    intro g ambient y g' ambient' hp hr
    cases hr
    exact hp
  have hcounter (n : Nat) :
      Ensures (modify (fun g : WGWorld => {g with keypairCounter := n}) : WG.M Unit)
        Q (fun _ => Q) := by
    intro g ambient y g' ambient' hp hr
    cases hr
    exact hp
  have hdev : Ensures getDev Q (fun _ => Q) := by
    intro g ambient d g' ambient' hp hr
    cases hd : g.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      simp [getDev, hd] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hp
  apply (ensures_iff _ _ _).mp
  unfold keypairCreate
  refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
  · exact (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.hiddenAlloc .kzallocKeypair) Q)
  · intro ok
    refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr
        (hoare_liftAmbient_variant (AmbientM.branch .keypairCreateNoMem !ok) Q)
    · intro noMemory
      cases noMemory with
      | true => exact hpure none
      | false =>
        refine ensures_bind (Q := fun _ => Q) _ _ hget ?_
        intro state
        refine ensures_bind (Q := fun _ => Q) _ _ (hcounter _) ?_
        intro _
        refine ensures_bind (Q := fun _ => Q) _ _ hdev ?_
        intro device
        refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
        · exact (ensures_iff _ _ _).mpr (modifyDev_peers_spec P _ (fun _ => rfl))
        · intro _
          refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
          · exact (ensures_iff _ _ _).mpr (modifyDev_peers_spec P _ (fun _ => rfl))
          · intro _
            exact hpure _

theorem deriveKeys_peers_spec (P : (PeerId → Option Peer) → Prop)
    (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    ⦃fun w => ⌜P (peerAt w)⌝⦄ deriveKeys kp initiator ck
    ⦃⇓? _ w => ⌜P (peerAt w)⌝⦄ := by
  let Q : WGWorld → Prop := fun g => P (peerAt g)
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
          exact (ensures_iff _ _ _).mpr (modifyDev_peers_spec P _ (fun _ => rfl))

end Leanux.Proofs.WG.Noise
