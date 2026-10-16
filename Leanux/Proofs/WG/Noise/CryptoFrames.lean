import Leanux.Proofs.WG.Noise.ComponentFrames

/-! Crypto helper preservation within WireGuard. These helpers still have
type WG.M, so preserving the native WireGuard state is a substantive claim.
Ambient execution, including its decision trace, remains unrestricted. -/
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem kdf_wg_spec (P : WGWorld → Prop) (second third : Bool) (ck data : List UInt8) :
    ⦃fun w => ⌜P w⌝⦄ kdf second third ck data ⦃⇓? _ w => ⌜P w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient x w' ambient' hp hr
  cases second <;> cases third <;>
    simp [kdf, Leanux.WG.orM, branch, AmbientM.branch, StateT.run] at hr
  all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact hp


theorem kdfOut_wg_spec (P : WGWorld → Prop) (outs : List (List UInt8)) (i : Nat) :
    ⦃fun w => ⌜P w⌝⦄ kdfOut outs i ⦃⇓? _ w => ⌜P w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient x w' ambient' hp hr
  cases hi : outs[i]? with
  | none =>
    simp [kdfOut, hi, invariant, AmbientM.invariant, StateT.run] at hr
    cases hr
  | some o =>
    simp [kdfOut, hi, StateT.run] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact hp

theorem messageEphemeral_wg_spec (P : WGWorld → Prop) (copy : Bool)
    (e ck hash : List UInt8) :
    ⦃fun w => ⌜P w⌝⦄ messageEphemeral copy e ck hash ⦃⇓? _ w => ⌜P w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold messageEphemeral
  refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
  · exact (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.branch .msgEphemeralCopy copy) P)
  · intro _
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (kdf_wg_spec P false false ck e)
    · intro outs
      refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
      · exact (ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 0)
      · intro _
        intro w ambient x w' ambient' hp hr
        cases hr
        exact hp

theorem mixDh_wg_spec (P : WGWorld → Prop) (key : Bool)
    (ck priv pub : List UInt8) :
    ⦃fun w => ⌜P w⌝⦄ mixDh key ck priv pub ⦃⇓? _ w => ⌜P w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  dsimp only [mixDh]
  refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
  · exact (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.branch .mixDhNull !(curve25519 priv pub).2) P)
  · intro b
    cases b with
    | true =>
      intro w ambient x w' ambient' hp hr
      cases hr
      exact hp
    | false =>
      refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
      · exact (ensures_iff _ _ _).mpr (kdf_wg_spec P key false ck (curve25519 priv pub).1)
      · intro outs
        refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
        · exact (ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 0)
        · intro first
          cases key with
          | false =>
            intro w ambient x w' ambient' hp hr
            cases hr
            exact hp
          | true =>
            refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
            · exact (ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 1)
            · intro _
              intro w ambient x w' ambient' hp hr
              cases hr
              exact hp

theorem mixPrecomputedDh_wg_spec (P : WGWorld → Prop) (ck precomputed : List UInt8) :
    ⦃fun w => ⌜P w⌝⦄ mixPrecomputedDh ck precomputed ⦃⇓? _ w => ⌜P w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold mixPrecomputedDh
  refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
  · exact (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.branch .mixPrecomputedNull
        (precomputed == (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.zeroKey))) P)
  · intro b
    cases b with
    | true =>
      intro w ambient x w' ambient' hp hr
      cases hr
      exact hp
    | false =>
      refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
      · exact (ensures_iff _ _ _).mpr (kdf_wg_spec P true false ck precomputed)
      · intro outs
        refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
        · exact (ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 0)
        · intro _
          refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
          · exact (ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 1)
          · intro _
            intro w ambient x w' ambient' hp hr
            cases hr
            exact hp

theorem messageDecrypt_wg_spec (P : WGWorld → Prop) (sealed key hash : List UInt8) :
    ⦃fun w => ⌜P w⌝⦄ messageDecrypt sealed key hash ⦃⇓? _ w => ⌜P w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient x w' ambient' hp hr
  cases hplain : aeadDecrypt key noiseNonce sealed hash <;>
    simp [messageDecrypt, hplain, branch, AmbientM.branch, StateT.run] at hr
  all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact hp

theorem generatePublic_wg_spec (P : WGWorld → Prop) (secret : Key) :
    ⦃fun w => ⌜P w⌝⦄ generatePublic secret ⦃⇓? _ w => ⌜P w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient x w' ambient' hp hr
  cases hs : secret == nullPoint <;>
    simp [generatePublic, hs, branch, AmbientM.branch, StateT.run] at hr
  all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact hp

end Leanux.Proofs.WG.Noise
