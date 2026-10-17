import Leanux.Proofs.WG.Keypairs.Ordinary
import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.WGHandshake

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing Leanux.Proofs.Framing.Allocation

theorem deriveKeys_sameSnapshot (kp : KeypairId) (initiator : Bool) (chainingKey : List UInt8) :
    SameSnapshot (deriveKeys kp initiator chainingKey) := by
  have saved (f : Keypair → Keypair) (hf : ∀ key, cell (f key) = cell key) :
      SameSnapshot (do let key ← getKeypair kp; setKeypair kp (f key)) := by
    intro initial
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x w' ambient' hp hr
    cases hd : w.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[kp]? with
      | none =>
        simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
        cases hr
      | some key =>
        simp only [StateT.run_bind,
          Leanux.Proofs.WG.CounterWindow.getKeypair_run w ambient d kp key hd hk,
          Leanux.Proofs.WG.CounterWindow.setKeypair_run] at hr
        cases hr
        rw [snapshot_store w d kp (f key) hd, hf,
          put_existing _ _ _ (snapshot_lookup w d kp key hd hk)]
        exact hp
  unfold deriveKeys
  apply SameView.bind (fun initial => hoare_liftAmbient
    (AmbientM.hiddenClock64 .deriveKeysBirthdate) (fun w => snapshot w = initial))
  intro birthdate
  apply SameView.bind ((kdf_sameWGWorld true false chainingKey []).factor snapshot)
  intro outs
  apply SameView.bind ((kdfOut_sameWGWorld outs 0).factor snapshot)
  intro first
  apply SameView.bind ((kdfOut_sameWGWorld outs 1).factor snapshot)
  intro second
  apply saved
  intro key
  cases initiator <;> rfl

theorem getKeypair_snapshot_wp (i : Nat) (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ getKeypair i
    ⦃⇓? k w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some (cell k)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient key w' ambient' hp hr
  cases hd : w.dev with
  | none =>
    simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hk : d.keypairs[i]? with
    | none =>
      simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      cases hr
    | some value =>
      rw [Leanux.Proofs.WG.CounterWindow.getKeypair_run w ambient d i value hd hk] at hr
      cases hr
      exact ⟨hp, snapshot_lookup w d i key hd hk⟩

theorem setKeypair_snapshot_wp (i : Nat) (k : Keypair) (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some (cell k)⌝⦄ setKeypair i k
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hd : w.dev with
  | none => simp [snapshot, hd] at hp
  | some d =>
    have hs : ((setKeypair i k).run w).run ambient =
        .ok (((), Leanux.Proofs.WG.CounterWindow.store w i k), ambient) := rfl
    rw [hs] at hr
    cases hr
    rw [snapshot_store w d i k hd, put_existing _ _ _ hp.2]
    exact hp.1

theorem decryptPacket_sameSnapshot (pkt : RxPacket) : SameSnapshot (decryptPacket pkt) := by
  have ambient {α : Type} (a : AmbientM α) : SameSnapshot (StateT.lift a) :=
    fun initial => hoare_liftAmbient a (fun w => snapshot w = initial)
  have read (i : Nat) : SameSnapshot (getKeypair i) := by
    intro initial
    exact hoare_consequence (getKeypair_snapshot_wp i (fun s => s = initial))
      (fun _ h => h) (fun _ _ h => h.1)
  have either (a b : WG.M Bool) (ha : SameSnapshot a) (hb : SameSnapshot b) :
      SameSnapshot (WG.orM a b) := by
    unfold WG.orM
    apply SameView.bind ha
    intro x
    cases x
    · exact hb
    · exact SameView.pure _ true
  have invalidate : SameSnapshot (do
      let key ← getKeypair pkt.keypair
      setKeypair pkt.keypair {key with receiving := {key.receiving with isValid := false}}
      pure (none : Option RxPacket)) := by
    intro initial
    apply hoare_bind _ _ (getKeypair_snapshot_wp pkt.keypair (fun s => s = initial))
    intro key
    apply hoare_bind _ _ (setKeypair_snapshot_wp pkt.keypair
      {key with receiving := {key.receiving with isValid := false}} (fun s => s = initial))
    intro _
    exact preserves_pure none
  unfold decryptPacket
  apply SameView.bind (ambient (AmbientM.branch .decNoKeypair false))
  intro missing
  cases missing with
  | true => exact SameView.pure _ none
  | false =>
    apply SameView.bind (read pkt.keypair)
    intro key
    apply SameView.bind (either _ _
      (ambient (AmbientM.branch .decKeyInvalid (!key.receiving.isValid)))
      (either _ _ ((branchExpired_sameWGWorld .decKeyExpired key.receiving.birthdate
        REJECT_AFTER_TIME).factor snapshot)
        (ambient (AmbientM.branchCmp .decCounterLimit
          (key.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES)
          key.receivingCounter.counter REJECT_AFTER_MESSAGES))))
    intro rejected
    cases rejected with
    | true => exact invalidate
    | false =>
      apply SameView.bind (ambient (AmbientM.hiddenAlloc .skbCowDataRx))
      intro cow
      apply SameView.bind (either _ _
        (ambient (AmbientM.branch .decCowDataFailed (!cow)))
        (ambient (AmbientM.branch .decTooManyFrags false)))
      intro failed
      cases failed with
      | true => exact SameView.pure _ none
      | false =>
        apply SameView.bind (ambient (AmbientM.branch .decSgvecFailed false))
        intro sg
        cases sg with
        | true => exact SameView.pure _ none
        | false =>
          apply SameView.bind (ambient (AmbientM.branch .decDecryptFailed _))
          intro failed
          cases failed with
          | true => exact SameView.pure _ none
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            split
            · apply SameView.bind (ambient (AmbientM.branch .decTrimFailed false))
              intro trimmed
              cases trimmed <;> exact SameView.pure _ _
            · exact ambient (AmbientM.invariant "unreachable")

end Leanux.Proofs.WG.Keypairs
