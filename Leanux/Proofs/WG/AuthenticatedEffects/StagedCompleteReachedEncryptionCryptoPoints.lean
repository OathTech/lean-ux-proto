import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionCryptoFrames

/-! Actual encryption primitive cuts keep the incoming journal until the
AEAD receipt. The fixed preparation tree supplies its interior prefixes;
the key and scatter witnesses are literal native source runs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCrypto
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal CompleteCarrier

inductive Point (headId : SkbId) (head : RunWitness DataPacket) (skb : SkbId)
    (read : RunWitness DataPacket) (w : World) (h : List Event) : World → List Event → Prop where
  | preparation (point : EncryptionPrimitive.Point (EncryptionPrimitive.preparationShape read.value) w v) :
      Point headId head skb read w h v h
  | key (prepared : (Encryption.prepare Env.checksumHelp read.value).run w=.ok (some value,u))
      (keyRead : (liftWG (getKeypair head.value.keypair)).run u=.ok (key,v)) : Point headId head skb read w h v h
  | scatter (prepared : (Encryption.prepare Env.checksumHelp read.value).run w=.ok (some value,u))
      (keyRead : (liftWG (getKeypair head.value.keypair)).run u=.ok (key,v))
      (checked : (branch .encSgvecFailed false : Leanux.M Bool).run v=.ok (failed,q)) :
      Point headId head skb read w h q h
  | returned (performed : runPrefix (EncryptionInterior.crypt headId head skb read) w h=
      (.ok (value,v),last)) : Point headId head skb read w h v last

variable {head read : RunWitness DataPacket}

/-- The actual preparation, key-read and scatter cuts conserve the original
packet ledger before any AEAD receipt, as does the receipt's normal return. -/
theorem Point.accounted (point : Point headId head skb read w h v last)
    (before : Accounted h ledger debts locals w.wg) : Accounted last ledger debts locals v.wg := by
  cases point with
  | preparation point=>rw [point.same_wg];exact before
  | key prepared keyRead=>rw [key_same prepared keyRead];exact before
  | scatter prepared keyRead checked=>rw [scatter_same prepared keyRead checked];exact before
  | returned performed=>exact EncryptionInterior.crypt_accounted before performed

theorem Point.residual (point : Point headId head skb read w h v last) :
    ∃remaining,runPrefix (EncryptionInterior.crypt headId head skb read) w h=runPrefix remaining v last := by
  cases point with
  | preparation point=>
    refine ⟨inject headId head skb read
      (captureFrom w (EncryptionPrimitive.remainder point) >>= afterPreparation head.value.keypair read.value),?_⟩
    rw [crypt_source]
    exact inject_residual (fun _=>preparation_residual point)
  | key prepared keyRead=>
    rw [crypt_source]
    exact ⟨_,inject_residual (fun _=>key_residual prepared keyRead)⟩
  | scatter prepared keyRead checked=>
    rw [crypt_source]
    exact ⟨_,inject_residual (fun _=>scatter_residual prepared keyRead checked)⟩
  | returned performed=>exact ⟨pure _,performed⟩

noncomputable def remainder (point : Point headId head skb read w h v last) : PrefixM Event (Option (List UInt8)) :=
  Classical.choose point.residual

theorem remainder_run (point : Point headId head skb read w h v last) :
    runPrefix (EncryptionInterior.crypt headId head skb read) w h=runPrefix (remainder point) v last :=
  Classical.choose_spec point.residual

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCrypto
