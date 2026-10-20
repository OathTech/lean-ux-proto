import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionPrimitiveFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionInteriorPacketCuts

/-! Encryption observer continuations retain the original preparation and
key-read snapshots. A resumed preparation does not replace its receipt entry
with the intermediate world. The two original event injections stay exact. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCrypto
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open EncryptionPrimitive

def captureFrom (origin : World) (body : Leanux.M α) : PrefixM E (RunWitness α) :=
  fun w=>ExceptT.mk fun h=>((body.run w).map (fun (value,v)=>(⟨value,origin,v⟩,v)),h)

theorem capture_from_run (origin : World) (body : Leanux.M α) (w : World) (h : List E) :
    runPrefix (captureFrom origin body) w h=
      ((body.run w).map (fun (value,v)=>(⟨value,origin,v⟩,v)),h) := rfl

def afterScatter (receipt : Encryption.Receipt) (failed : Bool) : PrefixM Encryption.Receipt (Option (List UInt8)) := do
  if failed then return none
  emitPrefix receipt
  pure (some receipt.ciphertext)

def afterKey (slot : KeypairId) (packet : DataPacket) (prepared : Encryption.Prepared)
    (preparation : RunWitness (Option Encryption.Prepared)) (keyRead : RunWitness Keypair) :
    PrefixM Encryption.Receipt (Option (List UInt8)) := do
  let failed ← liftPrefix (branch .encSgvecFailed false)
  afterScatter ⟨slot,packet,prepared,preparation,keyRead⟩ failed

def afterPreparation (slot : KeypairId) (packet : DataPacket)
    (preparation : RunWitness (Option Encryption.Prepared)) : PrefixM Encryption.Receipt (Option (List UInt8)) := do
  let some prepared:=preparation.value | return none
  let keyRead ← captureRun (liftWG (getKeypair slot))
  afterKey slot packet prepared preparation keyRead

theorem observe_source (slot : KeypairId) (packet : DataPacket) :
    Encryption.observe Env.checksumHelp slot packet=
      (captureRun (Encryption.prepare Env.checksumHelp packet) >>= afterPreparation slot packet) := rfl

theorem preparation_residual (point : Point (preparationShape packet) w v) :
    runPrefix (Encryption.observe Env.checksumHelp slot packet) w h=
      runPrefix (captureFrom w (remainder point) >>= afterPreparation slot packet) v h := by
  rw [observe_source,runPrefix_bind,runPrefix_bind,runPrefix_captureRun,remainder_run point,capture_from_run]
  cases result : (remainder point).run v <;> rfl

theorem prepared_residual
    (prepared : (Encryption.prepare Env.checksumHelp packet).run w=.ok (value,u)) :
    runPrefix (Encryption.observe Env.checksumHelp slot packet) w h=
      runPrefix (afterPreparation slot packet ⟨value,w,u⟩) u h := by
  rw [observe_source,runPrefix_bind,runPrefix_captureRun,prepared]

theorem key_residual
    (prepared : (Encryption.prepare Env.checksumHelp packet).run w=.ok (some value,u))
    (read : (liftWG (getKeypair slot)).run u=.ok (key,v)) :
    runPrefix (Encryption.observe Env.checksumHelp slot packet) w h=
      runPrefix (afterKey slot packet value ⟨some value,w,u⟩ ⟨key,u,v⟩) v h := by
  rw [prepared_residual prepared]
  simp only [afterPreparation,runPrefix_bind,runPrefix_captureRun,read]

theorem scatter_residual
    (prepared : (Encryption.prepare Env.checksumHelp packet).run w=.ok (some value,u))
    (read : (liftWG (getKeypair slot)).run u=.ok (key,v))
    (checked : (branch .encSgvecFailed false : Leanux.M Bool).run v=.ok (failed,q)) :
    runPrefix (Encryption.observe Env.checksumHelp slot packet) w h=
      runPrefix (afterScatter ⟨slot,packet,value,⟨some value,w,u⟩,⟨key,u,v⟩⟩ failed) q h := by
  rw [key_residual prepared read,afterKey,runPrefix_bind,runPrefix_lift,checked]

def inject (headId : SkbId) (head : RunWitness DataPacket) (skb : SkbId) (read : RunWitness DataPacket)
    (body : PrefixM Encryption.Receipt α) : PrefixM Event α :=
  focusPrefix (Event.old ∘ Journal.Event.encrypted) (fun event=>(old? event).bind Journal.encryption?)
    (focusPrefix (fun receipt=>(⟨headId,head,skb,read,receipt⟩ : WorkerEncryption.Receipt))
      (fun receipt=>some receipt.cipher) body)

theorem crypt_source (headId : SkbId) (head : RunWitness DataPacket) (skb : SkbId) (read : RunWitness DataPacket) :
    EncryptionInterior.crypt headId head skb read=
      inject headId head skb read (Encryption.observe Env.checksumHelp head.value.keypair read.value) := rfl

theorem focus_residual (encode : E → F) (decode : F → Option E)
    (same : ∀events,runPrefix left w events=runPrefix right v events) :
    runPrefix (focusPrefix encode decode left) w h=runPrefix (focusPrefix encode decode right) v h := by
  change ((runPrefix left w _).1,h++((runPrefix left w _).2.drop _).map encode)=
    ((runPrefix right v _).1,h++((runPrefix right v _).2.drop _).map encode)
  rw [same]

theorem inject_residual {read : RunWitness DataPacket}
    (same : ∀events,runPrefix left w events=runPrefix right v events) :
    runPrefix (inject headId head skb read left) w h=runPrefix (inject headId head skb read right) v h := by
  apply focus_residual
  intro events
  exact focus_residual _ _ same

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionCrypto
