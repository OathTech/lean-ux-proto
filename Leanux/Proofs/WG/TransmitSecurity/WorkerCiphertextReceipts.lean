import Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption
import Leanux.Proofs.WG.TransmitSecurity.PacketPayloadFrames

/-! Successful worker encryption returns the ciphertext of its actual newly
appended receipt. This ties the subsequent byte write to this journal position. -/
namespace Leanux.Proofs.WG.TransmitSecurity.WorkerCiphertext
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open WorkerEncryption

theorem crypt_success (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (read : RunWitness DataPacket) (w v : World) (history : List WorkerEncryption.Receipt)
    (bytes : List UInt8)
    (run : (runPrefix (WorkerEncryption.crypt headId head id read) w history).1 = .ok (some bytes,v)) :
    ∃ cipher, runPrefix (WorkerEncryption.crypt headId head id read) w history =
      (.ok (some bytes,v),history ++ [⟨headId,head,id,read,cipher⟩]) ∧
      cipher.slot = head.value.keypair ∧ cipher.packet = read.value ∧
      cipher.Valid Env.checksumHelp ∧ cipher.preparation.before = w ∧ cipher.ciphertext = bytes := by
  have native := (WorkerEncryption.crypt_erases headId head id read w history).symm.trans run
  obtain ⟨cipher,source,slot,packet,valid,start,output⟩ := Encryption.original_success_receipt
    Env.checksumHelp head.value.keypair read.value w v bytes
    (history.filterMap (fun r => some r.cipher)) native
  have observed := focusPrefix_suffix (fun r => (⟨headId,head,id,read,r⟩ : WorkerEncryption.Receipt))
    (fun r => some r.cipher) _ w history _ [cipher] source
  exact ⟨cipher,observed,slot,packet,valid,start,output⟩

end Leanux.Proofs.WG.TransmitSecurity.WorkerCiphertext
