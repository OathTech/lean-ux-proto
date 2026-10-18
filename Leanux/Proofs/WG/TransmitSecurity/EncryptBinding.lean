import Leanux.Proofs.WG.TransmitSecurity.EncryptReceipts
import Leanux.Proofs.WG.TransmitSecurity.EncryptFrames

/-! The concrete encryption callback reads the same key allocation that was
resident at entry; preparation cannot swap it before the AEAD. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Encryption
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes

def keyAt (w : World) (slot : KeypairId) : Option Keypair :=
  w.wg.dev.bind fun d => d.keypairs[slot]?

theorem read_resident (slot : KeypairId) (r : RunWitness Keypair)
    (valid : r.Valid (liftWG (getKeypair slot))) : keyAt r.before slot = some r.value := by
  change (liftWG (getKeypair slot)).run r.before = .ok (r.value,r.after) at valid
  rw [liftWG_run] at valid
  cases actual : ((getKeypair slot).run r.before.wg).run r.before.ambient with
  | error stop => simp [actual,Except.map] at valid
  | ok out =>
    rcases out with ⟨⟨k,v⟩,b⟩
    simp only [actual,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
    obtain ⟨same,_⟩ := valid
    obtain ⟨_,_,d,device,found⟩ := KeyTimes.getKeypair_return slot r.before.wg v k r.before.ambient b actual
    simp [keyAt,device,found,same]

theorem Receipt.entry_key (r : Receipt) (valid : r.Valid Env.checksumHelp) :
    keyAt r.preparation.before r.slot = some r.keyRead.value := by
  have resident := read_resident r.slot r.keyRead valid.2.2.2
  have frame := (ProjectedAction.iff_run _ _ _).mp (prepare_keys r.packet)
    r.preparation.before r.preparation.value r.preparation.after valid.1
  have same := congrArg (fun s : Option (Std.TreeMap KeypairId Keypair) =>
    s.bind fun keys => keys[r.slot]?) frame
  have lookup : keyAt r.preparation.after r.slot = keyAt r.preparation.before r.slot := by
    simpa only [productKeys,keys,keyAt,Option.bind_map,Function.comp_def] using same
  rw [← lookup,valid.2.2.1]
  exact resident

theorem original_ciphertext_binding (slot : KeypairId) (pkt : DataPacket)
    (w v : World) (bytes : List UInt8)
    (success : (encryptPacket Env.checksumHelp slot pkt).run w = .ok (some bytes,v)) :
    ∃ (k : Keypair) (p : Prepared), keyAt w slot = some k ∧
      bytes = dataMessage k.remoteIndex pkt.nonce k.sending.key
        (p.inner.bytes ++ List.replicate p.padding 0) := by
  obtain ⟨r,_,slotEq,packetEq,valid,start,bytesEq⟩ :=
    original_success_receipt Env.checksumHelp slot pkt w v bytes [] success
  refine ⟨r.keyRead.value,r.prepared,?_,?_⟩
  · simpa only [start,slotEq] using r.entry_key valid
  · simpa only [Receipt.ciphertext,packetEq] using bytesEq.symm

end Leanux.Proofs.WG.TransmitSecurity.Encryption
