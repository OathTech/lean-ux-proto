import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastIngressFrames
import Leanux.Proofs.WG.Queues.TxLiveKeys

/-! Native key/session operations change the separate key frontier while
retaining the packet frontier, allocation epoch and pending encryption aliases.
No key validity, authentication or reference-ownership claim is inferred. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Keys
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition
set_option maxHeartbeats 600000

theorem ready_tx_fields (f : Device → Device) (epoch : ∀ d, (f d).ifindex = d.ifindex)
    (frontier : ∀ d, (f d).nextSkb = d.nextSkb)
    (ring : ∀ d, (f d).encryptQueue = d.encryptQueue) :
    Preserves (Ready past active) (modifyDev f) :=
  ready_frame (LiveFrontier.modify_live f frontier ring) (modify_fields f epoch frontier ring)

macro "encryption_past_key_step" : tactic => `(tactic| first
  | (allocation_release_head hiddenClock64; unfold hiddenClock64)
  | (allocation_release_head modifyDev; exact ready_tx_fields _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  | (allocation_release_head keypairPut; exact ready_frame (LiveFrontier.key_put _ _) (key_put _ _))
  | (allocation_release_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
  | (allocation_release_head generatePublic; exact (generatePublic_sameWGWorld _).wp (Ready _ _))
  | (allocation_release_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (Ready _ _))
  | (allocation_release_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (Ready _ _))
  | (allocation_release_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (Ready _ _))
  | (allocation_release_head messageDecrypt; exact (messageDecrypt_sameWGWorld _ _ _).wp (Ready _ _))
  | (allocation_release_head kdf; exact (Framing.kdf_sameWGWorld _ _ _ _).wp (Ready _ _))
  | (allocation_release_head kdfOut; exact (Framing.kdfOut_sameWGWorld _ _).wp (Ready _ _))
  | maintenance_store_leaf
  | encryption_past_receive_step)

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Keys
