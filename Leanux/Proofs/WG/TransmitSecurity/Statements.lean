import Leanux.Proofs.WG.TransmitSecurity.NonceStagingSafety
import Leanux.Proofs.WG.TransmitSecurity.NonceCreation
import Leanux.Proofs.WG.TransmitSecurity.WireNonce
import Leanux.Proofs.WG.TransmitSecurity.EncryptBinding

/-! Campaign 3, T1 local allocation contracts. Initialized caller coverage and
transport from allocation through every AEAD invocation remain open. -/
namespace Leanux.Proofs.WG.TransmitSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- Security: recording every native staging increment preserves the original
success or Stop exactly; rejected batches cannot be hidden by an observer that
only records successful sends. This is source erasure, not initialized safety. -/
theorem original_staging_nonce_observer (pid : PeerId) :
    ErasesStatePrefix (Nonce.stagingObserved pid) (sendStagedPackets pid) :=
  Nonce.stagingObserved_erases pid

/-- Security: an original nonce increment cannot reuse an allocation already
in the journal, assuming the explicit sending-counter invariant at entry.
The updated invariant and failure-prefix journal are preserved; initialized
caller coverage is a separate obligation. -/
theorem original_nonce_reservation (slot : KeypairId) :
    StatePrefixEnsures (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.reserveObserved slot) (fun _ h w _ => Nonce.Inv (Nonce.view w) h) :=
  Nonce.reserveObserved_safe slot

/-- Security: the nonce observer refers to the actual get/increment operation;
adding its receipt changes neither the native outcome nor either native state. -/
theorem original_nonce_reservation_erases (slot : KeypairId) :
    ErasesStatePrefix (Nonce.reserveObserved slot) (Nonce.reserveNative slot) :=
  Nonce.reserveObserved_erases slot

/-- Security: a complete original staged-send invocation cannot repeat any
recorded nonce allocation under its allocation-stamped sending key, assuming
the explicit entry invariant. Queue refusal and later Stop retain allocations;
caller initialization and allocation-to-AEAD transport are separate obligations. -/
theorem original_staging_nonce_safety (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.stagingObserved pid) :=
  Nonce.stagingObserved_safe pid

/-- Security: native key creation cannot reset the nonce history of an existing
allocation identity. Its fresh global stamp preserves the supplied allocation
invariant even if a device-local slot is reused. This is normal-call preservation. -/
theorem original_creation_nonce_safety (peer : Option PeerId)
    (history : List Nonce.Allocation) :
    Framing.Preserves (fun w => Nonce.Inv (Nonce.view w) history) (keypairCreate peer) :=
  Nonce.create_preserves peer history

/-- Security: the real runner starts with an empty sending-allocation history
and no active key, for either fixture flag. This establishes initialization,
not preservation by all later runner operations. -/
theorem initialized_nonce_projection (net bare : Bool) :
    Nonce.Inv (Nonce.view (Runner.initialWG net bare)) [] := by
  rw [Nonce.initial_view]
  exact Nonce.initial 0

/-- Security: distinct admitted sending counters cannot collide after the
native 64-bit serialization used by AEAD. The actual admission bound is enough;
no unbounded-Nat-to-wire injectivity assumption is used. Packet provenance and
single-use transport to encryption remain separate obligations. -/
theorem original_admitted_nonce_encoding {n m : Nat}
    (hn : n < REJECT_AFTER_MESSAGES) (hm : m < REJECT_AFTER_MESSAGES)
    (same : counterNonce n = counterNonce m) : n = m :=
  admitted_aead_nonce_injective hn hm same

/-- Security: each native encryption invocation records at most one actual
AEAD result with its original packet, preparation and key read; the observer
preserves every success and Stop. This local source coverage does not establish
that the worker selects each admitted packet only once. -/
theorem original_encryption_receipts (slot : KeypairId) (pkt : DataPacket)
    (w : World) (h : List Encryption.Receipt) :
    ErasesPrefix (Encryption.observe Env.checksumHelp slot pkt)
      (encryptPacket Env.checksumHelp slot pkt) ∧
    ∃ suffix, (runPrefix (Encryption.observe Env.checksumHelp slot pkt) w h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix,
        r.slot = slot ∧ r.packet = pkt ∧ r.Valid Env.checksumHelp :=
  ⟨Encryption.observe_erases Env.checksumHelp slot pkt,
    Encryption.observe_receipts Env.checksumHelp slot pkt w h⟩

/-- Security: native encryption uses the entry-resident key in the selected
slot and the packet's assigned nonce for both header and AEAD. Allocation,
checksum and padding preparation cannot substitute a different key. The source
premise is actual encryption success; staging authorization and queue provenance
must still connect that slot and packet to their earlier selection. -/
theorem original_ciphertext_key_binding (slot : KeypairId) (pkt : DataPacket)
    (w v : World) (bytes : List UInt8)
    (success : (encryptPacket Env.checksumHelp slot pkt).run w = .ok (some bytes,v)) :
    ∃ (k : Keypair) (p : Encryption.Prepared), Encryption.keyAt w slot = some k ∧
      bytes = dataMessage k.remoteIndex pkt.nonce k.sending.key
        (p.inner.bytes ++ List.replicate p.padding 0) :=
  Encryption.original_ciphertext_binding slot pkt w v bytes success

end Leanux.Proofs.WG.TransmitSecurity
