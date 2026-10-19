import Leanux.Proofs.WG.HandshakeSecurity.InitializedEncryptionMaterial

/-! The actual native ciphertext layout uses the same assigned counter for
the data header and AEAD input. Bounded serialization preserves uniqueness. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.EncryptionMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
variable {h : List Journal.Event} {r : WorkerEncryption.Receipt}

def wireToken (r : WorkerEncryption.Receipt) : Nat × List UInt8 :=
  (r.cipher.keyRead.value.internalId,counterNonce r.cipher.packet.nonce)

theorem wire_unique (unique : ((h.filterMap Journal.encryption?).map token).Nodup)
    (bounds : ∀ r ∈ h.filterMap Journal.encryption?, r.cipher.packet.nonce < REJECT_AFTER_MESSAGES) :
    ((h.filterMap Journal.encryption?).map wireToken).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_map.mpr
  have unequal := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp unique)
  apply unequal.imp_of_mem
  intro r s first second different same
  apply different
  apply Nonce.Allocation.ext
  · exact congrArg Prod.fst same
  · exact admitted_aead_nonce_injective (bounds r first) (bounds s second) (congrArg Prod.snd same)

def Encoding (r : WorkerEncryption.Receipt) : Prop :=
  r.cipher.packet = r.read.value ∧
  r.cipher.ciphertext =
    le32 MESSAGE_DATA_TYPE ++ le32 r.cipher.keyRead.value.remoteIndex ++ le64 r.read.value.nonce ++
      aeadEncrypt r.cipher.keyRead.value.sending.key (counterNonce r.read.value.nonce)
        (r.cipher.prepared.inner.bytes ++ List.replicate r.cipher.prepared.padding 0) []

theorem encoding (valid : r.Valid) : Encoding r := by
  refine ⟨valid.2.2.2.1,?_⟩
  simp only [Encryption.Receipt.ciphertext,dataMessage,valid.2.2.2.1]

/-- All reservation tokens remain nonrepeating even for failed/abandoned work;
actual AEAD wire nonces are nonrepeating per allocation and use the packet's
assigned header counter. All clauses share the initialized final journal. -/
theorem final_encoding (trace : Runner.Trace) (placeholders : Bool) :
    let h := ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2).filterMap
      AuthenticatedEffects.CausalJournal.old?
    (h.filterMap Journal.nonce?).Nodup ∧
      ((h.filterMap Journal.encryption?).map wireToken).Nodup ∧
      ∀ r ∈ h.filterMap Journal.encryption?, Encoding r := by
  have core := final_initialized trace placeholders
  have history := congrArg Prod.snd (AuthenticatedEffects.CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  refine ⟨?_,wire_unique core.2.1 core.2.2,fun r member => encoding (core.1 r member).1⟩
  rw [←history]
  exact Journal.initialized_reservations trace placeholders

end Leanux.Proofs.WG.HandshakeSecurity.EncryptionMaterial
