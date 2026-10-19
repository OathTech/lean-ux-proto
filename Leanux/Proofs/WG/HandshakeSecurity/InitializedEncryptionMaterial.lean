import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialFinal
import Leanux.Proofs.WG.HandshakeSecurity.StagingMaterialBank
import Leanux.Proofs.WG.TransmitSecurity.BatchJournalFinal
import Leanux.Proofs.WG.TransmitSecurity.ReservationEncryption

/-! Initialized AEAD material is linked to the one canonical reservation bank.
The actual native key allocation and AEAD nonce, rather than numeric slots,
identify the pair whose reuse is excluded. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.EncryptionMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity Responder ReservationAssignments

def token (r : WorkerEncryption.Receipt) : Nonce.Allocation :=
  ⟨r.cipher.keyRead.value.internalId,r.cipher.packet.nonce⟩

def Bindings (h : List Journal.Event) : Prop :=
  ∀ r ∈ h.filterMap Journal.encryption?, r.Valid ∧ ResidentMaterial.BoundReceipt h r ∧
    Bank.Assigned (StagingMaterial.bank h) h r (token r)

theorem bindings (material : ResidentMaterial.Safe h) (batch : BatchJournal.Safe h)
    (bank : StagingMaterial.Safe h) : Bindings h := by
  intro r member
  obtain ⟨valid,binding⟩ := material.worker r member
  have bound := binding (batch r member).2.2
  obtain ⟨assignedToken,assigned,stamp,nonce⟩ := StagingMaterial.assigned_of_binding bank bound
  refine ⟨valid,bound,?_⟩
  have equal : assignedToken = token r := by
    apply Nonce.Allocation.ext
    · exact stamp
    · exact nonce.trans (congrArg DataPacket.nonce valid.2.2.2.1).symm
  exact equal ▸ assigned

theorem unique (bound : Bindings h)
    (exclusive : Bank.Exclusive (StagingMaterial.bank h) h) :
    ((h.filterMap Journal.encryption?).map token).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_map.mpr
  apply exclusive.2.imp_of_mem
  intro r s first second unequal same
  exact unequal (token r) (bound r first).2.2 (same ▸ (bound s second).2.2)

theorem bounded (material : ResidentMaterial.Safe h) (origins : PacketOrigins.Safe h)
    (reservations : ReservationHistory.Safe h) :
    ∀ r ∈ h.filterMap Journal.encryption?, r.cipher.packet.nonce < REJECT_AFTER_MESSAGES := by
  intro r member
  obtain ⟨valid,_⟩ := material.worker r member
  obtain ⟨generation,_,certificate⟩ := (origins.worker r member).2
  have bound := (reservations.packet certificate).1
  have readBound : r.read.value.nonce < REJECT_AFTER_MESSAGES := by
    simpa only [PacketMaterial.material] using bound
  exact (congrArg DataPacket.nonce valid.2.2.2.1).symm ▸ readBound

/-- Native initialized material, batch selection and the canonical reservation
bank refer to the same exact journal history; no incoming invariant remains. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    let h := (runPrefixOuter (Journal.execute trace placeholders) []).2
    Bindings h ∧ ((h.filterMap Journal.encryption?).map token).Nodup ∧
      ∀ r ∈ h.filterMap Journal.encryption?, r.cipher.packet.nonce < REJECT_AFTER_MESSAGES := by
  have material := ResidentMaterial.initialized trace placeholders
  have bound := bindings material (BatchJournal.Scheduler.initialized trace placeholders)
    (StagingMaterial.initialized trace placeholders)
  exact ⟨bound,unique bound (StagingMaterial.initialized_exclusive trace placeholders),
    bounded material (PacketOrigins.initialized trace placeholders) (ReservationHistory.initialized trace placeholders)⟩

/-- The exact old-event projection gives the same allocation-key nonce result
for the final causal observer, including internally stopped executions. -/
theorem final_initialized (trace : Runner.Trace) (placeholders : Bool) :
    let h := (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
      AuthenticatedEffects.CausalJournal.old?
    Bindings h ∧ ((h.filterMap Journal.encryption?).map token).Nodup ∧
      ∀ r ∈ h.filterMap Journal.encryption?, r.cipher.packet.nonce < REJECT_AFTER_MESSAGES := by
  have history := congrArg Prod.snd (AuthenticatedEffects.CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  dsimp only
  rw [←history]
  exact initialized trace placeholders

end Leanux.Proofs.WG.HandshakeSecurity.EncryptionMaterial
