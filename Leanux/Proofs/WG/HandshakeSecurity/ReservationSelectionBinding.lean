import Leanux.Proofs.WG.HandshakeSecurity.ReservationSelectionInitialized
import Leanux.Proofs.WG.HandshakeSecurity.InitializedEncryptionMaterial

/-! Material at the actual AEAD read traces through the allocation's one
reservation bank to the earlier native current-slot selection. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity Responder ReservationAssignments

theorem StagingMaterial.Safe.prefix (safe : StagingMaterial.Safe (h ++ suffix)) : StagingMaterial.Safe h := by
  intro pre event post position
  apply safe pre event (post ++ suffix)
  rw [position]
  simp only [List.append_assoc,List.cons_append]

namespace ReservationSelection

theorem Safe.prefix (safe : Safe (h ++ suffix)) : Safe h := by
  intro pre event post position
  apply safe pre event (post ++ suffix)
  rw [position]
  simp only [List.append_assoc,List.cons_append]

theorem Safe.at (safe : Safe h) (found : h[index]? = some (.reserved slot r)) :
    r.Valid (Nonce.reserveNative slot) ∧ Picked (h.take index) slot r.before := by
  obtain ⟨bound,value⟩ := List.getElem?_eq_some_iff.mp found
  apply safe (h.take index) (.reserved slot r) (h.drop (index + 1))
  rw [←value,List.getElem_cons_drop bound,List.take_append_drop]

theorem selected_of_binding (safe : Safe h) (bank : StagingMaterial.Safe h)
    (bound : ResidentMaterial.BoundReceipt h r) :
    Earlier h r.read.value.keypair (keyCore r.cipher.keyRead.value) := by
  obtain ⟨generation,_,packets,allocation,n,input,member,_,_,atInput,_,material,resident,_⟩ := bound
  obtain ⟨before,after,position⟩ := List.mem_iff_append.mp member
  have found : h[before.length]? = some (.allocated packets allocation) := by rw [position]; simp
  have mapped := (StagingMaterial.bank_spec bank found).1
  rw [←mapped,List.getElem?_map] at atInput
  cases used : (StagingMaterial.bank h before.length)[n]? with
  | none => simp [used] at atInput
  | some u =>
    rw [used] at atInput
    have same : u.packet = input := Option.some.inj atInput
    have key : u.packet.keypair = r.read.value.keypair := by
      rw [same]
      simpa only [PacketMaterial.material] using congrArg DataPacket.keypair material
    have atReservation := (StagingMaterial.bank_spec bank found).2.2 u (List.mem_of_getElem? used)
    have core := atReservation.2.2 (keyCore r.cipher.keyRead.value) (by simpa only [same] using resident)
    have receipt := (Bank.credit_valid (StagingMaterial.bank_valid bank) found used).2.2.2
    have earlier := (safe.at receipt).2 _ core
    have full : Earlier h u.packet.keypair (keyCore r.cipher.keyRead.value) := by
      have extended := Earlier.append (suffix := h.drop (u.position + 1)) earlier
      simpa only [List.take_append_drop] using extended
    simpa only [key] using full

/-- Each actual AEAD's core was selected strictly earlier in the same source
journal. The native packet, bank and selection carriers are initialized. -/
theorem initialized_encryption (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 = pre ++ .encrypted r :: post) :
    r.Valid ∧ Earlier pre r.read.value.keypair (keyCore r.cipher.keyRead.value) := by
  obtain ⟨valid,bound⟩ := ResidentMaterial.initialized trace placeholders pre (.encrypted r) post position
  have member : r ∈ ((runPrefixOuter (Journal.execute trace placeholders) []).2).filterMap Journal.encryption? := by
    rw [position]
    exact List.mem_filterMap.mpr ⟨.encrypted r,by simp,rfl⟩
  have batch := (BatchJournal.Scheduler.initialized trace placeholders r member).2.2
  have selection := initialized trace placeholders
  have bank := StagingMaterial.initialized trace placeholders
  rw [position] at selection bank
  exact ⟨valid,selected_of_binding selection.prefix bank.prefix (bound batch)⟩

end ReservationSelection
end Leanux.Proofs.WG.HandshakeSecurity
