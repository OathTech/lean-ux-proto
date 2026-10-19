import Leanux.Proofs.WG.TransmitSecurity.ReservationInitialized
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverOuter

/-! Joining initialized packet origins and reservation receipts in the same
journal. The source connection is positional even if execution later stops. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationHistory
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {id : SkbId}

theorem Safe.prefix (safe : Safe (pre ++ post)) : Safe pre := by
  intro before event after position
  exact safe before event (after ++ post) (by simp only [position,List.append_assoc,List.cons_append])

theorem Safe.packet (safe : Safe history)
    (origin : PacketOrigins.Certificate history generation id value) :
    value.nonce < REJECT_AFTER_MESSAGES ∧ Reserved history value.keypair value.nonce := by
  obtain ⟨packets,run,member,_,_,n,packet,atPacket,_,material⟩ := origin
  obtain ⟨pre,post,position⟩ := List.mem_iff_append.mp member
  have checked := safe pre (.allocated packets run) post position
  have packetMember : packet ∈ packets := List.mem_of_getElem? atPacket
  have bounded := checked.2 packet packetMember
  have nonce : packet.nonce = value.nonce := by simpa only [PacketMaterial.material] using congrArg DataPacket.nonce material
  have key : packet.keypair = value.keypair := by simpa only [PacketMaterial.material] using congrArg DataPacket.keypair material
  constructor
  · exact nonce ▸ bounded.1
  · have included : pre ⊆ history := by
      intro e inside
      rw [position]
      exact List.mem_append_left _ inside
    simpa only [nonce,key] using bounded.2.mono included

theorem initialized_encryption (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 =
      pre ++ .encrypted r :: post) :
    r.Valid ∧ r.read.value.nonce < REJECT_AFTER_MESSAGES ∧
      Reserved pre r.read.value.keypair r.read.value.nonce := by
  have safe := initialized trace placeholders
  rw [position] at safe
  have origin := PacketOrigins.initialized trace placeholders pre (.encrypted r) post position
  obtain ⟨generation,_,certificate⟩ := origin.2
  refine ⟨origin.1,?_⟩
  simpa only [PacketMaterial.material] using safe.prefix.packet certificate

end Leanux.Proofs.WG.TransmitSecurity.ReservationHistory
