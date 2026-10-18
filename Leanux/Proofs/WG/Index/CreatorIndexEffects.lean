import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.RetirementRetentionEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do
open Queues.RxCredits

/-- Handshake publication adds no keypair row; every retained key row keeps
its actual resident owner and slot witnesses. -/
theorem hashSlotCoverage_handshakeInsert (d : Device) (pid : PeerId) (index : Nat)
    (covered : HashSlotCoverage d) :
    HashSlotCoverage {d with indexTable :=
      {index,owner := .handshake pid} :: removeOwner (.handshake pid) d.indexTable} := by
  intro entry member kid owner
  rcases List.mem_cons.mp member with same | kept
  · subst entry
    cases owner
  · exact covered entry (List.mem_filter.mp kept).1 kid owner

/-- A handshake row creates no dead-key retirement obligation, and all
surviving key rows retain their original stamped reservation witnesses. -/
theorem deadHashedReserved_handshakeInsert (retired : Reservations)
    (d : Device) (pid : PeerId) (index : Nat)
    (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired {d with indexTable :=
      {index,owner := .handshake pid} :: removeOwner (.handshake pid) d.indexTable} := by
  intro entry member kid key target peer owner keyFound keyPeer peerFound dead
  rcases List.mem_cons.mp member with same | kept
  · subst entry
    cases owner
  · exact reserved entry (List.mem_filter.mp kept).1 kid key target peer
      owner keyFound keyPeer peerFound dead

end Leanux.Proofs.WG.Index
