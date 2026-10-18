import Leanux.Proofs.WG.Index.RetirementRetentionEffects
import Leanux.Proofs.WG.Index.HashSlotClearWorkerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise
open Queues.RxCredits

/-- Handshake clearing removes only its own table row and updates a resident
peer without changing its allocation stamp or dead flag. -/
theorem expiryZeroDevice_deadHashedReserved (retired : Reservations)
    (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired (Config.expiryZeroDevice d pid p) := by
  let removed : Device := {d with indexTable := removeOwner (.handshake pid) d.indexTable}
  have smaller : DeadHashedReserved retired removed := by
    intro entry member kid key target peer owner keyFound keyPeer peerFound dead
    exact reserved entry (List.mem_filter.mp member).1 kid key target peer
      owner keyFound keyPeer peerFound dead
  exact peerWrite_deadHashedReserved retired removed pid p (Config.zeroedHandshake p)
    resident rfl rfl smaller

end Leanux.Proofs.WG.Index
