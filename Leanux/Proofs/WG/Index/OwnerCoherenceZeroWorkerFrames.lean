import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceExpiryFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Handshake unhash and zeroing retain entry slot coverage: no owner is
introduced, and the resident's reference count and three slots are unchanged. -/
theorem expiryZeroDevice_lastOwnerCovered (d : Device) (pid : PeerId) (p : Peer)
    (covered : LastOwnerCovered d pid p) :
    LastOwnerCovered (Config.expiryZeroDevice d pid p) pid (Config.zeroedHandshake p) := by
  let removed : Device := {d with indexTable := removeOwner (.handshake pid) d.indexTable}
  apply peerWrite_lastOwnerCovered removed pid p (Config.zeroedHandshake p) rfl rfl
  intro last e member word
  have old : e ∈ d.indexTable := (List.mem_filter.mp member).1
  exact covered last e old word

end Leanux.Proofs.WG.Index
