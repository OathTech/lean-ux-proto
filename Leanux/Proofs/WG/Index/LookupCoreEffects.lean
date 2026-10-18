import Leanux.Proofs.WG.Index.IncomingIndexEffects
import Leanux.Proofs.WG.Index.ReachedIndexModel
import Leanux.Proofs.WG.Index.OwnerCoherenceFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Lifetimes Std.Do

/-- Resident acquisition leaves the table/cursor unchanged, preserves all
three slots and dead-owner reservations, and increases only the selected count. -/
theorem deviceIndexCore_acquire (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]?=some p) (core : DeviceIndexCore d) :
    DeviceIndexCore (acquirePeer d pid p) := by
  have kept := incomingIndex_acquire [] d pid p resident ⟨core.2.1,core.2.2.2⟩
  exact ⟨core.1,kept.1,
    fun entry member => ownerCoherent_acquire d pid p resident entry.owner
      (core.2.2.1 entry member),kept.2⟩
end Leanux.Proofs.WG.Index
