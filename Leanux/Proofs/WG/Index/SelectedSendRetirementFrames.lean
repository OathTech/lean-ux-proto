import Leanux.Proofs.WG.Index.SelectedSendRetirementModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Leanux.Proofs.Logged
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- The preparation changes no owner word, count, key slot, allocation stamp
or dead flag. Only the actual queue occurrence and PENDING flag change. -/
theorem sendPrepared_index
    (retired : Reservations) (pid : PeerId)
    (w : WGWorld) (d : Device) (p : Peer) (device : w.dev = some d)
    (resident : d.peers[pid]? = some p)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (safe : SendIndexSafe retired w) :
    ConfiguredIdentity.Inv {w with dev := some (sendPreparedDevice d pid p)} ∧
      BaseCoherence.Inv {w with dev := some (sendPreparedDevice d pid p)} ∧
      SendIndexSafe retired {w with dev := some (sendPreparedDevice d pid p)} := by
  let dequeued := {d with sendWorkQueue := d.sendWorkQueue.erase pid}
  let updated := {p with handshakePending := dequeued.sendWorkQueue.contains pid}
  have hp : dequeued.peers[pid]? = some p := resident
  have cfg : ConfiguredIdentity.view {w with dev := some (sendPreparedDevice d pid p)} =
      ConfiguredIdentity.view w := by
    simp only [ConfiguredIdentity.view,device,Option.map_some]
    exact congrArg some (ConfiguredIdentity.state_peer_same dequeued pid p updated hp rfl)
  refine ⟨?_,BaseCoherence.transport base ?_,?_,?_,?_⟩
  · intro state found
    exact configured state (cfg.symm.trans found)
  · simp [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,device,sendPreparedDevice]
  · intro actual found
    cases found
    exact hashSlotCoverage_peerWrite dequeued pid p updated hp rfl (safe.1 d device)
  · intro actual found
    cases found
    exact peerWrite_owner_coherent dequeued pid p updated hp rfl rfl (safe.2.1 d device)
  · intro actual found
    cases found
    exact peerWrite_deadHashedReserved retired dequeued pid p updated hp rfl rfl (safe.2.2 d device)

end Leanux.Proofs.WG.Index
