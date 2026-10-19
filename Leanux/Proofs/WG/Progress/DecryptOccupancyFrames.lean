import Leanux.Proofs.WG.Progress.DecryptOccupancyModel
import Leanux.Proofs.WG.Queues.RxRingScheduler

/-! Physical decrypt-cell retention through the actual RX publication tail,
and its exact campaign projection. Peer/key deletion remains permitted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DecryptOccupancy
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
open Leanux.Proofs.WG.Queues

theorem enqueue_cell (id : SkbId) (state : PacketState) :
    SameView RxRing.cell (enqueuePerPeerRx napiIrqExit id state) := by
  ring_poll_source [enqueuePerPeerRx] using [RxRing.napiIrqExit_cell]
    with [RxRing.peerGet_frame, RxRing.getPeer_frame, RxRing.setPeer_frame, RxRing.peerPut_frame]

theorem afterItem_cell : SameView RxRing.cell
    (do branch .decWorkerNeedResched (← condResched .decryptWorker) : Leanux.M Bool) := by
  have cond := (condResched_sameKernel .decryptWorker).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map fun d => (d.ifindex,d.decryptQueue))
    RxRing.cell (fun _ => rfl)
  ring_poll_source [] using [cond] with []



end Leanux.Proofs.WG.Progress.DecryptOccupancy
