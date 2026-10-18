import Leanux.Proofs.WG.Index.ReceiverCoreBridge
import Leanux.Proofs.WG.Index.ReachedReceiverSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem receiveStep_index (cs : Ledger) (loans : Reservations) :
    Campaign2.Ensures receiveStep (View.ReceiveInput cs loans)
      (fun _ => View.ReceiveInput cs loans) := by
  intro w a result v b pre run
  exact (receiveInput_snapshot cs loans v b).mpr
    (Incoming.receiveStep_cut cs loans w a result v b
      ((receiveInput_snapshot cs loans w a).mp pre) run)


end Leanux.Proofs.WG.Index
