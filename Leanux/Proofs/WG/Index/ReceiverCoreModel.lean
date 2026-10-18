import Leanux.Proofs.WG.Index.IncomingCallerModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

namespace View
def ReceiveInput (cs : Ledger) (loans : Reservations) (s : Campaign2.Snapshot) : Prop :=
  ∃ w a,Campaign2.snapshot w a=s ∧ Incoming.Cut cs loans w

end View

end Leanux.Proofs.WG.Index
