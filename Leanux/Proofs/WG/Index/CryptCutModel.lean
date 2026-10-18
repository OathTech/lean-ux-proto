import Leanux.Proofs.WG.Index.CryptCoreFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.CryptCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

def Cut (initial : Ledger) (loans : Reservations)
    (before h : List RxHistory.Event) (w : World) : Prop :=
  HolderNapi.At initial loans before h w ∧ OwnerChecks.Inv h w ∧
    CurrentSlots.Inv w.wg ∧ BaseCoherence.Inv w.wg ∧ Reached.Core w.wg

end Leanux.Proofs.WG.Index.CryptCore
