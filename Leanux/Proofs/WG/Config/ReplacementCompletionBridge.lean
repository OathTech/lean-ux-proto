import Leanux.Proofs.WG.Config.ReplacementCompletionSource
import Leanux.Proofs.WG.Index.ReceiverCoreBridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.ReplaceCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Queues.RxCredits Queues.RxCredits.DurableHolders AllowedIps Std.Do Lifetimes

theorem input_snapshot (cs : Ledger) (loans : Reservations)
    (tables : FlatTable × FlatTable) (w : WGWorld) (a : Ambient) :
    View.Input cs loans tables (Campaign2.snapshot w a) ↔ Input cs loans tables w := by
  constructor
  · rintro ⟨v,b,same,input⟩
    exact Index.receiveInput_world (congrArg Campaign2.Snapshot.wg same) ▸ input
  · intro input
    exact ⟨w,a,rfl,input⟩

end Leanux.Proofs.WG.Config.ReplaceCompletion
