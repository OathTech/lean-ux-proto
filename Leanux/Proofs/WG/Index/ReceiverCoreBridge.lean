import Leanux.Proofs.WG.Index.ReceiverCoreModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem receiveInput_world {w v : WGWorld} {a b : Ambient}
    (same : (Campaign2.snapshot w a).wg=(Campaign2.snapshot v b).wg) : w=v := by
  cases w
  cases v
  simp_all [Campaign2.snapshot,Campaign2.core]

theorem receiveInput_snapshot (cs : Ledger) (loans : Reservations) (w : WGWorld) (a : Ambient) :
    View.ReceiveInput cs loans (Campaign2.snapshot w a) ↔ Incoming.Cut cs loans w := by
  constructor
  · rintro ⟨v,b,same,cut⟩
    have worlds : v=w := receiveInput_world (congrArg Campaign2.Snapshot.wg same)
    exact worlds ▸ cut
  · intro cut
    exact ⟨w,a,rfl,cut⟩


end Leanux.Proofs.WG.Index
