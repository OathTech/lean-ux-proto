import Leanux.Proofs.WG.TransmitSecurity.NonceReceiveFrames
import Leanux.Proofs.WG.Lifetimes.StackSource
import Leanux.Proofs.WG.Queues.RxNapiCuts

/-! Stack route and environment bookkeeping preserve the projected nonce state.
Only the actual WireGuard transmit callback reserves sending nonces. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes

theorem product_store (h : List Allocation) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : Inv (view w.wg) h) :
    Inv (view v.wg) h := by
  have store := congrArg (fun s : ProductStore43 => s.2.2.2) same
  have projected := congrArg (fun s : WGStoreView => View.mk s.keypairCounter
    (fun id => (s.dev.bind fun d => d.keypairs[id]?).map Nonce.cell)) store
  change view v.wg = view w.wg at projected
  simpa only [projected] using hi


theorem pending_peers : SameView view Queues.RxNapi.pendingSource :=
  device_read.bind (fun _ => SameView.pure _ _)

theorem scheduled_peers : SameView view Queues.RxNapi.scheduledSource :=
  device_read.bind (fun _ => SameView.pure _ _)

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
