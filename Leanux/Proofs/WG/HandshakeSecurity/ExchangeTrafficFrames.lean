import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDeviceConfiguration
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1TrafficFrames
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation
import Leanux.Proofs.WG.Lifetimes.TxCallSource

/-! Traffic frames are projected from WireGuard state, separately from the
actual source callback composition. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem product_wg_stable (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : ProductInv h w) : ProductInv h v := by
  apply retained hi
  have tags := congrArg (fun s : WGStoreView => fun pid : PeerId =>
    (s.dev.bind fun d => d.peers[pid]?).map Peer.handshakeState) same
  intro pid tag found _
  exact (congrFun tags pid).symm.trans found

theorem multicast_frame (family addr : Nat) (h : List Event) :
    Framing.Preserves (ProductInv h) (Env.xmitMulticastLoop family addr) := by
  have native : Framing.Preserves (ProductInv h)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (frame_store h _ (loopbackSend_kernel [] true))
  have ambient {α : Type} (a : AmbientM α) :
      Framing.Preserves (ProductInv h) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  routing_tx_source [Env.xmitMulticastLoop] using [native,ambient]

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
