import Leanux.Proofs.WG.Roaming.RemoteDriverSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Roaming.RemoteDriver
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem store_inv (entry : RemoteMap) (history : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (pre : Inv entry history w) :
    Inv entry history v := by
  have maps := congrArg (fun s : ProductStore43 => fun pid : PeerId =>
    ((s.2.2.2.dev.bind fun d=>d.peers[pid]?).bind Peer.endpoint).map destination) same
  change destinationAt v.wg = destinationAt w.wg at maps
  unfold Inv NativeInv
  rw [maps]
  exact pre

end Leanux.Proofs.WG.Roaming.RemoteDriver
