import Leanux.Proofs.WG.Queues.RxBorrow
import Leanux.Proofs.WG.Roaming.Frames
set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteCompletion
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing
open Lifetimes Queues

theorem store_remotes {α : Type} {action : WG.M α} (frame : SameWGStore action) :
    SameView destinationAt action :=
  frame.of_factor (fun s => fun pid => ((s.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination)
    destinationAt (fun _ => rfl)

theorem lookupRepay_remotes (protocol : Nat) (bytes : List UInt8) :
    SameView destinationAt (RxBorrow.source protocol bytes) := by
  apply (RxBorrow.source_frame protocol bytes).of_factor
    (fun s : WGStoreView × (PeerId → Option Peer) => fun pid => ((s.2 pid).bind Peer.endpoint).map destination)
    destinationAt
  intro g
  rfl
end Leanux.Proofs.WG.Roaming.RemoteCompletion

