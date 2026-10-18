import Leanux.Proofs.WG.Roaming.RemoteLifecycleSource
import Leanux.Proofs.WG.Roaming.RemoteDriverSource
import Leanux.Proofs.WG.Index.ReachedOrdinaryControlSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDispatch
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open RemoteSilent

theorem dump_frame {α : Type} (action : WG.M α) (frame : SameDump action) :
    SameView destinationAt action := by
  apply frame.of_factor (fun s : WGStoreView=>fun pid : PeerId=>
    ((s.dev.bind fun d=>d.peers[pid]?).bind Peer.endpoint).map destination) destinationAt
  intro g
  rfl

theorem mtu_frame (mtu : Nat) :
    SameView (fun w : World=>destinationAt w.wg) (Env.setMtu mtu) := by
  apply (setMtu_sameEnvScalar mtu).of_factor
    (fun s : ProductStore43=>fun pid=>
      ((s.2.2.2.dev.bind fun d=>d.peers[pid]?).bind Peer.endpoint).map destination)
  intro w
  funext pid
  cases device : w.wg.dev <;>
    simp [destinationAt,peerAt,envScalarView,envScalarStore,envScalarDevice,productStoreView,wgStoreView,device]

theorem store_retained {α : Type} (entry : RemoteMap) (action : Leanux.M α)
    (same : SameView (fun w : World=>wgStoreView w.wg) action) :
    Preserves (fun w : World=>Retained entry w.wg) action :=
  (same.of_factor (fun s : WGStoreView=>fun pid : PeerId=>
    ((s.dev.bind fun d=>d.peers[pid]?).bind Peer.endpoint).map destination)
    (fun w : World=>destinationAt w.wg) (fun _=>rfl)).wp (RemoteRetained entry)

end Leanux.Proofs.WG.Roaming.RemoteDispatch
