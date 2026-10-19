import Leanux.Proofs.WG.Roaming.RemoteChronologyPollBridge
import Leanux.Proofs.WG.Roaming.RemoteChronologyCaptureSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Poll
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem suffixTracks_product_store {E : Type} (effect : Effect E) (entry : RemoteMap)
    (base h : List E) (w v : World) (same : productStoreView v = productStoreView w)
    (prior : SuffixTracks effect entry base h w) : SuffixTracks effect entry base h v := by
  obtain ⟨suffix,shape,tracked⟩ := prior
  refine ⟨suffix,shape,?_⟩
  have maps := congrArg (fun s : ProductStore43 => fun pid : PeerId =>
    ((s.2.2.2.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination) same
  change destinationAt v.wg = destinationAt w.wg at maps
  unfold Tracks
  rw [maps]
  exact tracked


end Leanux.Proofs.WG.Roaming.RemoteChronology.Poll
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem store_inv (entry : RemoteMap) (history : List RemoteDriver.Event) (w v : World)
    (same : productStoreView v = productStoreView w) (pre : Inv entry history w) :
    Inv entry history v := by
  have maps := congrArg (fun s : ProductStore43 => fun pid : PeerId =>
    ((s.2.2.2.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination) same
  change destinationAt v.wg = destinationAt w.wg at maps
  unfold Inv NativeInv RemoteChronology.Inv
  rw [maps]
  exact pre

theorem wg_store_inv (entry : RemoteMap) (history : List RemoteDriver.Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (pre : Inv entry history w) :
    Inv entry history v := by
  have maps := congrArg (fun s : WGStoreView => fun pid : PeerId =>
    ((s.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination) same
  change destinationAt v.wg = destinationAt w.wg at maps
  unfold Inv NativeInv RemoteChronology.Inv
  rw [maps]
  exact pre


end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
