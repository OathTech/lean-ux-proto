import Leanux.Proofs.WG.Index.AllowedFrameSource
import Leanux.Proofs.WG.Noise.DriverTagLeafFrames
import Leanux.Proofs.WG.Noise.PendingAllowedInsertionFrames

/-! Allowed-IP operations project the existing list/node contracts onto tags.
Insertion composes the existing source factors, without a second trie proof. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do Queues

theorem aip_frame {α : Type} (a : AipM α) : SameView tagView (liftAip a) := by
  intro initial
  apply hoare_liftAip
  intro w d store hi hd
  funext pid
  simpa only [tagView,responseTagMap,hd,Option.bind_some] using congrFun hi pid

theorem node_frame {α : Type} {a : WG.M α} (frame : SameNode a) : SameView tagView a := by
  apply frame.of_factor (fun s => responseTagMap s.dev) tagView
  intro g
  change responseTagMap g.dev = responseTagMap (g.dev.map nodeDevice)
  cases g.dev <;> rfl

theorem listDel_frame (id : NodeId) : SameView tagView (listDel id) := by
  apply (AllowedIps.listDel_clearListView id).of_factor
    (fun s => fun pid => (s.2 pid).map Peer.handshakeState) tagView
  intro g
  funext pid
  simp [tagView,responseTagMap,AllowedIps.clearListView,
    Option.map_bind,Option.map_map,Function.comp_def]

theorem free_frame : SameView tagView WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  have effect := (hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.free_storeView (wgStoreView g)) g ambient result final after rfl run
  have peers := congrArg (fun s : WGStoreView × (PeerId → Option Peer) =>
    fun pid => (s.2 pid).map Peer.handshakeState) effect
  funext pid
  simpa [tagView,responseTagMap,AllowedIps.clearStoreView,
    AllowedIps.clearStoreProjection,wgStoreView,Option.map_bind,Option.map_map,
    Option.bind_map,Function.comp_def,AllowedIps.resetAllowedips] using congrFun peers pid

theorem listAddTail_frame (pid : PeerId) (id : NodeId) : SameView tagView (listAddTail pid id) :=
  modifyPeer_frame pid (fun p => {p with allowedipsList := p.allowedipsList ++ [id]})
    (fun _ => rfl)

theorem allowedContracts : Config.AllowedFrame.Contracts tagView where
  aip := aip_frame
  deleteList := listDel_frame
  appendList := listAddTail_frame
  sequence := modifyDev_frame _ (fun _=>funext fun _=>rfl)
  removeNode := fun id=>node_frame (removeNodeBody_sameNode id)

theorem removeByPeer_frame (pid : PeerId) : SameView tagView (removeByPeer pid) :=
  Config.AllowedFrame.remove allowedContracts pid

theorem addPlacedSource_frame (root : Slot) (bits key cidr : Nat) (pid : PeerId)
    (placed : Option NodeId) (exact : Bool) :
    SameView tagView (Config.addPlacedSource root bits key cidr pid placed exact) :=
  Config.AllowedFrame.placed allowedContracts root bits key cidr pid placed exact

theorem addRootSource_frame (root : Slot) (bits key cidr : Nat) (pid : PeerId)
    (trie : Option NodeId) :
    SameView tagView (Config.addRootSource root bits key cidr pid trie) :=
  Config.AllowedFrame.root allowedContracts root bits key cidr pid trie

theorem add_frame (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView tagView (add root bits key cidr peer) :=
  Config.AllowedFrame.add allowedContracts root bits key cidr peer

theorem insert_frame (family addr cidr : Nat) (pid : PeerId) :
    SameView tagView (WG.insert family addr cidr pid) :=
  Config.AllowedFrame.insert allowedContracts family addr cidr pid

theorem setAllowedip_frame (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView tagView (setAllowedip pid ip) :=
  Config.AllowedFrame.allowed allowedContracts pid ip

end Leanux.Proofs.WG.Noise.DriverTags
