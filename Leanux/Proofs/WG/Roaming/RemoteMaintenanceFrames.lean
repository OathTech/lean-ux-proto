import Leanux.Proofs.WG.Roaming.RemoteSilentSource
import Leanux.Proofs.WG.Roaming.RemoteBorrowFrames
import Leanux.Proofs.WG.Index.BulkRemovalSource
import Leanux.Proofs.WG.Index.LifecycleControlSource
import Leanux.Proofs.WG.Index.LifecycleSource
import Leanux.Proofs.WG.Noise.DriverTagAllowedFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteMaintenance
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open RemoteSilent

theorem socket_frame {α : Type} {action : WG.M α} (frame : SameSocket action) :
    SameView destinationAt action := by
  apply frame.of_factor (fun s : WGOwnedView => fun pid =>
    ((s.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination) destinationAt
  intro g
  funext pid
  cases device : g.dev <;>
    simp [destinationAt,peerAt,socketView,socketDevice,wgOwnedView,wgStoreView,device]

theorem aip_frame {α : Type} (a : AipM α) : SameView destinationAt (liftAip a) := by
  intro initial
  apply hoare_liftAip
  intro w d store hi hd
  funext pid
  simpa only [destinationAt,peerAt,hd,Option.bind_some] using congrFun hi pid

theorem node_frame {α : Type} {action : WG.M α} (frame : SameNode action) :
    SameView destinationAt action := by
  apply frame.of_factor (fun s : WGStoreView => fun pid : PeerId =>
    ((s.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination) destinationAt
  intro g
  funext pid
  cases device : g.dev <;>
    simp [destinationAt,peerAt,nodeView,nodeDevice,wgStoreView,device]

theorem listDel_frame (id : NodeId) : SameView destinationAt (listDel id) := by
  apply (AllowedIps.listDel_clearListView id).of_factor
    (fun s => fun pid => ((s.2 pid).bind Peer.endpoint).map destination) destinationAt
  intro g
  funext pid
  simp [destinationAt,peerAt,AllowedIps.clearListView,Option.map_bind,
    Function.comp_def,Option.bind_map,Option.bind_assoc]

theorem free_frame : SameView destinationAt WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  have effect := (hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.free_storeView (wgStoreView g)) g ambient result final after rfl run
  have peers := congrArg (fun s : WGStoreView × (PeerId → Option Peer) =>
    fun pid => ((s.2 pid).bind Peer.endpoint).map destination) effect
  funext pid
  simpa [destinationAt,peerAt,AllowedIps.clearStoreView,
    AllowedIps.clearStoreProjection,wgStoreView,Option.map_bind,Option.map_map,
    Option.bind_map,Function.comp_def,Option.bind_assoc,AllowedIps.resetAllowedips] using congrFun peers pid

theorem prepare_frame (pid : PeerId) : SameView destinationAt (Index.flushedSendPrepare pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v after run
  cases device : w.dev with
  | none =>
    simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,peer,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      cases pendingFlag : p.handshakePending with
      | false =>
        simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,peer,pendingFlag,invariant,AmbientM.invariant] at run
        cases run
      | true =>
        simp [Index.flushedSendPrepare,modifyDev,getPeer,getDev,device,peer,pendingFlag,setPeer] at run
        obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
        funext target
        by_cases same : pid = target
        · subst target
          simp [destinationAt,peerAt,device,peer]
        · simp [destinationAt,peerAt,device,Std.TreeMap.getElem?_insert,same]

end Leanux.Proofs.WG.Roaming.RemoteMaintenance
