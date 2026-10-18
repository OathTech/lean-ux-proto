import Leanux.Proofs.WG.Roaming.RemoteSilentSource
import Leanux.Proofs.WG.Roaming.RemoteBorrowFrames
import Leanux.Proofs.WG.Index.BulkRemovalSource
import Leanux.Proofs.WG.Index.LifecycleControlSource
import Leanux.Proofs.WG.Index.LifecycleSource
import Leanux.Proofs.WG.Noise.DriverTagAllowedFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteWorkers
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Std.Do TimerDiscipline
open RemoteSilent

theorem packet_frame {α : Type} (a : SkbM α) : SameView destinationAt (liftSkb a) := by
  intro initial
  apply hoare_liftSkb
  intro w d store hi hd
  funext pid
  simpa only [destinationAt,peerAt,hd,Option.bind_some] using congrFun hi pid

theorem getKeypair_frame (kid : KeypairId) : SameView destinationAt (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a key final after run
  exact congrArg destinationAt (KeyTimes.getKeypair_return kid g final key a after run).1

theorem keypairPut_frame (kid : Option KeypairId) (now : Bool) :
    SameView destinationAt (keypairPut kid now) := by
  have frame : SameView peerAt (keypairPut kid now) :=
    fun initial => keypairPut_peers_spec (fun ps=>ps=initial) kid now
  exact frame.of_factor (fun ps => fun pid => ((ps pid).bind Peer.endpoint).map destination)
    destinationAt (fun _ => rfl)

theorem product_store {α : Type} (entry : RemoteMap) (action : Leanux.M α)
    (frame : SameProductStore action) :
    Preserves (fun w : World=>Retained entry w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result final pre run
  have same := congrArg (fun s : ProductStore43 => s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w result final run)
  have maps := congrArg (fun s : WGStoreView => fun pid : PeerId =>
    ((s.dev.bind fun d=>d.peers[pid]?).bind Peer.endpoint).map destination) same
  change destinationAt final.wg=destinationAt w.wg at maps
  change RemoteRetained entry (destinationAt final.wg)
  rw [maps]
  exact pre

end Leanux.Proofs.WG.Roaming.RemoteWorkers
