import Leanux.Proofs.WG.Roaming.RemoteDriverCaptureSource
import Leanux.Proofs.WG.Roaming.RemoteBirthFrames
import Leanux.Proofs.WG.Index.ConfigurationPeerSource
import Leanux.Proofs.WG.Roaming.InitiationRejectionFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration RemoteSilent

theorem ambient_frame {α : Type} (a : AmbientM α) :
    SameView destinationAt (StateT.lift a : WG.M α) :=
  fun initial => hoare_liftAmbient a (fun g => destinationAt g = initial)

theorem configuration_frame {α : Type} {action : WG.M α} (frame : SameConfiguration action) :
    SameView destinationAt action := by
  apply frame.of_factor (fun s : WGOwnedView => fun pid =>
    ((s.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination) destinationAt
  intro g
  funext pid
  cases device : g.dev <;>
    simp [destinationAt,peerAt,configurationView,configurationDevice,wgOwnedView,wgStoreView,device]

theorem lookup_frame (key : Key) : SameView destinationAt (pubkeyLookup key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a value final b run
  exact endpointMap_destinations
    ((pubkeyLookup_initiationEndpoints key g.dev g a value final b rfl run).1)

theorem port_frame (port : Nat) : SameView destinationAt (setPort port) := by
  unfold setPort
  apply (RemoteCompletion.store_remotes getDev_sameWGStore).bind
  intro d
  apply (ambient_frame (AmbientM.branch .setPortSame (d.incomingPort == port))).bind
  intro same
  cases same with
  | true => exact SameView.pure destinationAt 0
  | false =>
    apply (DumpComposition.forIn_sameView d.peerList ()
      (fun pid _ => do
        _ ← branch .setPortPeerIter true
        clearPeerEndpointSrc pid
        pure (.yield ()))
      (fun pid _ => (ambient_frame (AmbientM.branch .setPortPeerIter true)).bind (fun _ =>
        (RemoteMutation.clear_source_destinations pid).bind (fun _ =>
          SameView.pure destinationAt (ForInStep.yield ()))))).bind
    intro _
    apply (ambient_frame (AmbientM.branch .setPortPeerIter false)).bind
    intro _
    apply (ambient_frame (AmbientM.branch .setPortNotRunning !d.running)).bind
    intro down
    cases down with
    | true => exact (modifyDev_remotes (fun d => {d with incomingPort := port})
        (fun _ => rfl)).bind (fun _ => SameView.pure destinationAt 0)
    | false => exact RemoteMaintenance.socket_frame (socketInit_sameSocket port)

theorem expiry_frame (pid : PeerId) : SameView destinationAt (expireCurrentPeerKeypairs pid) := by
  intro initial
  change Preserves (fun g=>destinationAt g=initial) _
  unfold expireCurrentPeerKeypairs
  simp (config := {zeta:=false}) only [requireNotPending,pure_bind,branch]
  repeat' first
    | (rx_retention_head handshakeClear; exact (handshakeClear_frame _).wp (fun s=>s=initial))
    | (rx_retention_head resetLastSentHandshake; exact (RemoteBirth.resetLast_remotes _).wp (fun s=>s=initial))
    | (rx_retention_head getPeer; exact (getPeer_frame _).wp (fun s=>s=initial))
    | (rx_retention_head getKeypair; exact (RemoteWorkers.getKeypair_frame _).wp (fun s=>s=initial))
    | (rx_retention_head setKeypair; exact
        (modifyDev_remotes (fun d=>{d with keypairs:=d.keypairs.insert _ _}) (fun _=>rfl)).wp (fun s=>s=initial))
    | (rx_retention_head invariant; unfold invariant)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem keepaliveSetup_frame (pid : PeerId) (interval : Nat) (running : Bool) :
    SameView destinationAt (HolderConfigTail.setup pid interval running) := by
  intro initial
  change Preserves (fun g=>destinationAt g=initial) _
  apply Index.ConfigurationIndex.peerReadUpdate_preserves _ pid
    (fun p=>{p with persistentKeepaliveInterval:=interval})
  · intro p before
    change Preserves (fun g : WGWorld=>g=before) _
    unfold WG.andM
    simp (config := {zeta:=false}) only [branch]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  · exact (modifyPeer_remotes pid (fun p=>{p with persistentKeepaliveInterval:=interval})
      (fun _=>rfl)).wp (fun s=>s=initial)

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
