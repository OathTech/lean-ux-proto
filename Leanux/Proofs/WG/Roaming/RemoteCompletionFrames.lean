import Leanux.Proofs.WG.Roaming.RemoteSessionFrames
import Leanux.Proofs.WG.Roaming.RemoteTimerFrames
import Leanux.Proofs.WG.Roaming.RemoteSetterFrames
import Leanux.Proofs.WG.Roaming.RemoteTransportFrames
import Leanux.Proofs.WG.Roaming.RemoteBorrowFrames
import Leanux.Proofs.WG.Index.ReceiveCompletionSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteCompletion
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing
open Lifetimes Queues TimerDiscipline

def Retained (entry : RemoteMap) (g : WGWorld) : Prop := RemoteRetained entry (destinationAt g)

theorem receivedWithKeypair_remotes (pid : PeerId) (received : KeypairId) :
    SameView destinationAt (receivedWithKeypair pid received) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases device : g.dev with
  | none =>
    simp [receivedWithKeypair,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [receivedWithKeypair,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨out,ending,effect⟩ := receivedWithKeypair_effect pid received d p resident
        g ambient result final after device run
      apply endpointMap_destinations
      rw [ending,device]
      by_cases matched : p.keypairNext = some received
      · simp only [ConfirmationEffect,matched,ite_true] at effect
        exact rotationRun_endpoints effect.2
      · simp only [ConfirmationEffect,matched,ite_false] at effect
        rw [effect.2]

theorem keepKeyFreshRx_retained (entry : RemoteMap) (pid : PeerId) :
    Preserves (Retained entry) (keepKeyFreshRx pid) :=
  Index.ReceiveCompletion.keepKeyFreshRx_preserves_source (Retained entry) pid
    ((modifyPeer_remotes pid (fun p => {p with sentLastminuteHandshake := true}) (fun _ => rfl)).wp (RemoteRetained entry))
    ((ensures_iff _ _ _).mp (sendQueuedHandshakeInitiation_remotes pid false entry))

theorem timersDataReceived_retained (entry : RemoteMap) (pid : PeerId) :
    Preserves (Retained entry) (timersDataReceived pid) :=
  Index.ReceiveCompletion.dataReceived_preserves_source (Retained entry) pid
    ((modPeerTimer_remotes _ _ _ _).wp (RemoteRetained entry))
    ((modifyPeer_remotes pid (fun p => {p with timerNeedAnotherKeepalive := true}) (fun _ => rfl)).wp (RemoteRetained entry))

theorem updateRxStats_remotes (pid : PeerId) (len : Nat) :
    SameView destinationAt (updateRxStats pid len) := by
  change SameView destinationAt ((modifyDev fun d => {d with rxPackets := d.rxPackets+1,rxBytes := d.rxBytes+len}) >>= fun _ =>
      modifyPeer pid (fun p => {p with rxBytes := p.rxBytes+len}))
  exact (modifyDev_remotes
    (fun d : Device => {d with rxPackets := d.rxPackets+1,rxBytes := d.rxBytes+len})
    (fun _ => rfl)).bind (fun _ =>
    modifyPeer_remotes pid (fun p => {p with rxBytes := p.rxBytes+len}) (fun _ => rfl))

theorem dishonest_remotes (why : Dishonest) :
    SameView destinationAt (dishonest why) := by
  cases why <;> exact modifyDev_remotes _ (fun _ => rfl)

theorem prepareRest_retained (entry : RemoteMap) (pid : PeerId) (pkt : RxPacket) :
    Preserves (Retained entry) (RxCredits.prepareRest pid pkt) :=
  Index.ReceiveCompletion.prepareRest_preserves_source (Retained entry) pid pkt
    (keepKeyFreshRx_retained entry pid)
    ((delTimer_remotes pid .newHandshake).wp (RemoteRetained entry))
    ((traversal_remotes pid).wp (RemoteRetained entry))
    (timersDataReceived_retained entry pid)
    (fun len => (updateRxStats_remotes pid len).wp (RemoteRetained entry))
    (fun why => (dishonest_remotes why).wp (RemoteRetained entry))
    (fun protocol ds bytes => (store_remotes (inetEcnDecapsulate_sameWGStore protocol ds bytes)).wp
      (RemoteRetained entry))

theorem rxFinish_remotes (pid : PeerId) (ready : Packets.RxReady) :
    SameView destinationAt (Packets.rxFinish pid ready) := by
  intro initial
  exact Index.ReceiveCompletion.rxFinish_preserves_source (fun w => destinationAt w = initial)
    pid ready ((lookupRepay_remotes _ _).wp (fun s => s = initial))
    ((dishonest_remotes _).wp (fun s => s = initial))
    ((updateRxStats_remotes _ _).wp (fun s => s = initial))

theorem afterConfirmation_retained (entry : RemoteMap) (pid : PeerId) (pkt : RxPacket)
    (confirmed : Bool) :
    Preserves (Retained entry) (ConsumeConfirmation.afterConfirmation pid pkt confirmed) :=
  Index.ReceiveCompletion.afterConfirmation_preserves_source (Retained entry) pid pkt confirmed
    ((handshakeComplete_remotes _ _).wp (RemoteRetained entry))
    ((ensures_iff _ _ _).mp (sendStagedPackets_remotes pid entry))
    (prepareRest_retained entry pid pkt)
    (fun ready => (rxFinish_remotes pid ready).wp (RemoteRetained entry))


end Leanux.Proofs.WG.Roaming.RemoteCompletion

