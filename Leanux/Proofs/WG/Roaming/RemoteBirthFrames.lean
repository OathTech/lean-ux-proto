import Leanux.Proofs.WG.Noise.PeerInitializationSource
import Leanux.Proofs.WG.Roaming.RemoteBirthModel
import Leanux.Proofs.WG.Roaming.RemoteTransportFrames
import Leanux.Proofs.WG.Roaming.RemotePeerFrames
import Leanux.Proofs.WG.Noise.DriverTagSource
import Leanux.Proofs.WG.Queues.BaseCreation
import Leanux.Proofs.WG.Config.Precomputation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteBirth
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits Leanux.Proofs.Framing Std.Do

theorem precompute_remotes (pid : PeerId) :
    SameView destinationAt (precomputeStaticStatic pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases device : g.dev with
  | none =>
    simp [precomputeStaticStatic,requireNotPending,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [precomputeStaticStatic,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨value,out,tail,execution,effect⟩ :=
        Config.precomputeStaticStatic_returns pid d p resident g ambient device
      rw [run] at execution
      cases execution
      funext target
      change ((final.dev.bind fun d => d.peers[target]?).bind Peer.endpoint).map destination = _
      rw [effect]
      unfold Config.precomputeDevice
      split
      · dsimp only
        split
        all_goals by_cases same : pid = target
        all_goals first
          | (subst target; simp [destinationAt,peerAt,Config.withPeer,device,resident])
          | simp [destinationAt,peerAt,Config.withPeer,device,Std.TreeMap.getElem?_insert,same]
      · by_cases same : pid = target
        all_goals first
          | (subst target; simp [destinationAt,peerAt,Config.withPeer,device,resident])
          | simp [destinationAt,peerAt,Config.withPeer,device,Std.TreeMap.getElem?_insert,same]

theorem handshakeInit_remotes (pid : PeerId) (psk : Option Key) :
    SameView destinationAt (handshakeInit pid psk) :=
  handshakeInit_frame_source destinationAt pid psk
    (modifyPeer_remotes pid _ (fun _=>rfl))
    (modifyPeer_remotes pid _ (fun _=>rfl))
    (precompute_remotes pid)
theorem resetLast_remotes (pid : PeerId) :
    SameView destinationAt (resetLastSentHandshake pid) :=
  resetLastSentHandshake_frame_source destinationAt pid
    (fun _=>modifyPeer_remotes pid _ (fun _=>rfl))
theorem finish_remotes (pid : PeerId) (key : Key) (psk : Option Key) :
    SameView destinationAt (BaseCreation.finish pid key psk) := by
  unfold BaseCreation.finish
  exact (remotes_frame_of_sendWork _ pid
    (TimerDiscipline.dstCacheReset_sendWorkView pid)).bind (fun _ =>
      (handshakeInit_remotes pid psk).bind (fun _ =>
        (resetLast_remotes pid).bind (fun _ =>
          modifyDev_remotes _ (fun _ => rfl))))

theorem creationCore_remotes (w : WGWorld) (pid : PeerId) (key : Key) :
    destinationAt (Peers.creationCoreWorld w pid key) =
      birthRemotes (destinationAt w) (.ok pid) := by
  funext target
  cases device : w.dev <;> by_cases same : pid = target
  all_goals simp [destinationAt,peerAt,Peers.creationCoreWorld,Peers.createdPeer,
    birthRemotes,device,Std.TreeMap.getElem?_insert,same]

end Leanux.Proofs.WG.Roaming.RemoteBirth
