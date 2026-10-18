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
    SameView destinationAt (handshakeInit pid psk) := by
  have modify_eq (f : Peer → Peer) : Noise.modifyPeer pid f = (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have factor : handshakeInit pid psk = (do
      modifyPeer pid (fun p => {p with handshakeEntryPeer := some pid})
      if ← branch .handshakeInitHasPsk psk.isSome then
        modifyPeer pid (fun p => {p with presharedKey := psk.getD p.presharedKey})
      precomputeStaticStatic pid) := by
    simp only [handshakeInit,IndexOwner.setPeerWord,modify_eq,bind_assoc]
  rw [factor]
  apply (modifyPeer_remotes pid (fun p => {p with handshakeEntryPeer := some pid}) (fun _ => rfl)).bind
  intro _
  apply (show SameView destinationAt (branch .handshakeInitHasPsk psk.isSome) from
    fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun g => destinationAt g = initial)).bind
  intro hasPsk
  cases hasPsk
  · simpa using precompute_remotes pid
  · exact (modifyPeer_remotes pid (fun p => {p with presharedKey := psk.getD p.presharedKey})
      (fun _ => rfl)).bind (fun _ => precompute_remotes pid)

theorem resetLast_remotes (pid : PeerId) :
    SameView destinationAt (resetLastSentHandshake pid) := by
  have factor : resetLastSentHandshake pid = (do
      let now ← hiddenClock64 .resetLastSent
      modifyPeer pid (fun p => {p with
        lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64})) := by
    rfl
  rw [factor]
  exact (show SameView destinationAt (hiddenClock64 .resetLastSent : WG.M Int64) from
    fun initial => hoare_liftAmbient (AmbientM.hiddenClock64 _) (fun g => destinationAt g = initial)).bind
    (fun _ => modifyPeer_remotes pid _ (fun _ => rfl))

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
