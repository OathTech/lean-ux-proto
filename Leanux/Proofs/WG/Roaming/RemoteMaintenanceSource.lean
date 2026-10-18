import Leanux.Proofs.WG.Roaming.RemoteMaintenanceFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteMaintenance
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open RemoteSilent

theorem allowedContracts : Config.AllowedFrame.Contracts destinationAt where
  aip := aip_frame
  deleteList := listDel_frame
  appendList := fun pid id => modifyPeer_remotes pid
    (fun p => {p with allowedipsList := p.allowedipsList ++ [id]}) (fun _ => rfl)
  sequence := modifyDev_remotes _ (fun _ => rfl)
  removeNode := fun id => node_frame (removeNodeBody_sameNode id)

theorem removeByPeer_frame (pid : PeerId) : SameView destinationAt (removeByPeer pid) :=
  Config.AllowedFrame.remove allowedContracts pid

theorem flushedSend (entry : RemoteMap) (pid : PeerId) :
    Ensures (runFlushedSendWork pid) (Retained entry) (fun _ => Retained entry) :=
  Index.runFlushedSendWork_preserves _ pid
    (of_frame entry _ (prepare_frame pid)) (sendWorker entry pid)

theorem drain (entry : RemoteMap) (upTo : Option PeerId) :
    Ensures (drainHandshakeSendWq upTo) (Retained entry) (fun _ => Retained entry) :=
  Index.drainHandshakeSendWq_preserves _ (flushedSend entry) (flushedClear entry) upTo

theorem timers (entry : RemoteMap) (pid : PeerId) :
    Ensures (timersStop pid) (Retained entry) (fun _ => Retained entry) :=
  Index.timersStop_preserves _ (fun p t => of_frame entry _ (delTimer_remotes p t))
    (drain entry) pid

theorem makeDead_frame (pid : PeerId) : SameView destinationAt (peerMakeDead pid) := by
  rw [Configuration.peerMakeDead_factor]
  unfold Configuration.peerMakeDeadWith
  exact (modifyDev_remotes (fun d => {d with peerList:=d.peerList.filter (· != pid)}) (fun _=>rfl)).bind (fun _ =>
    (removeByPeer_frame pid).bind (fun _ =>
    (RemoteCompletion.store_remotes getDev_sameWGStore).bind (fun d =>
    (show SameView destinationAt (branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid)) : WG.M Bool) from
      fun initial => hoare_liftAmbient (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2 == pid)))
        (fun g=>destinationAt g=initial)).bind (fun _ =>
    (modifyDev_remotes (fun d=>{d with peerHashtable:=d.peerHashtable.filter (·.2 != pid)}) (fun _=>rfl)).bind (fun _ =>
      modifyPeer_remotes pid (fun p=>{p with isDead:=true}) (fun _=>rfl))))))

theorem afterDead (entry : RemoteMap) (pid : PeerId) :
    Ensures (peerRemoveAfterDead pid) (Retained entry) (fun _ => Retained entry) :=
  Index.peerRemoveAfterDead_preserves _
    (fun p => of_frame entry _ (keypairsClear_frame p)) (timers entry) (drain entry)
    (of_frame entry _ (modifyDev_remotes _ (fun _=>rfl)))
    (fun p => peerPut_remotes (some p) entry) pid

theorem remove (entry : RemoteMap) (peer : Option PeerId) :
    Ensures (peerRemove peer) (Retained entry) (fun _ => Retained entry) :=
  Index.peerRemove_preserves _ (fun p=>of_frame entry _ (makeDead_frame p)) (afterDead entry) peer

theorem removeAll (entry : RemoteMap) :
    Ensures peerRemoveAll (Retained entry) (fun _ => Retained entry) :=
  Index.peerRemoveAll_preserves _ (of_frame entry _ free_frame)
    (fun p=>of_frame entry _ (makeDead_frame p)) (afterDead entry)

theorem destruct (entry : RemoteMap) :
    Ensures wgDestruct (Retained entry) (fun _ => Retained entry) := by
  intro w a result v b _ run
  have absent := Index.wgDestruct_absent w a result v b trivial run
  intro pid remote present
  simp [destinationAt,peerAt,absent] at present

theorem stopPeer_plain (entry : RemoteMap) (pid : PeerId) :
    StatePrefixPreserves (fun _ w _ => Retained entry w) (fun _ => True)
      (Index.LifecycleIndex.stopPeerPlain pid) := by
  apply DriverTags.Control.stopPeerWith_preserves
  · intro p
    apply Index.LifecycleIndex.native_lift
    simp only [requireNotPending]
    exact preserves_pure ()
  · intro p; exact Index.LifecycleIndex.native_lift _ _ ((purge_frame p).wp (RemoteRetained entry))
  · intro p; exact Index.LifecycleIndex.native_lift _ _ ((ensures_iff _ _ _).mp (timers entry p))
  · intro p; exact Index.LifecycleIndex.native_lift _ _ ((handshakeClear_frame p).wp (RemoteRetained entry))
  · intro p; exact Index.LifecycleIndex.native_lift _ _ ((keypairsClear_frame p).wp (RemoteRetained entry))
  · intro p
    apply Index.LifecycleIndex.native_lift
    unfold resetLastSentHandshake
    exact preserves_bind (hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent) (Retained entry))
      (fun now => (modifyPeer_remotes p (fun p=>{p with lastSentHandshake:=now-(REKEY_TIMEOUT+1 : Nat).toInt64*NSEC_PER_SEC64})
        (fun _=>rfl)).wp (RemoteRetained entry))

theorem stop (entry : RemoteMap) : Ensures wgStop (Retained entry) (fun _ => Retained entry) := by
  refine (Noise.ensures_iff wgStop (Retained entry) (fun _ => Retained entry)).mpr ?_
  apply Index.LifecycleIndex.native_erased (Retained entry)
    (DriverTags.Control.stopWith (fun {_} a=>liftWGPrefix a) Index.LifecycleIndex.stopPeerPlain) wgStop
  · rw [DriverTags.Control.stop_factor]
    exact DriverTags.Control.stopWith_erases _ _ Index.LifecycleIndex.stopPeerPlain_erases
  · apply DriverTags.Control.stopWith_preserves _ _ (fun _ _ _ _=>trivial)
      _ (stopPeer_plain entry)
    · exact Index.LifecycleIndex.native_lift _ _ ((RemoteCompletion.store_remotes getDev_sameWGStore).wp (RemoteRetained entry))
    · intro b; exact Index.LifecycleIndex.native_ambient _ (AmbientM.branch .stopPeersIter b)
    · exact Index.LifecycleIndex.native_ambient _ (AmbientM.unsupported _)
    · exact Index.LifecycleIndex.native_ambient _ (AmbientM.branch .stopDrainIter false)
    · exact Index.LifecycleIndex.native_lift _ _ ((modifyDev_remotes (fun d=>{d with handshakeQueueLen:=0}) (fun _=>rfl)).wp (RemoteRetained entry))
    · exact Index.LifecycleIndex.native_lift _ _ ((socket_frame (socketReinit_sameSocket none none)).wp (RemoteRetained entry))

theorem down (entry : RemoteMap) : Ensures wgDown (Retained entry) (fun _ => Retained entry) := by
  rw [DriverTags.Control.down_factor]
  exact ensures_bind _ _ (of_frame entry _ (modifyDev_remotes _ (fun _=>rfl))) (fun _=>stop entry)

end Leanux.Proofs.WG.Roaming.RemoteMaintenance
