import Leanux.Proofs.WG.Config.GetterScalarFrames
import Leanux.Proofs.WG.Index.CreatorSource
import Leanux.Proofs.WG.Index.SenderIndexSource
import Leanux.Proofs.WG.Index.BulkRemovalSource
import Leanux.Proofs.WG.Queues.JointRemoval

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
theorem creator (pid : PeerId) : SameView view (createInitiation pid) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  apply Index.createInitiation_preserves_source pid
  · intro ck hash
    exact (ensures_iff _ _ _).mpr (modify_peer pid (fun p=>{p with chainingKey:=ck,hash}) (fun _=>rfl) entry)
  · intro secret
    exact (ensures_iff _ _ _).mpr (modify_peer pid (fun p=>{p with ephemeralPrivate:=clamp secret}) (fun _=>rfl) entry)
  · exact (ensures_iff _ _ _).mpr (modify_peer pid (fun p=>{p with handshakeState:=HANDSHAKE_CREATED_INITIATION}) (fun _=>rfl) entry)
  · unfold Index.creatorPublish
    exact ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (indexOwner_peerDeref_preserves (.handshake pid) (fun g=>view g=entry)))
      (fun _=>(ensures_iff _ _ _).mpr (index_frame (indexInsert (.handshake pid)) entry))

theorem sender (pid : PeerId) : SameView view (sendHandshakeInitiation pid) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  apply Index.sendInitiation_preserves_source pid
  · intro now
    exact (ensures_iff _ _ _).mpr
      (modify_peer pid (fun p=>{p with lastSentHandshake:=now}) (fun _=>rfl) entry)
  · exact (ensures_iff _ _ _).mpr (creator pid entry)
  · intro msg
    exact (ensures_iff _ _ _).mpr (mac pid msg entry)
  · exact (ensures_iff _ _ _).mpr (traversal pid entry)
  · exact (ensures_iff _ _ _).mpr (delete_timer pid .sendKeepalive entry)
  · intro msg
    exact (ensures_iff _ _ _).mpr (socket pid msg entry)
  · exact (ensures_iff _ _ _).mpr (initiated pid entry)

theorem worker (entry : Map) (pid : PeerId) :
    Ensures (handshakeSendWorker pid) (Retained entry) (fun _=>Retained entry) := by
  unfold handshakeSendWorker
  exact ensures_bind _ _ (of_frame entry _ (sender pid)) (fun _=>peer_put entry (some pid))

theorem clear_worker (entry : Map) (pid : PeerId) :
    Ensures (queuedExpiredZeroKeyMaterial pid) (Retained entry) (fun _=>Retained entry) := by
  unfold queuedExpiredZeroKeyMaterial
  exact ensures_bind _ _ (of_frame entry _ (handshake_clear pid)) (fun _=>
    ensures_bind _ _ (of_frame entry _ (keypairs_clear pid)) (fun _=>peer_put entry (some pid)))

theorem flushed_send (entry : Map) (pid : PeerId) :
    Ensures (runFlushedSendWork pid) (Retained entry) (fun _=>Retained entry) :=
  Index.runFlushedSendWork_preserves _ pid (of_frame entry _ (prepare pid)) (worker entry pid)

theorem flushed_clear (entry : Map) (pid : PeerId) :
    Ensures (runFlushedClearWork pid) (Retained entry) (fun _=>Retained entry) :=
  Index.runFlushedClearWork_preserves _ pid
    (of_frame entry _ (modify_device (fun d=>{d with clearWorkQueue:=d.clearWorkQueue.erase pid}) (fun _=>rfl)))
    (clear_worker entry pid)

theorem drain (entry : Map) (upTo : Option PeerId) :
    Ensures (drainHandshakeSendWq upTo) (Retained entry) (fun _=>Retained entry) :=
  Index.drainHandshakeSendWq_preserves _ (flushed_send entry) (flushed_clear entry) upTo

theorem timers_stop (entry : Map) (pid : PeerId) :
    Ensures (timersStop pid) (Retained entry) (fun _=>Retained entry) :=
  Index.timersStop_preserves _ (fun p t=>of_frame entry _ (delete_timer p t)) (drain entry) pid

theorem make_dead (pid : PeerId) : SameView view (peerMakeDead pid) := by
  rw [Configuration.peerMakeDead_factor]
  unfold Configuration.peerMakeDeadWith
  exact (modify_device (fun d=>{d with peerList:=d.peerList.filter (· !=pid)}) (fun _=>rfl)).bind (fun _=>
    (scalar_frame (ScalarAllowed.remove_frame pid)).bind (fun _=>
    read_device.bind (fun d=>
    (show SameView view (branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2==pid)) : WG.M Bool) from
      fun entry=>hoare_liftAmbient (AmbientM.branch .pubkeyRemoveHashed (d.peerHashtable.any (·.2==pid)))
        (fun g=>view g=entry)).bind (fun _=>
    (modify_device (fun d=>{d with peerHashtable:=d.peerHashtable.filter (·.2 !=pid)}) (fun _=>rfl)).bind (fun _=>
      modify_peer pid (fun p=>{p with isDead:=true}) (fun _=>rfl))))))

theorem after_dead (entry : Map) (pid : PeerId) :
    Ensures (peerRemoveAfterDead pid) (Retained entry) (fun _=>Retained entry) :=
  Index.peerRemoveAfterDead_preserves _
    (fun p=>of_frame entry _ (keypairs_clear p)) (timers_stop entry) (drain entry)
    (of_frame entry _ (modify_device (fun d=>{d with numPeers:=d.numPeers-1}) (fun _=>rfl)))
    (fun p=>peer_put entry (some p)) pid

theorem remove (entry : Map) (peer : Option PeerId) :
    Ensures (peerRemove peer) (Retained entry) (fun _=>Retained entry) :=
  Index.peerRemove_preserves _ (fun p=>of_frame entry _ (make_dead p)) (after_dead entry) peer

theorem remove_all (entry : Map) :
    Ensures peerRemoveAll (Retained entry) (fun _=>Retained entry) :=
  Index.peerRemoveAll_preserves _ (of_frame entry _ free_frame)
    (fun p=>of_frame entry _ (make_dead p)) (after_dead entry)

end Leanux.Proofs.WG.Config.GetterScalar
