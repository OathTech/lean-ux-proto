import Leanux.Proofs.WG.Roaming.RemoteSilentFrames
import Leanux.Proofs.WG.Index.CallbackRulesSource
import Leanux.Proofs.WG.Index.SenderIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteSilent
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing Std.Do TimerDiscipline

theorem callback (entry : RemoteMap) (pid : PeerId) (timer : PeerTimer) :
    Ensures (timerCallback pid timer) (Retained entry) (fun _ => Retained entry) := by
  apply Index.CallbackRules.callback (Q := Retained entry)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact of_frame entry _ (modifyPeer_remotes pid _ (fun _ => rfl))
  · exact of_frame entry _ (modifyPeer_remotes pid _ (fun _ => rfl))
  · exact of_frame entry _ (RemoteMutation.clear_source_destinations pid)
  · exact of_frame entry _ (purge_frame pid)
  · exact of_frame entry _ (delTimer_remotes pid .sendKeepalive)
  · intro site timer delay
    exact of_frame entry _ (modPeerTimer_remotes site pid timer delay)
  · intro retry
    exact sendQueuedHandshakeInitiation_remotes pid retry entry
  · exact sendKeepalive_remotes pid entry
  · exact peerGet_retained entry pid
  · exact peerPut_remotes (some pid) entry
  · exact of_frame entry _ (modifyDev_remotes _ (fun _ => rfl))

theorem createInitiation_frame (pid : PeerId) : SameView destinationAt (createInitiation pid) := by
  intro initial
  apply (ensures_iff _ _ _).mp
  exact Index.createInitiation_preserves_source pid (fun g => destinationAt g = initial)
    (fun ck hash => (ensures_iff _ _ _).mpr
      (modifyPeer_remotes pid (fun p => {p with chainingKey := ck, hash}) (fun _ => rfl) initial))
    (fun secret => (ensures_iff _ _ _).mpr
      (modifyPeer_remotes pid (fun p => {p with ephemeralPrivate := clamp secret}) (fun _ => rfl) initial))
    ((ensures_iff _ _ _).mpr
      (modifyPeer_remotes pid (fun p => {p with handshakeState := HANDSHAKE_CREATED_INITIATION})
        (fun _ => rfl) initial))
    ((ensures_iff _ _ _).mpr (creatorPublish_remotes pid initial))

theorem clearWorker (entry : RemoteMap) (pid : PeerId) :
    Ensures (queuedExpiredZeroKeyMaterial pid) (Retained entry) (fun _ => Retained entry) := by
  unfold queuedExpiredZeroKeyMaterial
  exact ensures_bind _ _ (of_frame entry _ (handshakeClear_frame pid)) (fun _ =>
    ensures_bind _ _ (of_frame entry _ (keypairsClear_frame pid)) (fun _ =>
      peerPut_remotes (some pid) entry))

theorem flushedClear (entry : RemoteMap) (pid : PeerId) :
    Ensures (runFlushedClearWork pid) (Retained entry) (fun _ => Retained entry) :=
  Index.runFlushedClearWork_preserves _ pid
    (of_frame entry _ (modifyDev_remotes _ (fun _ => rfl))) (clearWorker entry pid)

theorem sendInitiation_frame (pid : PeerId) : SameView destinationAt (sendHandshakeInitiation pid) := by
  intro initial
  apply (ensures_iff _ _ _).mp
  apply Index.sendInitiation_preserves_source pid (fun g => destinationAt g=initial)
  · intro now
    exact (ensures_iff _ _ _).mpr
      (modifyPeer_remotes pid (fun p => {p with lastSentHandshake:=now}) (fun _ => rfl) initial)
  · exact (ensures_iff _ _ _).mpr (createInitiation_frame pid initial)
  · intro msg
    exact (ensures_iff _ _ _).mpr (addMacToPacket_spec_remotes_variant pid msg initial)
  · exact (ensures_iff _ _ _).mpr (traversal_remotes pid initial)
  · exact (ensures_iff _ _ _).mpr (delTimer_remotes pid .sendKeepalive initial)
  · intro msg
    exact (ensures_iff _ _ _).mpr (sendBufferToPeer_spec_remotes_variant pid msg initial)
  · exact (ensures_iff _ _ _).mpr (initiated_frame pid initial)

theorem sendWorker (entry : RemoteMap) (pid : PeerId) :
    Ensures (handshakeSendWorker pid) (Retained entry) (fun _ => Retained entry) := by
  unfold handshakeSendWorker
  exact ensures_bind _ _ (of_frame entry _ (sendInitiation_frame pid))
    (fun _ => peerPut_remotes (some pid) entry)

theorem dataCompletion (entry : RemoteMap) (pid : PeerId) (item : List SkbId) :
    Ensures (createDataDone pid item) (Retained entry) (fun _ => Retained entry) := by
  exact (ensures_iff _ _ _).mpr (DataCompletionRules.preserves _ pid item
    ((ensures_iff _ _ _).mp (of_frame entry _ (traversal_remotes pid)))
    ((ensures_iff _ _ _).mp (of_frame entry _ (delTimer_remotes pid .sendKeepalive)))
    (fun bytes ds => (ensures_iff _ _ _).mp (of_frame entry _ (sendSkb_frame pid bytes ds)))
    ((ensures_iff _ _ _).mp (of_frame entry _ (dataSent_frame pid)))
    (Queues.RxCredits.TxReservation.keepKeyFresh_preserves _ pid
      ((ensures_iff _ _ _).mp (sendQueuedHandshakeInitiation_remotes pid false entry))))

end Leanux.Proofs.WG.Roaming.RemoteSilent
