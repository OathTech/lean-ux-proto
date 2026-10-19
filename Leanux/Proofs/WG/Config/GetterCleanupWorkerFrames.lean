import Leanux.Proofs.WG.Config.GetterMetadataFrames
import Leanux.Proofs.WG.Config.GetterCleanupMacFrames
import Leanux.Proofs.WG.Config.ReplacementCompletionSource
import Leanux.Proofs.WG.Index.CreatorSource
import Leanux.Proofs.WG.Index.SenderIndexSource
import Leanux.Proofs.WG.Index.BulkRemovalSource
import Leanux.Proofs.WG.Roaming.RemoteTimerFrames
import Leanux.Proofs.WG.Config.AllowedRemovalReadbackFrames
import Leanux.Proofs.WG.Index.AllowedFrameSource
import Leanux.Proofs.WG.Config.GetterCleanupFrames
import Leanux.Proofs.WG.Config.GetterCleanupTimerFrames
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterCleanup
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do

theorem normal_frame {α : Type} {action : WG.M α}
    (frame : SameView getterMetadata action) (entry : GetterMetadata) :
    Ensures action (fun g=>getterMetadata g=entry) (fun _ g=>getterMetadata g=entry) :=
  (ensures_iff _ _ _).mpr (frame entry)
theorem creator (pid : PeerId) : SameView getterMetadata (createInitiation pid) := by
  intro initial
  apply (ensures_iff _ _ _).mp
  apply Index.createInitiation_preserves_source pid
  · intro ck hash
    exact normal_frame (modify_peer pid _) initial
  · intro secret
    exact normal_frame (modify_peer pid _) initial
  · exact normal_frame (modify_peer pid _) initial
  · exact normal_frame ((dereference (.handshake pid)).bind
      (fun _=>index (indexInsert (.handshake pid)))) initial
theorem sender (pid : PeerId) : SameView getterMetadata (sendHandshakeInitiation pid) := by
  intro initial
  apply (ensures_iff _ _ _).mp
  apply Index.sendInitiation_preserves_source pid
  · intro now
    exact normal_frame (modify_peer pid _) initial
  · exact normal_frame (creator pid) initial
  · intro msg
    exact normal_frame (mac pid msg) initial
  · exact normal_frame (traversal pid) initial
  · exact normal_frame (delete_timer pid .sendKeepalive) initial
  · intro msg
    exact sendBufferToPeer_getterMetadata pid msg initial
  · exact normal_frame (initiated pid) initial
theorem send_worker (pid : PeerId) : SameView getterMetadata (handshakeSendWorker pid) :=
  (sender pid).bind (fun _=>peerPut_metadata_getter_variant (some pid))
theorem send_prepare (pid : PeerId) : SameView getterMetadata (Index.flushedSendPrepare pid) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold Index.flushedSendPrepare
  repeat' getter_cleanup_step initial
theorem flushed_send (pid : PeerId) : SameView getterMetadata (runFlushedSendWork pid) :=
  fun initial=>(ensures_iff _ _ _).mp (Index.runFlushedSendWork_preserves _ pid
    (normal_frame (send_prepare pid) initial) (normal_frame (send_worker pid) initial))
theorem flushed_clear (pid : PeerId) : SameView getterMetadata (runFlushedClearWork pid) := by
  intro initial
  apply (ensures_iff _ _ _).mp
  apply Index.runFlushedClearWork_preserves
  · exact normal_frame (modify_device (fun d=>{d with clearWorkQueue:=d.clearWorkQueue.erase pid}) (fun _=>rfl)) initial
  · exact normal_frame (clear_worker pid) initial
theorem drain (upTo : Option PeerId) : SameView getterMetadata (drainHandshakeSendWq upTo) :=
  fun initial=>(ensures_iff _ _ _).mp (Index.drainHandshakeSendWq_preserves _
    (fun pid=>normal_frame (flushed_send pid) initial)
    (fun pid=>normal_frame (flushed_clear pid) initial) upTo)
theorem timers_stop (pid : PeerId) : SameView getterMetadata (timersStop pid) :=
  fun initial=>(ensures_iff _ _ _).mp (Index.timersStop_preserves _
    (fun pid timer=>normal_frame (delete_timer pid timer) initial)
    (fun upTo=>normal_frame (drain upTo) initial) pid)
theorem after_dead (pid : PeerId) : SameView getterMetadata (peerRemoveAfterDead pid) :=
  fun initial=>(ensures_iff _ _ _).mp (Index.peerRemoveAfterDead_preserves _
    (fun pid=>normal_frame (keypairs_clear pid) initial)
    (fun pid=>normal_frame (timers_stop pid) initial)
    (fun upTo=>normal_frame (drain upTo) initial)
    (normal_frame (modify_device (fun d=>{d with numPeers:=d.numPeers-1}) (fun _=>rfl)) initial)
    (fun pid=>normal_frame (peerPut_metadata_getter_variant (some pid)) initial) pid)
theorem remove_all : SameView getterMetadata peerRemoveAll :=
  fun initial=>(ensures_iff _ _ _).mp (Index.peerRemoveAll_preserves _
    (normal_frame free_allowed initial)
    (fun pid=>normal_frame (make_dead pid) initial)
    (fun pid=>normal_frame (after_dead pid) initial))



end Leanux.Proofs.WG.Config.GetterCleanup
