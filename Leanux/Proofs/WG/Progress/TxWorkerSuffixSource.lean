import Leanux.Proofs.WG.Progress.SocketSuffixSource
import Leanux.Proofs.WG.Progress.StagingSuffixSource
import Leanux.Proofs.WG.TimerDiscipline.HookTransmitWorkerSource

/-! Concrete normal record-suffix transport through data completion and transmit
steps. Existing timer, socket, release and exact source factors supply every leaf. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.TimerDiscipline Leanux.Proofs.WG.Noise Queues

theorem keepKeyFresh_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (keepKeyFresh pid) := by
  unfold keepKeyFresh
  repeat' first
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head getKeypair; exact native_getKeypair records _)
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head branchCmp; exact native_branchCmp records _ _ _ _)
    | (native_suffix_head branchExpired; exact native_expired records _ _ _ _)
    | (native_suffix_head sendQueuedHandshakeInitiation; exact queuedInitiation_retains records _ _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | (native_suffix_head WG.andM; apply native_and)
    | (native_suffix_head WG.orM; apply native_or)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem dataDoneStep_retains (records : List HiddenRecord) (pid : PeerId) (id : SkbId) (sent : Bool) :
    NativeKeeps records (dataDoneStep pid id sent) := by
  unfold dataDoneStep
  repeat' first
    | (native_suffix_head getTxSkb; exact native_getTx records _)
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head sendSkbToPeer; exact sendSkbToPeer_retains records _ _ _)
    | (native_suffix_head WG.andM; apply native_and)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem dataDoneFinish_retains (records : List HiddenRecord) (pid : PeerId) (sent : Bool) :
    NativeKeeps records (dataDoneFinish pid sent) := by
  unfold dataDoneFinish
  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head timersDataSent; exact timersDataSent_retains records _)
    | (native_suffix_head keepKeyFresh; exact keepKeyFresh_retains records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem createDataDone_retains (records : List HiddenRecord) (pid : PeerId) (item : List SkbId) :
    NativeKeeps records (createDataDone pid item) := by
  rw [←dataDoneSource_eq]
  unfold dataDoneSource
  exact native_bind records _ _ (timersTraversal_retains records pid) (fun _=>
    native_bind records _ _ (timersAnySent_retains records pid) (fun _=>
      native_bind records _ _
        (native_forIn records _ _ _ (dataDoneStep_retains records pid))
        (dataDoneFinish_retains records pid)))

theorem txPrepare_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (HookJournal.TransmitWorker.prepare pid) := by
  unfold HookJournal.TransmitWorker.prepare
  repeat' first
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | (native_suffix_head getTxSkb; exact native_getTx records _)
    | (native_suffix_head PrevQueue.peek; exact prev_peek_retains records _)
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | (native_suffix_head WG.andM; apply native_and)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem txDispose_retains (records : List HiddenRecord)
    (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    NativeKeeps records (TxDisposition.disposeSource pid item key) := by
  unfold TxDisposition.disposeSource
  apply native_bind records _ _
    (native_forIn records _ _ _ (fun id _=>
      native_bind records _ _ (native_freeTx records id) (fun _=>native_pure records _)))
  intro _
  exact native_bind records _ _ (keypairPut_retains records (some key) false) (fun _=>
    native_bind records _ _ (peerPut_retains records (some pid)) (fun _=>native_pure records _))

theorem txStep_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (txStep pid) := by
  rw [←HookJournal.TransmitWorker.source]
  unfold HookJournal.TransmitWorker.stepWith
  apply native_bind records _ _ (txPrepare_retains records pid)
  rintro (_|⟨item,key,crypted⟩)
  · exact native_pure records _
  · cases crypted
    · exact txDispose_retains records pid item key
    · exact native_bind records _ _ (createDataDone_retains records pid item)
        (fun _=>txDispose_retains records pid item key)

end Leanux.Proofs.WG.Progress.RecordSuffix
