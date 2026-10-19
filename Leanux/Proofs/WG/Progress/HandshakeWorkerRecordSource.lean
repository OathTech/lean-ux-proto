import Leanux.Proofs.WG.Progress.HandshakeCallerSuffixSource
import Leanux.Proofs.WG.Progress.CryptIterationRecordSource
import Leanux.Proofs.WG.Progress.ClearWorkerRecordSource
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource

/-! Concrete normal record decrease for original receive activations and
selected handshake send work. No completion guard or successful return is assumed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem receiveIteration_record_effect (records : List HiddenRecord) :
    Hoare (workerIter .receiveWorker none (monadLift WG.receiveStep : Leanux.M Bool) (condResched .receiveWorker))
      (fun w=>w.ambient.hidden=some records)
      (fun result w=>Tail records w.ambient.hidden ∧
        (result=.yielded→StrictTail records w.ambient.hidden)) :=
  workerIter_record_effect _ _ _ _ records
    (native_product records _ (receiveStep_retains records))
    (condResched_after_tail .receiveWorker records)

theorem receive_activation_strict (a : Activation) (worker : a.worker=.receiveWorker)
    (records : List HiddenRecord) :
    Hoare (Activation.run a) (fun w=>w.ambient.hidden=some records)
      (fun _ w=>StrictTail records w.ambient.hidden) := by
  apply activation_strict_of_iterations .receiveWorker _ a worker records
  intro active same input
  simpa only [Activation.iter,same] using receiveIteration_record_effect input

theorem sendSelect_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) TimerDiscipline.sendWorkerSelection := by
  unfold TimerDiscipline.sendWorkerSelection
  apply preserves_bind (native_product records _ (native_getDev records))
  intro d
  split
  · apply preserves_bind (peekUnit_retains records .sendWorker)
    intro named
    cases named
    · exact preserves_bind (preserves_pure _) (fun _=>preserves_pure _)
    · exact preserves_bind (resolveUnit_retains records _ _ _) (fun _=>preserves_pure _)
  · apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run

theorem sendDequeue_retains (records : List HiddenRecord) (pid : PeerId) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (TimerDiscipline.sendWorkerDequeue pid) := by
  unfold TimerDiscipline.sendWorkerDequeue
  apply preserves_bind (native_product records _ (native_modifyDev records _))
  intro _
  apply preserves_bind (native_product records _ (native_getPeer records pid))
  intro p
  split
  · apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
  · apply preserves_bind (native_product records _ (native_getDev records))
    intro d
    exact native_product records _ (native_setPeer records pid _)

theorem sendWorker_strict (records : List HiddenRecord) :
    Hoare Env.runOneSendWorker (fun w=>Tail records w.ambient.hidden)
      (fun _ w=>StrictTail records w.ambient.hidden) := by
  rw [TimerDiscipline.runOneSendWorker_source]
  apply hoare_bind _ _ (sendSelect_retains records)
  intro selected
  apply hoare_bind _ _ (sendDequeue_retains records selected.2)
  intro _
  exact runWorker_strict records .sendWorker _
    (native_product records _ (handshakeSendWorker_retains records selected.2))

end Leanux.Proofs.WG.Progress.RecordSuffix
