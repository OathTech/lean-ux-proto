import Leanux.Proofs.WG.TimerDiscipline.HookInitiationClaims
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource
import Leanux.Proofs.WG.Noise.DriverTagDeferredSource
import Leanux.Proofs.WG.Queues.RxWaitAppends

/-! Actual selected send-worker invocation and the existing deferred send
factory. The complete single-worker contract has no callback premise; the
outer send loop explicitly awaits a hook-aware scheduler observer. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal.SendEnvironment
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Queues

theorem quiet {α : Type} (action : Leanux.M α) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (liftPrefix action) :=
  PrefixEnsures.preserves (PrefixEnsures.lift action (fun _ _ hi=>hi)
    (fun _ _ _ _ hi _=>hi))

def one : PrefixM Receipt Unit := do
  let selected ← liftPrefix sendWorkerSelection
  liftPrefix (sendWorkerDequeue selected.2)
  runWorkerPrefix .sendWorker (liftWGObserver (Initiation.workerObserved selected.2))

theorem one_erases : ErasesPrefix one Env.runOneSendWorker := by
  rw [runOneSendWorker_source]
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun selected =>
    erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
      runWorkerPrefix_erases .sendWorker (liftWGObserver_erases (Initiation.worker_erases selected.2))))

theorem one_preserves :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory one := by
  exact (quiet _).bind (fun selected => (quiet _).bind (fun _ =>
    runWorkerPrefix_preserves (I := fun h _=>ValidHistory h) (S := ValidHistory) (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) .sendWorker
      (Initiation.worker_preserves selected.2).liftWGObserver.preserves))

theorem one_appends : Appends one :=
  (Appends.lift _).bind (fun selected => (Appends.lift _).bind (fun _ =>
    (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runWorker_appends)
      .sendWorker (Initiation.worker_appends selected.2).liftWGObserver))

/-- Only sendOne is used by Deferred.sendWith. The remaining fields fill the
existing generic record and are not invoked by this send-loop instance. -/
def hooks : Noise.DriverTags.Deferred.Hooks Receipt :=
  ⟨one,liftPrefix Env.runOneClearWorker,
    fun w pid timer entry prior=>liftPrefix (timerDispatchUnit w pid timer entry prior),
    fun j=>liftPrefix (RxHistory.placeholderTimerPassSource j)⟩

def allWith (schedule : PrefixM Receipt Unit) : PrefixM Receipt Unit :=
  Noise.DriverTags.Deferred.sendWith hooks schedule

theorem allWith_erases (schedule : PrefixM Receipt Unit)
    (erases : ErasesPrefix schedule (Env.schedule none)) :
    ErasesPrefix (allWith schedule) Env.runSendWorkers :=
  Noise.DriverTags.Deferred.send_erases hooks
    ⟨one_erases,erasesPrefix_lift _,fun _ _ _ _ _=>erasesPrefix_lift _,fun _=>erasesPrefix_lift _⟩
      schedule erases

theorem allWith_preserves (schedule : PrefixM Receipt Unit)
    (keeps : PrefixPreserves (fun h _=>ValidHistory h) ValidHistory schedule) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (allWith schedule) :=
  Noise.DriverTags.Deferred.send_preserves (I := fun h _=>ValidHistory h) (S := ValidHistory) (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) hooks
    ⟨one_preserves,quiet _,fun _ _ _ _ _=>quiet _,fun _=>quiet _⟩ schedule keeps

theorem allWith_appends (schedule : PrefixM Receipt Unit) (appends : Appends schedule) :
    Appends (allWith schedule) := by
  unfold allWith Noise.DriverTags.Deferred.sendWith
  repeat' first
    | exact appends
    | exact one_appends
    | exact Appends.lift _
    | exact Appends.pure _
    | apply Appends.range
    | apply Appends.bind
    | split
    | (intro x; try dsimp only)

end Leanux.Proofs.WG.TimerDiscipline.HookJournal.SendEnvironment
