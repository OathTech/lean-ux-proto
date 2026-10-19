import Leanux.Proofs.WG.TimerDiscipline.EpisodeJournalSource

/-! Existing deferred factories retain every reached runTimers call. Other callbacks contain no runTimers invocation; placeholder passes have a distinct source and are not reported as wheel episodes. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes

def old {E α : Type} (observer : PrefixM E α) : PrefixM Receipt α :=
  liftPrefix (fun entry => (runPrefix observer entry []).1)

theorem old_eq {E α : Type} (observer : PrefixM E α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action) : old observer = liftPrefix action := by
  apply congrArg liftPrefix
  funext entry
  exact erases entry []

theorem old_erases {E α : Type} (observer : PrefixM E α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action) : ErasesPrefix (old observer) action := by
  rw [old_eq observer action erases]
  exact erasesPrefix_lift _

theorem lift_preserves {α : Type} (action : Leanux.M α) :
    PrefixPreserves (fun history _=>ValidHistory history) ValidHistory (liftPrefix action) :=
  PrefixEnsures.preserves (PrefixEnsures.lift action (fun _ _ prior=>prior)
    (fun _ _ _ _ prior _=>prior))

open RxHistory.DeferredSource

theorem atoms : AtomContracts (fun h _=>ValidHistory h) ValidHistory (fun {_} a=>old a) := by
  constructor
  all_goals intros; exact lift_preserves _

theorem quiet_erases : Noise.DriverTags.Deferred.QuietErases (fun {_} a=>old a) := by
  constructor
  · intro what queues
    exact old_erases _ _ (RxHistory.mixed_erases (requireDrainedPrefix_erases what queues))
  · exact old_erases _ _ (RxHistory.audit_erases getDevSavedAudit_erases)
  · intro d j
    exact old_erases _ _ (RxHistory.audit_erases (wheelNextDueAudit_erases d j))
  · intro b
    exact old_erases _ _ (RxHistory.audit_erases (requireStepCompleteAudit_erases b))
  · intro j
    exact old_erases _ _ (RxHistory.audit_erases (requireNothingDueAudit_erases j))
  · exact old_erases _ _ (RxHistory.mixed_erases requireIdleDevicePrefix_erases)
  · exact old_erases _ _ (RxHistory.audit_erases (erasesPrefix_lift _))
  · intro timer
    exact old_erases _ _ (RxHistory.audit_erases (erasesPrefix_lift _))
  · intro ticks
    exact old_erases _ _ (RxHistory.audit_erases (advanceAudit_erases ticks))

theorem hooks_erases : Noise.DriverTags.Deferred.HookErases
    (Noise.DriverTags.Deferred.originalHooks (fun {_} a=>old a)) := by
  constructor
  · exact old_erases _ _ (RxHistory.audit_erases runOneSendWorkerAudit_erases)
  · exact old_erases _ _ (RxHistory.audit_erases runOneClearWorkerAudit_erases)
  · intro w pid timer entry prior
    exact old_erases _ _ (RxHistory.audit_erases (timerDispatchAudit_erases w pid timer entry prior))
  · intro j
    exact old_erases _ _ (RxHistory.audit_erases (RxHistory.placeholderTimerPass_erases j))

def idle : PrefixM Receipt Unit :=
  idleWith (fun {_} a=>old a) call (fun j=>liftPrefix (Env.runTimersPlaceholder j))

def afterAdvance : PrefixM Receipt Unit :=
  afterAdvanceWith (fun {_} a=>old a) call (fun j=>liftPrefix (Env.runTimersPlaceholder j))

def deferred (c : EnvDeferredCall) : PrefixM Receipt c.Result :=
  deferredWith (fun {_} a=>old a) (liftPrefix Env.runCryptWorkers)
    (liftPrefix Env.runSendWorkers) (liftPrefix Env.afterXmit)
    call (fun j=>liftPrefix (Env.runTimersPlaceholder j)) idle afterAdvance c

theorem idle_erases : ErasesPrefix idle Env.idleTimers :=
  Noise.DriverTags.Deferred.idle_erases _ quiet_erases _ _
    call_erases (fun _=>erasesPrefix_lift _)

theorem afterAdvance_erases : ErasesPrefix afterAdvance Env.afterAdvance :=
  Noise.DriverTags.Deferred.afterAdvance_erases _ quiet_erases _ _
    call_erases (fun _=>erasesPrefix_lift _)

theorem deferred_erases (c : EnvDeferredCall) : ErasesPrefix (deferred c) c.original := by
  unfold deferred
  rw [← Noise.DriverTags.Deferred.deferred_source]
  exact Noise.DriverTags.Deferred.deferred_erases _ quiet_erases _ hooks_erases _ _ _ _ _ _ _
    (erasesPrefix_lift _) (erasesPrefix_lift _) (erasesPrefix_lift _) call_erases
    (fun _=>erasesPrefix_lift _) idle_erases afterAdvance_erases c

theorem idle_preserves :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory idle :=
  RxHistory.DeferredSource.idle_preserves
    (I := fun h _=>ValidHistory h) (S := ValidHistory)
    (fun _ _ h=>h) (fun _ _ _ _ h=>h) _ atoms _
    call_preserves _ (fun _=>lift_preserves _)

theorem afterAdvance_preserves :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory afterAdvance :=
  RxHistory.DeferredSource.afterAdvance_preserves
    (I := fun h _=>ValidHistory h) (S := ValidHistory)
    (fun _ _ h=>h) (fun _ _ _ _ h=>h) _ atoms _
    call_preserves _ (fun _=>lift_preserves _)

theorem deferred_preserves (c : EnvDeferredCall) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (deferred c) :=
  RxHistory.DeferredSource.deferred_preserves _ atoms _ _ _ _ _ _ _
    (lift_preserves _) (lift_preserves _) (lift_preserves _) call_preserves
    (fun _=>lift_preserves _) idle_preserves afterAdvance_preserves c

end Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
