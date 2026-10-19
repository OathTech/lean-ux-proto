import Leanux.Proofs.WG.Progress.CommittedRunSource
import Leanux.Proofs.WG.Noise.DriverTagDeferredSource

/-! The existing deferred factories with the actual committed-run scheduler.
Only scheduler activation calls emit receipts; the old atoms retain their
original executions and discard their separate private journals. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Deferred
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes
open RxHistory.DeferredSource

def crypt : PrefixM Receipt Unit := cryptWith (CommittedRuns.schedule none)
def send : PrefixM Receipt Unit := sendWith (fun {_} a=>old a) (CommittedRuns.schedule none)
def afterXmit : PrefixM Receipt Unit := afterXmitWith (fun {_} a=>old a) crypt send
def timers (j : UInt64) : PrefixM Receipt Bool := timersWith (fun {_} a=>old a) crypt j
def placeholder (j : UInt64) : PrefixM Receipt Unit := placeholderWith (fun {_} a=>old a) crypt send j
def idle : PrefixM Receipt Unit := idleWith (fun {_} a=>old a) timers placeholder
def afterAdvance : PrefixM Receipt Unit := afterAdvanceWith (fun {_} a=>old a) timers placeholder
def deferred (call : EnvDeferredCall) : PrefixM Receipt call.Result :=
  deferredWith (fun {_} a=>old a) crypt send afterXmit timers placeholder idle afterAdvance call

theorem atoms : AtomContracts (fun h _=>ValidHistory h) ValidHistory (fun {_} a=>old a) := by
  constructor
  all_goals intros; exact lift_preserves _

theorem crypt_preserves : PrefixPreserves (fun h _=>ValidHistory h) ValidHistory crypt :=
  RxHistory.DeferredSource.crypt_preserves
    (I := fun h _=>ValidHistory h) (S := ValidHistory) (fun _ _ h=>h) (fun _ _ _ _ h=>h)
    _ (CommittedRuns.schedule_preserves none)

theorem send_preserves : PrefixPreserves (fun h _=>ValidHistory h) ValidHistory send :=
  RxHistory.DeferredSource.send_preserves
    (I := fun h _=>ValidHistory h) (S := ValidHistory) (fun _ _ h=>h) (fun _ _ _ _ h=>h)
    _ atoms _ (CommittedRuns.schedule_preserves none)

theorem afterXmit_preserves : PrefixPreserves (fun h _=>ValidHistory h) ValidHistory afterXmit :=
  RxHistory.DeferredSource.afterXmit_preserves
    (I := fun h _=>ValidHistory h) (S := ValidHistory) (fun _ _ h=>h) (fun _ _ _ _ h=>h)
    _ atoms _ crypt_preserves _ send_preserves

theorem timers_preserves (j : UInt64) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (timers j) :=
  RxHistory.DeferredSource.timers_preserves
    (I := fun h _=>ValidHistory h) (S := ValidHistory) (fun _ _ h=>h) (fun _ _ _ _ h=>h)
    _ atoms _ crypt_preserves j

theorem placeholder_preserves (j : UInt64) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (placeholder j) :=
  RxHistory.DeferredSource.placeholder_preserves
    (I := fun h _=>ValidHistory h) (S := ValidHistory) (fun _ _ h=>h) (fun _ _ _ _ h=>h)
    _ atoms _ crypt_preserves _ send_preserves j

theorem idle_preserves : PrefixPreserves (fun h _=>ValidHistory h) ValidHistory idle :=
  RxHistory.DeferredSource.idle_preserves
    (I := fun h _=>ValidHistory h) (S := ValidHistory) (fun _ _ h=>h) (fun _ _ _ _ h=>h)
    _ atoms _ timers_preserves _ placeholder_preserves

theorem afterAdvance_preserves : PrefixPreserves (fun h _=>ValidHistory h) ValidHistory afterAdvance :=
  RxHistory.DeferredSource.afterAdvance_preserves
    (I := fun h _=>ValidHistory h) (S := ValidHistory) (fun _ _ h=>h) (fun _ _ _ _ h=>h)
    _ atoms _ timers_preserves _ placeholder_preserves

theorem deferred_preserves (call : EnvDeferredCall) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (deferred call) :=
  RxHistory.DeferredSource.deferred_preserves _ atoms _ _ _ _ _ _ _
    crypt_preserves send_preserves afterXmit_preserves timers_preserves placeholder_preserves
    idle_preserves afterAdvance_preserves call

theorem old_erases {E α : Type} (observed : PrefixM E α) (native : Leanux.M α)
    (erase : ErasesPrefix observed native) : ErasesPrefix (old observed) native := by
  rw [old_eq observed native erase]
  exact erasesPrefix_lift _

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

theorem crypt_erases : ErasesPrefix crypt Env.runCryptWorkers :=
  Noise.DriverTags.Deferred.crypt_erases _ (CommittedRuns.schedule_erases none)

theorem send_erases : ErasesPrefix send Env.runSendWorkers := by
  unfold send
  rw [← Noise.DriverTags.Deferred.send_source (fun {_} a=>old a) (CommittedRuns.schedule none)]
  exact Noise.DriverTags.Deferred.send_erases _ hooks_erases _ (CommittedRuns.schedule_erases none)

theorem afterXmit_erases : ErasesPrefix afterXmit Env.afterXmit :=
  Noise.DriverTags.Deferred.afterXmit_erases _ quiet_erases _ _ crypt_erases send_erases

theorem timers_erases (j : UInt64) : ErasesPrefix (timers j) (Env.runTimers j) := by
  unfold timers
  rw [← Noise.DriverTags.Deferred.timers_source (fun {_} a=>old a) crypt j]
  exact Noise.DriverTags.Deferred.timers_erases _ quiet_erases _ hooks_erases _ crypt_erases j

theorem placeholder_erases (j : UInt64) :
    ErasesPrefix (placeholder j) (Env.runTimersPlaceholder j) := by
  unfold placeholder
  rw [← Noise.DriverTags.Deferred.placeholder_source (fun {_} a=>old a) crypt send j]
  exact Noise.DriverTags.Deferred.placeholder_erases _ quiet_erases _ hooks_erases _ _
    crypt_erases send_erases j

theorem idle_erases : ErasesPrefix idle Env.idleTimers :=
  Noise.DriverTags.Deferred.idle_erases _ quiet_erases _ _ timers_erases placeholder_erases

theorem afterAdvance_erases : ErasesPrefix afterAdvance Env.afterAdvance :=
  Noise.DriverTags.Deferred.afterAdvance_erases _ quiet_erases _ _ timers_erases placeholder_erases

theorem deferred_erases (call : EnvDeferredCall) : ErasesPrefix (deferred call) call.original := by
  unfold deferred
  rw [← Noise.DriverTags.Deferred.deferred_source (fun {_} a=>old a)
    crypt send afterXmit timers placeholder idle afterAdvance call]
  exact Noise.DriverTags.Deferred.deferred_erases _ quiet_erases _ hooks_erases _ _ _ _ _ _ _
    crypt_erases send_erases afterXmit_erases timers_erases placeholder_erases
    idle_erases afterAdvance_erases call

end Leanux.Proofs.WG.Progress.CommittedRuns.Deferred
