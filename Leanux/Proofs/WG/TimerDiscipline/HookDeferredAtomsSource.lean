import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerSource
import Leanux.Proofs.WG.Noise.DriverTagDeferredSource

/-! The unchanged access/guard atoms retain their actual native outcomes.
Only the audit journal is discarded. Timer and clear callbacks contain no
timer-hook invocation; their later scheduled work remains explicit. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookDeferred
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes
open HookScheduler
variable {E : Type}

theorem old_erases {α : Type} (observer : RxHistory.Obs α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action) :
    ErasesPrefix (HookScheduler.old (E:=E) observer) action := by
  rw [HookScheduler.old_eq observer action erases]
  exact erasesPrefix_lift _

theorem quiet_atoms (S : List E → Prop) :
    Noise.DriverTags.Deferred.QuietAtoms (fun h _=>S h) S
      (fun {_} a=>HookScheduler.old a) := by
  constructor
  all_goals intros; exact HookScheduler.quiet S _

theorem quiet_erases :
    Noise.DriverTags.Deferred.QuietErases (fun {_} a=>HookScheduler.old (E:=E) a) := by
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

/-- The send callback is committed and observed. The remaining callbacks run
the exact native clear/timer actions, which only queue later hook-bearing work. -/
def hooks (sendOne : PrefixM E Unit) : Noise.DriverTags.Deferred.Hooks E :=
  ⟨sendOne,liftPrefix Env.runOneClearWorker,
    fun w pid timer entry prior=>liftPrefix (timerDispatchUnit w pid timer entry prior),
    fun j=>liftPrefix (RxHistory.placeholderTimerPassSource j)⟩

theorem hooks_erases (sendOne : PrefixM E Unit)
    (erases : ErasesPrefix sendOne Env.runOneSendWorker) :
    Noise.DriverTags.Deferred.HookErases (hooks sendOne) :=
  ⟨erases,erasesPrefix_lift _,fun _ _ _ _ _=>erasesPrefix_lift _,fun _=>erasesPrefix_lift _⟩

structure StateLeaves (I : List E → World → Prop) (S : List E → Prop) : Prop where
  quiet : Noise.DriverTags.Deferred.QuietAtoms I S (fun {_} a => HookScheduler.old a)
  clearOne : PrefixPreserves I S (liftPrefix Env.runOneClearWorker)
  timer : ∀ w pid timer entry prior,
    PrefixPreserves I S (liftPrefix (timerDispatchUnit w pid timer entry prior))
  placeholder : ∀ j, PrefixPreserves I S (liftPrefix (RxHistory.placeholderTimerPassSource j))

theorem hooks_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (leaves : StateLeaves I S) (sendOne : PrefixM E Unit)
    (keeps : PrefixPreserves I S sendOne) :
    Noise.DriverTags.Deferred.HookContracts I S (hooks sendOne) :=
  ⟨keeps,leaves.clearOne,leaves.timer,leaves.placeholder⟩

theorem history_leaves (S : List E → Prop) : StateLeaves (fun h _ => S h) S :=
  ⟨quiet_atoms S,HookScheduler.quiet S _,fun _ _ _ _ _ => HookScheduler.quiet S _,
    fun _ => HookScheduler.quiet S _⟩

theorem hooks_preserves (S : List E → Prop) (sendOne : PrefixM E Unit)
    (keeps : PrefixPreserves (fun h _=>S h) S sendOne) :
    Noise.DriverTags.Deferred.HookContracts (fun h _=>S h) S (hooks sendOne) :=
  hooks_preserves_state (history_leaves S) sendOne keeps

end Leanux.Proofs.WG.TimerDiscipline.HookDeferred
