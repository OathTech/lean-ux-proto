import Leanux.Proofs.WG.Queues.RxPollCompletion
import Leanux.Proofs.WG.Queues.RxScheduleHistory

/-! Callback completion through the existing concrete NAPI, crypt-worker and
scheduler observers. This protocol depends only on the journal. Focused audit
leaves cannot create callback entries or receipts; copied consistency trials
remain behind their original audit marker and are not committed callbacks. -/
namespace Leanux.Proofs.WG.Queues.RxCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

theorem closed_safe : ∀ h (_ : World), Closed historyEvent h → CompletionPrefix historyEvent h :=
  fun _ _ hi => hi.prefix

theorem audit_quiet (a : AuditM α) : Preserves historyEvent (RxHistory.audit a) :=
  quiet (fun w h => focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent historyEvent
    (fun _ => rfl) a w h) (Appends.focus _ _ _)

theorem mixed_quiet (a : MixedM α) : Preserves historyEvent (RxHistory.mixed a) :=
  audit_quiet _

theorem napiSoftirq_preserves : Preserves historyEvent RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves closed_safe (fun _ _ _ _ hi => hi)
    (audit_quiet _) observePoll_preserves

theorem pollScheduledInline_preserves : Preserves historyEvent RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves closed_safe (fun _ _ _ _ hi => hi)
    (audit_quiet _) observePoll_preserves

theorem napiIrqExit_preserves : Preserves historyEvent RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves closed_safe (fun _ _ _ _ hi => hi)
    (audit_quiet _) napiSoftirq_preserves

macro "completion_steps" : tactic => `(tactic|
  repeat' first
    | with_reducible exact audit_quiet _
    | with_reducible exact mixed_quiet _
    | with_reducible exact lift_quiet _
    | with_reducible exact PrefixPreserves.pure closed_safe _
    | with_reducible apply PrefixPreserves.range _ _ _ closed_safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ closed_safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem encryptIteration_preserves : Preserves historyEvent RxHistory.encryptIteration :=
  PrefixPreserves.bind napiSoftirq_preserves (fun _ => mixed_quiet _)

theorem decryptStep_preserves : Preserves historyEvent RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  repeat' first
    | with_reducible exact napiSoftirq_preserves
    | with_reducible exact napiIrqExit_preserves
    | completion_steps

theorem decryptIteration_preserves : Preserves historyEvent RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ closed_safe decryptStep_preserves
  exact PrefixPreserves.bind (lift_quiet _) (fun _ => lift_quiet _)

theorem cryptAhead_preserves (pid : PeerId) : Preserves historyEvent (RxHistory.cryptAhead pid) := by
  unfold RxHistory.cryptAhead
  repeat' first
    | with_reducible exact encryptIteration_preserves
    | completion_steps

theorem activationIteration_preserves (a : Activation) :
    Preserves historyEvent (RxHistory.activationIteration a) := by
  unfold RxHistory.activationIteration
  repeat' first
    | with_reducible exact encryptIteration_preserves
    | with_reducible exact decryptIteration_preserves
    | with_reducible exact cryptAhead_preserves _
    | completion_steps

theorem activationRun_preserves (a : Activation) :
    Preserves historyEvent (RxHistory.activationRun a) := by
  unfold RxHistory.activationRun
  repeat' first
    | with_reducible exact activationIteration_preserves _
    | completion_steps

theorem dispatch_preserves (worker : Worker) : Preserves historyEvent (RxHistory.dispatch worker) := by
  unfold RxHistory.dispatch
  repeat' first
    | with_reducible exact activationRun_preserves _
    | completion_steps

/-- The actual consistency-filter audit is protocol-quiet. Its saved trial
Worlds and histories are untouched; no trial receipt enters this journal. -/
theorem schedule_preserves (stack : Option Worker) : Preserves historyEvent (RxHistory.schedule stack) := by
  unfold RxHistory.schedule
  simp only [List.find?_cons, List.find?_nil]
  repeat' first
    | with_reducible exact dispatch_preserves _
    | with_reducible exact activationRun_preserves _
    | with_reducible exact napiSoftirq_preserves
    | completion_steps

theorem nestedResched_preserves (self : Worker) : Preserves historyEvent (RxHistory.nestedResched self) := by
  unfold RxHistory.nestedResched
  apply PrefixPreserves.bind (lift_quiet _)
  intro b
  split
  · exact schedule_preserves _
  · exact PrefixPreserves.pure closed_safe _

end Leanux.Proofs.WG.Queues.RxCompletion
