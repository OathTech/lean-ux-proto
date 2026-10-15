import Leanux.Proofs.WG.Queues.RxScheduleHistory
import Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit

/-! Deferred environment callers use the concrete stamped scheduler. Focused
send/drain leaves are poll-free in the source; their original access observations
and failure prefixes remain part of the same incoming audit history. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def runCryptWorkers : Obs Unit := do
  schedule
  liftPrefix Env.deliverSent

def runSendWorkers : Obs Unit := do
  if (← liftPrefix getK).wg.isNone then return
  liftPrefix Env.requireNoCryptWork
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix getDev).sendWorkQueue.isEmpty then liftPrefix Env.deliverSent; return
    audit runOneSendWorkerAudit
    schedule
  liftPrefix (budgetExhausted "the send work queue")

def afterXmit : Obs Unit := do
  let some d := (← liftPrefix getK).wg | return
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    liftPrefix (unsupported "wg_xmit queued crypt work and a handshake (their order)")
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  if crypt then
    runCryptWorkers
    let d ← liftPrefix getDev
    mixed (requireDrainedPrefix "wg_xmit queued" [!d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  runSendWorkers

theorem runCryptWorkers_erases : ErasesPrefix runCryptWorkers Env.runCryptWorkers := by
  unfold runCryptWorkers Env.runCryptWorkers
  repeat' first
    | with_reducible exact schedule_erases _
    | with_reducible exact audit_erases runOneSendWorkerAudit_erases
    | with_reducible exact mixed_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runCryptWorkers_preserves : PrefixPreserves BoundaryInv BoundarySafe runCryptWorkers := by
  unfold runCryptWorkers
  repeat' first
    | with_reducible exact schedule_preserves _
    | with_reducible exact audit_preserves _ runOneSendWorkerAudit_preserves
    | with_reducible exact mixed_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact boundaryLift_kernel _ getDev_sameKernel
    | with_reducible exact boundaryLift_kernel _ deliverSent_sameKernel
    | with_reducible exact boundaryLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact boundaryLift_kernel _ recordBudget_sameKernel
    | with_reducible exact boundaryLift_kernel _ (budgetExhausted_sameKernel _)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runCryptWorkers_projects : ProjectsUnder AuditInv auditEvent runCryptWorkers runCryptWorkersAudit := by
  unfold runCryptWorkers runCryptWorkersAudit
  repeat' first
    | with_reducible exact schedule_projects _
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact audit_projects runOneSendWorkerAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact mixed_projects (requireDrainedPrefix_allocation _ _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible apply projectsUnder_range
    | with_reducible apply projectsUnder_bind
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (budgetExhausted_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runSendWorkers_erases : ErasesPrefix runSendWorkers Env.runSendWorkers := by
  unfold runSendWorkers Env.runSendWorkers
  repeat' first
    | with_reducible exact runCryptWorkers_erases
    | with_reducible exact schedule_erases _
    | with_reducible exact audit_erases runOneSendWorkerAudit_erases
    | with_reducible exact mixed_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runSendWorkers_preserves : PrefixPreserves BoundaryInv BoundarySafe runSendWorkers := by
  unfold runSendWorkers
  repeat' first
    | with_reducible exact runCryptWorkers_preserves
    | with_reducible exact schedule_preserves _
    | with_reducible exact audit_preserves _ runOneSendWorkerAudit_preserves
    | with_reducible exact mixed_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact boundaryLift_kernel _ getDev_sameKernel
    | with_reducible exact boundaryLift_kernel _ deliverSent_sameKernel
    | with_reducible exact boundaryLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact boundaryLift_kernel _ recordBudget_sameKernel
    | with_reducible exact boundaryLift_kernel _ (budgetExhausted_sameKernel _)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runSendWorkers_projects : ProjectsUnder AuditInv auditEvent runSendWorkers runSendWorkersAudit := by
  unfold runSendWorkers runSendWorkersAudit
  repeat' first
    | with_reducible exact runCryptWorkers_projects
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact schedule_projects _
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact audit_projects runOneSendWorkerAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact mixed_projects (requireDrainedPrefix_allocation _ _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible apply projectsUnder_range
    | with_reducible apply projectsUnder_bind
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (budgetExhausted_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterXmit_erases : ErasesPrefix afterXmit Env.afterXmit := by
  unfold afterXmit Env.afterXmit
  repeat' first
    | with_reducible exact runCryptWorkers_erases
    | with_reducible exact runSendWorkers_erases
    | with_reducible exact schedule_erases _
    | with_reducible exact audit_erases runOneSendWorkerAudit_erases
    | with_reducible exact mixed_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterXmit_preserves : PrefixPreserves BoundaryInv BoundarySafe afterXmit := by
  unfold afterXmit
  repeat' first
    | with_reducible exact runCryptWorkers_preserves
    | with_reducible exact runSendWorkers_preserves
    | with_reducible exact schedule_preserves _
    | with_reducible exact audit_preserves _ runOneSendWorkerAudit_preserves
    | with_reducible exact mixed_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact boundaryLift_kernel _ getDev_sameKernel
    | with_reducible exact boundaryLift_kernel _ deliverSent_sameKernel
    | with_reducible exact boundaryLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact boundaryLift_kernel _ recordBudget_sameKernel
    | with_reducible exact boundaryLift_kernel _ (budgetExhausted_sameKernel _)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterXmit_projects : ProjectsUnder AuditInv auditEvent afterXmit afterXmitAudit := by
  unfold afterXmit afterXmitAudit
  repeat' first
    | with_reducible exact runCryptWorkers_projects
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runSendWorkers_projects
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact schedule_projects _
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact audit_projects runOneSendWorkerAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact mixed_projects (requireDrainedPrefix_allocation _ _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible apply projectsUnder_range
    | with_reducible apply projectsUnder_bind
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ requireNoCryptWork_sameKernel
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (budgetExhausted_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

/-- Direct projection of the original section wrapper, including its failure
before NET_RX cleanup. The body receives the actual produced history. -/
theorem runWorker_projects (worker : Worker) {g : Obs Unit} {a : AuditM Unit}
    (hg : ProjectsUnder AuditInv auditEvent g a)
    (ha : PrefixPreserves AuditInv AuditSafe a) :
    ProjectsUnder AuditInv auditEvent (runWorkerPrefix worker g) (runWorkerPrefix worker a) := by
  unfold runWorkerPrefix
  repeat' first
    | exact hg
    | exact ha
    | exact projectsUnder_lift _ _
    | exact projectsUnder_pure _ _
    | exact auditLift_kernel _ (hidden_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | apply projectsUnder_bind
    | apply PrefixPreserves.bind
    | split
    | (intro x; try dsimp only)

end Leanux.Proofs.WG.Queues.RxHistory
