import Leanux.Proofs.WG.Queues.RxEnvWorkersHistory
import Leanux.Proofs.WG.Lifetimes.EnvDeferredCalls

/-! Concrete timer callers retain every worker continuation and recorded wait
boundary. Only the literal poll-free placeholder timer pass is focused; its saved
peer scan is justified by its own getter. Reset/absence guards stay outside it. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- The original poll-free timer pass, before crypt/send processing. -/
def placeholderTimerPassSource (jHi : UInt64) : M Unit := do
  let pending := (← getDev).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let d ← getDev
    let due := Environment.dueEntries d jHi
    let first := Environment.firstDue due
    let some (_, pid, t) := first | break
    delTimer pid t
    Env.runTimerSection (← Env.timerWorker t) (WG.timerCallback pid t)

/-- Same pass with the existing R2 saved-map accesses. Each iteration derives
its scan premise from its actual getter; no saved-map premise escapes this block. -/
def placeholderTimerPassAudit (jHi : UInt64) : AuditM Unit := do
  let pending := (← liftPrefix getDev).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let d ← getDevSavedAudit
    let due ← dueEntriesAudit d jHi
    let first := Environment.firstDue due
    let some (_, pid, t) := first | break
    auditFocus (delTimerPrefix pid t)
    runTimerSectionAudit (← liftPrefix (Env.timerWorker t)) (auditFocus (timerCallbackPrefix pid t))

theorem placeholderTimerPass_erases (jHi : UInt64) :
    ErasesPrefix (placeholderTimerPassAudit jHi) (placeholderTimerPassSource jHi) := by
  unfold placeholderTimerPassAudit placeholderTimerPassSource
  repeat' first
    | with_reducible exact getDevSavedAudit_erases
    | with_reducible apply erasesPrefix_bind_pure (dueEntriesAudit_erases _ _)
    | with_reducible exact auditFocus_erases (delTimerPrefix_erases _ _)
    | with_reducible exact auditFocus_erases (timerCallbackPrefix_erases _ _)
    | with_reducible apply runTimerSectionAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem placeholderTimerPass_preserves (jHi : UInt64) :
    PrefixPreserves AuditInv AuditSafe (placeholderTimerPassAudit jHi) := by
  unfold placeholderTimerPassAudit
  repeat' first
    | apply PrefixEnsures.bind getDevSavedAudit_spec
    | (apply PrefixEnsures.bind (dueEntriesAudit_spec _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | with_reducible exact auditFocus_preserves (AmbientContracts.drop (delTimerPrefix_spec allocationAmbient (fun _ => True) _ _))
    | exact auditFocus_preserves (timerCallbackPrefix_preserves allocationAmbient allocationTx allocationTimerQueue _ _)
    | with_reducible apply runTimerSectionAudit_preserves
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ (timerWorker_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def runTimers (jHi : UInt64) : Obs Bool := do
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  if (← liftPrefix getK).wg.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  for _ in [0:(← liftPrefix recordBudget)] do
    let some site ← liftPrefix Env.peekNextSite | break
    let d ← liftPrefix getDev
    if let some w := Env.timerSectionOf site then
      if w == .clearPeerWorker then
        if d.clearWorkQueue.isEmpty then break
        audit runOneClearWorkerAudit
      else
        audit (fireTimerAudit w jHi)
        fired := true
    else if !fired then break
    else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then audit runOneSendWorkerAudit
    else
      runCryptWorkers
      if (← liftPrefix Env.peekNextSite) == some site then break
  if fired then
    liftPrefix Env.deliverSent
    let d ← liftPrefix getDev
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      liftPrefix (unsupported "work a timer queued outlived the guest's wait")
  return fired

theorem runTimers_erases (jHi : UInt64) : ErasesPrefix (runTimers jHi) (Env.runTimers jHi) := by
  unfold runTimers Env.runTimers
  repeat' first
    | with_reducible exact audit_erases runOneClearWorkerAudit_erases
    | with_reducible exact audit_erases (fireTimerAudit_erases _ _)
    | with_reducible exact audit_erases runOneSendWorkerAudit_erases
    | with_reducible exact runCryptWorkers_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runTimers_preserves (jHi : UInt64) : PrefixPreserves BoundaryInv BoundarySafe (runTimers jHi) := by
  unfold runTimers
  repeat' first
    | with_reducible exact audit_preserves _ runOneClearWorkerAudit_preserves
    | with_reducible exact audit_preserves _ (fireTimerAudit_preserves _ _)
    | with_reducible exact audit_preserves _ runOneSendWorkerAudit_preserves
    | with_reducible exact runCryptWorkers_preserves
    | with_reducible exact boundaryLift_kernel _ getDev_sameKernel
    | with_reducible exact boundaryLift_kernel _ deliverSent_sameKernel
    | with_reducible exact boundaryLift_kernel _ peekNextSite_sameKernel
    | with_reducible exact boundaryLift_kernel _ recordBudget_sameKernel
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runTimers_projects (jHi : UInt64) :
    ProjectsUnder AuditInv auditEvent (runTimers jHi) (runTimersAudit jHi) := by
  unfold runTimers runTimersAudit
  repeat' first
    | with_reducible exact audit_projects runOneClearWorkerAudit_preserves
    | with_reducible exact audit_projects (fireTimerAudit_preserves _ _)
    | with_reducible exact audit_projects runOneSendWorkerAudit_preserves
    | with_reducible exact runCryptWorkers_projects
    | with_reducible exact runOneClearWorkerAudit_preserves
    | with_reducible exact fireTimerAudit_preserves _ _
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible apply projectsUnder_range
    | with_reducible apply projectsUnder_bind
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | exact auditLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def placeholderSourceWithPass (jHi : UInt64) : M Unit := do
  modify fun w => { w with queuedThisCall := [] }
  if (← getK).wg.isNone then return   -- L: no wg0, no timers [AGENT, int-dl merge]
  -- the filter's own loop (review item 7): one turn per pending timer at most
  placeholderTimerPassSource jHi
  Env.runCryptWorkers
  Env.runSendWorkers
  for _ in [0:(← getDev).clearWorkQueue.length + 1] do
    if (← getDev).clearWorkQueue.isEmpty then break
    Env.runOneClearWorker

def placeholderAuditWithPass (jHi : UInt64) : AuditM Unit := do
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  if (← liftPrefix getK).wg.isNone then return
  placeholderTimerPassAudit jHi
  runCryptWorkersAudit
  runSendWorkersAudit
  for _ in [0:(← liftPrefix getDev).clearWorkQueue.length + 1] do
    if (← liftPrefix getDev).clearWorkQueue.isEmpty then break
    runOneClearWorkerAudit

theorem placeholderSource_eq (jHi : UInt64) :
    placeholderSourceWithPass jHi = Env.runTimersPlaceholder jHi := by
  rw [← Environment.runTimersPlaceholderSource_eq]
  simp only [placeholderSourceWithPass, placeholderTimerPassSource,
    Environment.runTimersPlaceholderSource, bind_assoc, pure_bind]
  rfl

theorem placeholderAudit_eq (jHi : UInt64) :
    placeholderAuditWithPass jHi = runTimersPlaceholderAudit jHi := by
  simp only [placeholderAuditWithPass, placeholderTimerPassAudit,
    runTimersPlaceholderAudit, bind_assoc, pure_bind]
  rfl

/-- The reset and absent-device return precede the focused pass; its worker
suffix remains concrete and observes every poll it actually reaches. -/
def runTimersPlaceholder (jHi : UInt64) : Obs Unit := do
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  if (← liftPrefix getK).wg.isNone then return
  audit (placeholderTimerPassAudit jHi)
  runCryptWorkers
  runSendWorkers
  for _ in [0:(← liftPrefix getDev).clearWorkQueue.length + 1] do
    if (← liftPrefix getDev).clearWorkQueue.isEmpty then break
    audit runOneClearWorkerAudit

theorem runTimersPlaceholder_erases (jHi : UInt64) :
    ErasesPrefix (runTimersPlaceholder jHi) (Env.runTimersPlaceholder jHi) := by
  rw [← placeholderSource_eq]
  unfold runTimersPlaceholder placeholderSourceWithPass
  repeat' first
    | with_reducible exact audit_erases (placeholderTimerPass_erases _)
    | with_reducible exact runCryptWorkers_erases
    | with_reducible exact runSendWorkers_erases
    | with_reducible exact audit_erases runOneClearWorkerAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runTimersPlaceholder_preserves (jHi : UInt64) :
    PrefixPreserves BoundaryInv BoundarySafe (runTimersPlaceholder jHi) := by
  unfold runTimersPlaceholder
  repeat' first
    | with_reducible exact audit_preserves _ (placeholderTimerPass_preserves _)
    | with_reducible exact runCryptWorkers_preserves
    | with_reducible exact runSendWorkers_preserves
    | with_reducible exact audit_preserves _ runOneClearWorkerAudit_preserves
    | with_reducible exact boundaryLift_kernel _ getDev_sameKernel
    | with_reducible exact boundaryLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact boundaryLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runTimersPlaceholder_projects (jHi : UInt64) :
    ProjectsUnder AuditInv auditEvent (runTimersPlaceholder jHi) (runTimersPlaceholderAudit jHi) := by
  rw [← placeholderAudit_eq]
  unfold runTimersPlaceholder placeholderAuditWithPass
  repeat' first
    | with_reducible exact audit_projects (placeholderTimerPass_preserves _)
    | with_reducible exact runCryptWorkers_projects
    | with_reducible exact runSendWorkers_projects
    | with_reducible exact audit_projects runOneClearWorkerAudit_preserves
    | with_reducible exact placeholderTimerPass_preserves _
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneClearWorkerAudit_preserves
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible apply projectsUnder_range
    | with_reducible apply projectsUnder_bind
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact auditLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def idleTimers : Obs Unit := do
  let w ← liftPrefix get
  if w.hidden.isNone then
    discard <| runTimers (w.jiffiesLast.getD 0 + w.timing.traceBound.toUInt64 + w.timing.advanceWait.toUInt64)
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation"))
  discard <| runTimers jEnd
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modify fun w => {w with jiffiesLast := some j})

theorem idleTimers_erases : ErasesPrefix idleTimers Env.idleTimers := by
  unfold idleTimers Env.idleTimers
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact runTimers_erases _
    | with_reducible exact runTimersPlaceholder_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem idleTimers_preserves : PrefixPreserves BoundaryInv BoundarySafe idleTimers := by
  unfold idleTimers
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact runTimers_preserves _
    | with_reducible exact runTimersPlaceholder_preserves _
    | with_reducible exact boundaryLift_kernel _ getDev_sameKernel
    | with_reducible exact boundaryLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact boundaryLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem idleTimers_projects : ProjectsUnder AuditInv auditEvent idleTimers idleTimersAudit := by
  unfold idleTimers idleTimersAudit
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact runTimers_projects _
    | with_reducible exact runTimersPlaceholder_projects _
    | with_reducible exact runTimersAudit_preserves _
    | with_reducible exact runTimersPlaceholderAudit_preserves _
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible apply projectsUnder_bind
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact auditLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def afterAdvance : Obs Unit := do
  let w ← liftPrefix get
  if w.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + w.timing.advanceWait.toUInt64
    if w.hiddenPlaceholders then runTimersPlaceholder jHi else discard <| runTimers jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance"))
  discard <| runTimers jEnd
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modify fun w => {w with jiffiesLast := some j})

theorem afterAdvance_erases : ErasesPrefix afterAdvance Env.afterAdvance := by
  unfold afterAdvance Env.afterAdvance
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact runTimers_erases _
    | with_reducible exact runTimersPlaceholder_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterAdvance_preserves : PrefixPreserves BoundaryInv BoundarySafe afterAdvance := by
  unfold afterAdvance
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact runTimers_preserves _
    | with_reducible exact runTimersPlaceholder_preserves _
    | with_reducible exact boundaryLift_kernel _ getDev_sameKernel
    | with_reducible exact boundaryLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact boundaryLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterAdvance_projects : ProjectsUnder AuditInv auditEvent afterAdvance afterAdvanceAudit := by
  unfold afterAdvance afterAdvanceAudit
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact runTimers_projects _
    | with_reducible exact runTimersPlaceholder_projects _
    | with_reducible exact runTimersAudit_preserves _
    | with_reducible exact runTimersPlaceholderAudit_preserves _
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible apply projectsUnder_bind
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact auditLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

/-- Every deferred-call constructor is explicit. Only inspected poll-free
cases focus their existing audit; worker/timer cases use concrete observers. -/
def deferred : (call : EnvDeferredCall) → Obs call.Result
  | .drained what queues => audit (EnvDeferredCall.observed (.drained what queues))
  | .idleDevice => audit (EnvDeferredCall.observed .idleDevice)
  | .noCrypt => audit (EnvDeferredCall.observed .noCrypt)
  | .crypt => runCryptWorkers
  | .sendOne => audit (EnvDeferredCall.observed .sendOne)
  | .clearOne => audit (EnvDeferredCall.observed .clearOne)
  | .sendAll => runSendWorkers
  | .afterXmit => afterXmit
  | .timerWorker timer => audit (EnvDeferredCall.observed (.timerWorker timer))
  | .fire worker jHi => audit (EnvDeferredCall.observed (.fire worker jHi))
  | .timers jHi => runTimers jHi
  | .placeholder jHi => runTimersPlaceholder jHi
  | .idle => idleTimers
  | .advance ticks => audit (EnvDeferredCall.observed (.advance ticks))
  | .afterAdvance => afterAdvance

theorem deferred_erases (call : EnvDeferredCall) :
    ErasesPrefix (deferred call) call.original := by
  cases call with
  | drained what queues => exact audit_erases (EnvDeferredCall.erases (.drained what queues))
  | idleDevice => exact audit_erases (EnvDeferredCall.erases .idleDevice)
  | noCrypt => exact audit_erases (EnvDeferredCall.erases .noCrypt)
  | crypt => exact runCryptWorkers_erases
  | sendOne => exact audit_erases (EnvDeferredCall.erases .sendOne)
  | clearOne => exact audit_erases (EnvDeferredCall.erases .clearOne)
  | sendAll => exact runSendWorkers_erases
  | afterXmit => exact afterXmit_erases
  | timerWorker timer => exact audit_erases (EnvDeferredCall.erases (.timerWorker timer))
  | fire worker jHi => exact audit_erases (EnvDeferredCall.erases (.fire worker jHi))
  | timers jHi => exact runTimers_erases jHi
  | placeholder jHi => exact runTimersPlaceholder_erases jHi
  | idle => exact idleTimers_erases
  | advance ticks => exact audit_erases (EnvDeferredCall.erases (.advance ticks))
  | afterAdvance => exact afterAdvance_erases

theorem deferred_projects (call : EnvDeferredCall) :
    ProjectsUnder AuditInv auditEvent (deferred call) call.observed := by
  cases call with
  | drained what queues => exact audit_projects (EnvDeferredCall.preserves (.drained what queues))
  | idleDevice => exact audit_projects (EnvDeferredCall.preserves .idleDevice)
  | noCrypt => exact audit_projects (EnvDeferredCall.preserves .noCrypt)
  | crypt => exact runCryptWorkers_projects
  | sendOne => exact audit_projects (EnvDeferredCall.preserves .sendOne)
  | clearOne => exact audit_projects (EnvDeferredCall.preserves .clearOne)
  | sendAll => exact runSendWorkers_projects
  | afterXmit => exact afterXmit_projects
  | timerWorker timer => exact audit_projects (EnvDeferredCall.preserves (.timerWorker timer))
  | fire worker jHi => exact audit_projects (EnvDeferredCall.preserves (.fire worker jHi))
  | timers jHi => exact runTimers_projects jHi
  | placeholder jHi => exact runTimersPlaceholder_projects jHi
  | idle => exact idleTimers_projects
  | advance ticks => exact audit_projects (EnvDeferredCall.preserves (.advance ticks))
  | afterAdvance => exact afterAdvance_projects

theorem deferred_preserves (call : EnvDeferredCall) :
    PrefixPreserves BoundaryInv BoundarySafe (deferred call) := by
  cases call with
  | drained what queues => exact audit_preserves _ (EnvDeferredCall.preserves (.drained what queues))
  | idleDevice => exact audit_preserves _ (EnvDeferredCall.preserves .idleDevice)
  | noCrypt => exact audit_preserves _ (EnvDeferredCall.preserves .noCrypt)
  | crypt => exact runCryptWorkers_preserves
  | sendOne => exact audit_preserves _ (EnvDeferredCall.preserves .sendOne)
  | clearOne => exact audit_preserves _ (EnvDeferredCall.preserves .clearOne)
  | sendAll => exact runSendWorkers_preserves
  | afterXmit => exact afterXmit_preserves
  | timerWorker timer => exact audit_preserves _ (EnvDeferredCall.preserves (.timerWorker timer))
  | fire worker jHi => exact audit_preserves _ (EnvDeferredCall.preserves (.fire worker jHi))
  | timers jHi => exact runTimers_preserves jHi
  | placeholder jHi => exact runTimersPlaceholder_preserves jHi
  | idle => exact idleTimers_preserves
  | advance ticks => exact audit_preserves _ (EnvDeferredCall.preserves (.advance ticks))
  | afterAdvance => exact afterAdvance_preserves

end Leanux.Proofs.WG.Queues.RxHistory
