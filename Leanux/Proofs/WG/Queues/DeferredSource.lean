import Leanux.Proofs.WG.Queues.SchedulerSource
import Leanux.Proofs.WG.Queues.RxEnvTimersHistory

/-! Literal deferred-worker and timer callers, with explicit committed worker
callbacks. The old embedding carries only the original poll-free audit or
access atoms; saved wheel scans, sections and end-of-wait guards stay intact. -/
namespace Leanux.Proofs.WG.Queues.RxHistory.DeferredSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open RxJoint.PollSource SchedulerSource

def cryptWith {E : Type} (schedule : PrefixM E Unit) : PrefixM E Unit := do
  schedule
  liftPrefix Env.deliverSent

def sendWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (schedule : PrefixM E Unit) : PrefixM E Unit := do
  if (← liftPrefix getWG).dev.isNone then return
  liftPrefix Env.requireNoCryptWork
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then liftPrefix Env.deliverSent; return
    old (audit runOneSendWorkerAudit)
    schedule
  liftPrefix (budgetExhausted "the send work queue")

def afterXmitWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (cryptWork sendWork : PrefixM E Unit) : PrefixM E Unit := do
  let some d := (← liftPrefix getWG).dev | return
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    liftPrefix (unsupported "wg_xmit queued crypt work and a handshake (their order)")
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if crypt then
    cryptWork
    let d ← liftPrefix (liftWG getDev)
    old (mixed (requireDrainedPrefix "wg_xmit queued" [!d.encryptQueue.empty, !d.txWorkQueue.isEmpty]))
  sendWork

def timersWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (cryptWork : PrefixM E Unit) (jPass : UInt64) : PrefixM E Bool := do
  liftPrefix (modifyWG fun w => { w with queuedThisCall := [] })
  if (← liftPrefix getWG).dev.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  let mut step : Option UInt64 := none
  for _ in [0:(← liftPrefix recordBudget)] do
    let some site ← liftPrefix Env.peekNextSite | break
    let d ← old (audit getDevSavedAudit)
    if let some w := Env.timerSectionOf site then
      if w == .clearPeerWorker then
        if let some b := step then
          old (audit (requireStepCompleteAudit b))
          step := none
        if d.clearWorkQueue.isEmpty then break
        old (audit runOneClearWorkerAudit)
      else
        let some (pid, t, we) ← old (audit (wheelNextDueAudit d jPass))
          | liftPrefix (throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jPass}"))
        old (audit (timerDispatchAudit w pid t we step))
        step := some we.bucketExpiry
        fired := true
    else
      if let some b := step then
        old (audit (requireStepCompleteAudit b))
        step := none
      if !fired then break
      else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then old (audit runOneSendWorkerAudit)
      else
        cryptWork
        if (← liftPrefix Env.peekNextSite) == some site then break
  if let some b := step then old (audit (requireStepCompleteAudit b))
  if fired then
    liftPrefix Env.deliverSent
    let d ← old (audit getDevSavedAudit)
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      liftPrefix (unsupported "work a timer queued outlived the guest's wait")
  return fired

def placeholderWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (cryptWork sendWork : PrefixM E Unit) (jHi : UInt64) : PrefixM E Unit := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getWG).dev.isNone then return
  old (audit (placeholderTimerPassAudit jHi))
  cryptWork
  sendWork
  for _ in [0:(← old (audit getDevSavedAudit)).clearWorkQueue.length + 1] do
    if (← old (audit getDevSavedAudit)).clearWorkQueue.isEmpty then break
    old (audit runOneClearWorkerAudit)

def idleWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit) : PrefixM E Unit := do
  let w ← liftPrefix getWG
  let a ← liftPrefix getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.traceBound.toUInt64 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then placeholder jHi else discard <| timers jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation"))
  discard <| timers jEnd
  old (audit (requireNothingDueAudit jEnd))
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modifyWG fun w => { w with jiffiesLast := some j })

def afterAdvanceWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit) : PrefixM E Unit := do
  let w ← liftPrefix getWG
  let a ← liftPrefix getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then placeholder jHi else discard <| timers jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance"))
  let some (j0, j1) := (← liftPrefix getEnv).lastAdvance | liftPrefix (invariant "afterAdvance without an advance")
  let jPass := if timeAfter jEnd j1 then jEnd else j0
  discard <| timers jPass
  old (audit (requireNothingDueAudit jPass))
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modifyWG fun w => { w with jiffiesLast := some j })

def deferredWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (cryptWork sendWork afterXmitWork : PrefixM E Unit)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit)
    (idle afterAdvanceWork : PrefixM E Unit) : (call : EnvDeferredCall) → PrefixM E call.Result
  | .drained what queues => old (audit (EnvDeferredCall.observed (.drained what queues)))
  | .idleDevice => old (audit (EnvDeferredCall.observed .idleDevice))
  | .noCrypt => old (audit (EnvDeferredCall.observed .noCrypt))
  | .crypt => cryptWork
  | .sendOne => old (audit (EnvDeferredCall.observed .sendOne))
  | .clearOne => old (audit (EnvDeferredCall.observed .clearOne))
  | .sendAll => sendWork
  | .afterXmit => afterXmitWork
  | .timerWorker timer => old (audit (EnvDeferredCall.observed (.timerWorker timer)))
  | .timers jHi => timers jHi
  | .placeholder jHi => placeholder jHi
  | .idle => idle
  | .advance ticks => old (audit (EnvDeferredCall.observed (.advance ticks)))
  | .afterAdvance => afterAdvanceWork

theorem crypt_factor : runCryptWorkers = cryptWith (schedule none) := rfl
theorem send_factor : runSendWorkers = sendWith (fun {_} a => a) (schedule none) := rfl
theorem afterXmit_factor : afterXmit = afterXmitWith (fun {_} a => a) runCryptWorkers runSendWorkers := rfl
theorem timers_factor (j : UInt64) : runTimers j = timersWith (fun {_} a => a) runCryptWorkers j := rfl
theorem placeholder_factor (j : UInt64) : runTimersPlaceholder j =
    placeholderWith (fun {_} a => a) runCryptWorkers runSendWorkers j := rfl
theorem idle_factor : idleTimers = idleWith (fun {_} a => a) runTimers runTimersPlaceholder := rfl
theorem afterAdvance_factor : afterAdvance =
    afterAdvanceWith (fun {_} a => a) runTimers runTimersPlaceholder := rfl
theorem deferred_factor (call : EnvDeferredCall) : deferred call =
    deferredWith (fun {_} a => a) runCryptWorkers runSendWorkers afterXmit
      runTimers runTimersPlaceholder idleTimers afterAdvance call := by cases call <;> rfl


theorem crypt_projects {E F : Type} (ρ : E → Option F)
    (schedule : PrefixM E Unit) (schedule' : PrefixM F Unit)
    (hs : ProjectsPrefix ρ id schedule schedule') :
    ProjectsPrefix ρ id (cryptWith schedule) (cryptWith schedule') := by
  unfold cryptWith
  exact projectsPrefix_bind ρ id id hs (fun _ => projectsPrefix_lift ρ _)

theorem crypt_appends {E : Type} (schedule : PrefixM E Unit) (hs : Appends schedule) :
    Appends (cryptWith schedule) := by
  unfold cryptWith
  exact Appends.bind hs (fun _ => Appends.lift _)

section
variable {E F : Type} (ρ : E → Option F)
    (old : {α : Type} → Obs α → PrefixM E α)
    (old' : {α : Type} → Obs α → PrefixM F α)
    (ho : ∀ {α : Type} (a : Obs α), Appends a → ProjectsPrefix ρ id (old a) (old' a))
include ho

theorem send_projects
    (schedule : PrefixM E Unit) (schedule' : PrefixM F Unit)
    (h_schedule : ProjectsPrefix ρ id schedule schedule')
    : ProjectsPrefix ρ id (sendWith old schedule)
      (sendWith old' schedule') := by
  unfold sendWith
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head schedule; exact h_schedule)
    | scheduler_project_step

theorem afterXmit_projects
    (cryptWork : PrefixM E Unit) (cryptWork' : PrefixM F Unit)
    (sendWork : PrefixM E Unit) (sendWork' : PrefixM F Unit)
    (h_cryptWork : ProjectsPrefix ρ id cryptWork cryptWork')
    (h_sendWork : ProjectsPrefix ρ id sendWork sendWork')
    : ProjectsPrefix ρ id (afterXmitWith old cryptWork sendWork)
      (afterXmitWith old' cryptWork' sendWork') := by
  unfold afterXmitWith
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head cryptWork; exact h_cryptWork)
    | (poll_source_head sendWork; exact h_sendWork)
    | scheduler_project_step

theorem timers_projects
    (cryptWork : PrefixM E Unit) (cryptWork' : PrefixM F Unit)
    (h_cryptWork : ProjectsPrefix ρ id cryptWork cryptWork')
    (j : UInt64)
    : ProjectsPrefix ρ id (timersWith old cryptWork j)
      (timersWith old' cryptWork' j) := by
  unfold timersWith
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head cryptWork; exact h_cryptWork)
    | scheduler_project_step

theorem placeholder_projects
    (cryptWork : PrefixM E Unit) (cryptWork' : PrefixM F Unit)
    (sendWork : PrefixM E Unit) (sendWork' : PrefixM F Unit)
    (h_cryptWork : ProjectsPrefix ρ id cryptWork cryptWork')
    (h_sendWork : ProjectsPrefix ρ id sendWork sendWork')
    (j : UInt64)
    : ProjectsPrefix ρ id (placeholderWith old cryptWork sendWork j)
      (placeholderWith old' cryptWork' sendWork' j) := by
  unfold placeholderWith
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head cryptWork; exact h_cryptWork)
    | (poll_source_head sendWork; exact h_sendWork)
    | scheduler_project_step

theorem idle_projects
    (timers : UInt64 → PrefixM E Bool) (timers' : UInt64 → PrefixM F Bool)
    (placeholder : UInt64 → PrefixM E Unit) (placeholder' : UInt64 → PrefixM F Unit)
    (h_timers : ∀ j, ProjectsPrefix ρ id (timers j) (timers' j))
    (h_placeholder : ∀ j, ProjectsPrefix ρ id (placeholder j) (placeholder' j))
    : ProjectsPrefix ρ id (idleWith old timers placeholder)
      (idleWith old' timers' placeholder') := by
  unfold idleWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head timers; exact h_timers _)
    | (poll_source_head placeholder; exact h_placeholder _)
    | scheduler_project_step

theorem afterAdvance_projects
    (timers : UInt64 → PrefixM E Bool) (timers' : UInt64 → PrefixM F Bool)
    (placeholder : UInt64 → PrefixM E Unit) (placeholder' : UInt64 → PrefixM F Unit)
    (h_timers : ∀ j, ProjectsPrefix ρ id (timers j) (timers' j))
    (h_placeholder : ∀ j, ProjectsPrefix ρ id (placeholder j) (placeholder' j))
    : ProjectsPrefix ρ id (afterAdvanceWith old timers placeholder)
      (afterAdvanceWith old' timers' placeholder') := by
  unfold afterAdvanceWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head timers; exact h_timers _)
    | (poll_source_head placeholder; exact h_placeholder _)
    | scheduler_project_step

theorem deferred_projects
    (cryptWork : PrefixM E Unit) (cryptWork' : PrefixM F Unit)
    (sendWork : PrefixM E Unit) (sendWork' : PrefixM F Unit)
    (afterXmitWork : PrefixM E Unit) (afterXmitWork' : PrefixM F Unit)
    (timers : UInt64 → PrefixM E Bool) (timers' : UInt64 → PrefixM F Bool)
    (placeholder : UInt64 → PrefixM E Unit) (placeholder' : UInt64 → PrefixM F Unit)
    (idle : PrefixM E Unit) (idle' : PrefixM F Unit)
    (afterAdvanceWork : PrefixM E Unit) (afterAdvanceWork' : PrefixM F Unit)
    (h_cryptWork : ProjectsPrefix ρ id cryptWork cryptWork')
    (h_sendWork : ProjectsPrefix ρ id sendWork sendWork')
    (h_afterXmitWork : ProjectsPrefix ρ id afterXmitWork afterXmitWork')
    (h_timers : ∀ j, ProjectsPrefix ρ id (timers j) (timers' j))
    (h_placeholder : ∀ j, ProjectsPrefix ρ id (placeholder j) (placeholder' j))
    (h_idle : ProjectsPrefix ρ id idle idle')
    (h_afterAdvanceWork : ProjectsPrefix ρ id afterAdvanceWork afterAdvanceWork')
    (call : EnvDeferredCall)
    : ProjectsPrefix ρ id (deferredWith old cryptWork sendWork afterXmitWork timers placeholder idle afterAdvanceWork call)
      (deferredWith old' cryptWork' sendWork' afterXmitWork' timers' placeholder' idle' afterAdvanceWork' call) := by
  cases call <;> unfold deferredWith
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head cryptWork; exact h_cryptWork)
    | (poll_source_head sendWork; exact h_sendWork)
    | (poll_source_head afterXmitWork; exact h_afterXmitWork)
    | (poll_source_head timers; exact h_timers _)
    | (poll_source_head placeholder; exact h_placeholder _)
    | (poll_source_head idle; exact h_idle)
    | (poll_source_head afterAdvanceWork; exact h_afterAdvanceWork)
    | scheduler_project_step

end

section
variable {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (ho : ∀ {α : Type} (a : Obs α), Appends a → Appends (old a))
include ho

theorem send_appends
    (schedule : PrefixM E Unit) (h_schedule : Appends schedule)
    : Appends (sendWith old schedule) := by
  unfold sendWith
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head schedule; exact h_schedule)
    | scheduler_append_step

theorem afterXmit_appends
    (cryptWork : PrefixM E Unit) (h_cryptWork : Appends cryptWork)
    (sendWork : PrefixM E Unit) (h_sendWork : Appends sendWork)
    : Appends (afterXmitWith old cryptWork sendWork) := by
  unfold afterXmitWith
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head cryptWork; exact h_cryptWork)
    | (poll_source_head sendWork; exact h_sendWork)
    | scheduler_append_step

theorem timers_appends
    (cryptWork : PrefixM E Unit) (h_cryptWork : Appends cryptWork)
    (j : UInt64)
    : Appends (timersWith old cryptWork j) := by
  unfold timersWith
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head cryptWork; exact h_cryptWork)
    | scheduler_append_step

theorem placeholder_appends
    (cryptWork : PrefixM E Unit) (h_cryptWork : Appends cryptWork)
    (sendWork : PrefixM E Unit) (h_sendWork : Appends sendWork)
    (j : UInt64)
    : Appends (placeholderWith old cryptWork sendWork j) := by
  unfold placeholderWith
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head cryptWork; exact h_cryptWork)
    | (poll_source_head sendWork; exact h_sendWork)
    | scheduler_append_step

theorem idle_appends
    (timers : UInt64 → PrefixM E Bool) (h_timers : ∀ j, Appends (timers j))
    (placeholder : UInt64 → PrefixM E Unit) (h_placeholder : ∀ j, Appends (placeholder j))
    : Appends (idleWith old timers placeholder) := by
  unfold idleWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head timers; exact h_timers _)
    | (poll_source_head placeholder; exact h_placeholder _)
    | scheduler_append_step

theorem afterAdvance_appends
    (timers : UInt64 → PrefixM E Bool) (h_timers : ∀ j, Appends (timers j))
    (placeholder : UInt64 → PrefixM E Unit) (h_placeholder : ∀ j, Appends (placeholder j))
    : Appends (afterAdvanceWith old timers placeholder) := by
  unfold afterAdvanceWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head timers; exact h_timers _)
    | (poll_source_head placeholder; exact h_placeholder _)
    | scheduler_append_step

theorem deferred_appends
    (cryptWork : PrefixM E Unit) (h_cryptWork : Appends cryptWork)
    (sendWork : PrefixM E Unit) (h_sendWork : Appends sendWork)
    (afterXmitWork : PrefixM E Unit) (h_afterXmitWork : Appends afterXmitWork)
    (timers : UInt64 → PrefixM E Bool) (h_timers : ∀ j, Appends (timers j))
    (placeholder : UInt64 → PrefixM E Unit) (h_placeholder : ∀ j, Appends (placeholder j))
    (idle : PrefixM E Unit) (h_idle : Appends idle)
    (afterAdvanceWork : PrefixM E Unit) (h_afterAdvanceWork : Appends afterAdvanceWork)
    (call : EnvDeferredCall)
    : Appends (deferredWith old cryptWork sendWork afterXmitWork timers placeholder idle afterAdvanceWork call) := by
  cases call <;> unfold deferredWith
  all_goals repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head cryptWork; exact h_cryptWork)
    | (poll_source_head sendWork; exact h_sendWork)
    | (poll_source_head afterXmitWork; exact h_afterXmitWork)
    | (poll_source_head timers; exact h_timers _)
    | (poll_source_head placeholder; exact h_placeholder _)
    | (poll_source_head idle; exact h_idle)
    | (poll_source_head afterAdvanceWork; exact h_afterAdvanceWork)
    | scheduler_append_step

end

end Leanux.Proofs.WG.Queues.RxHistory.DeferredSource
