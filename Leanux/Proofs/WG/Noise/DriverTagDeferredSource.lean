import Leanux.Proofs.WG.Queues.DeferredPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Deferred
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RxHistory.SchedulerSource RxHistory.DeferredSource
universe u

/-- These four actual executions must be explicit callbacks. The other old
atoms contain no owner invocation relevant to the tag journal. -/
structure Hooks (E : Type) where
  sendOne : PrefixM E Unit
  clearOne : PrefixM E Unit
  timer : Worker → PeerId → PeerTimer → WheelEntry → Option UInt64 → PrefixM E Unit
  placeholder : UInt64 → PrefixM E Unit

def originalHooks {E : Type} (old : {α : Type} → RxHistory.Obs α → PrefixM E α) : Hooks E :=
  ⟨old (RxHistory.audit runOneSendWorkerAudit), old (RxHistory.audit runOneClearWorkerAudit),
    fun w pid timer entry prior => old (RxHistory.audit (timerDispatchAudit w pid timer entry prior)),
    fun j => old (RxHistory.audit (RxHistory.placeholderTimerPassAudit j))⟩

def sendWith {E : Type} (hooks : Hooks E)
    (schedule : PrefixM E Unit) : PrefixM E Unit := do
  if (← liftPrefix getWG).dev.isNone then return
  liftPrefix Env.requireNoCryptWork
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then liftPrefix Env.deliverSent; return
    hooks.sendOne
    schedule
  liftPrefix (budgetExhausted "the send work queue")

def timersWith {E : Type} (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (hooks : Hooks E)
    (cryptWork : PrefixM E Unit) (jPass : UInt64) : PrefixM E Bool := do
  liftPrefix (modifyWG fun w => { w with queuedThisCall := [] })
  if (← liftPrefix getWG).dev.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  let mut step : Option UInt64 := none
  for _ in [0:(← liftPrefix recordBudget)] do
    let some site ← liftPrefix Env.peekNextSite | break
    let d ← old (RxHistory.audit getDevSavedAudit)
    if let some w := Env.timerSectionOf site then
      if w == .clearPeerWorker then
        if let some b := step then
          old (RxHistory.audit (requireStepCompleteAudit b))
          step := none
        if d.clearWorkQueue.isEmpty then break
        hooks.clearOne
      else
        let some (pid, t, we) ← old (RxHistory.audit (wheelNextDueAudit d jPass))
          | liftPrefix (throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jPass}"))
        hooks.timer w pid t we step
        step := some we.bucketExpiry
        fired := true
    else
      if let some b := step then
        old (RxHistory.audit (requireStepCompleteAudit b))
        step := none
      if !fired then break
      else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then hooks.sendOne
      else
        cryptWork
        if (← liftPrefix Env.peekNextSite) == some site then break
  if let some b := step then old (RxHistory.audit (requireStepCompleteAudit b))
  if fired then
    liftPrefix Env.deliverSent
    let d ← old (RxHistory.audit getDevSavedAudit)
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      liftPrefix (unsupported "work a timer queued outlived the guest's wait")
  return fired

def placeholderWith {E : Type} (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (hooks : Hooks E)
    (cryptWork sendWork : PrefixM E Unit) (jHi : UInt64) : PrefixM E Unit := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getWG).dev.isNone then return
  hooks.placeholder jHi
  cryptWork
  sendWork
  for _ in [0:(← old (RxHistory.audit getDevSavedAudit)).clearWorkQueue.length + 1] do
    if (← old (RxHistory.audit getDevSavedAudit)).clearWorkQueue.isEmpty then break
    hooks.clearOne
def deferredWith {E : Type} (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (hooks : Hooks E)
    (cryptWork sendWork afterXmitWork : PrefixM E Unit)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit)
    (idle afterAdvanceWork : PrefixM E Unit) : (call : EnvDeferredCall) → PrefixM E call.Result
  | .drained what queues => old (RxHistory.audit (EnvDeferredCall.observed (.drained what queues)))
  | .idleDevice => old (RxHistory.audit (EnvDeferredCall.observed .idleDevice))
  | .noCrypt => old (RxHistory.audit (EnvDeferredCall.observed .noCrypt))
  | .crypt => cryptWork
  | .sendOne => hooks.sendOne
  | .clearOne => hooks.clearOne
  | .sendAll => sendWork
  | .afterXmit => afterXmitWork
  | .timerWorker timer => old (RxHistory.audit (EnvDeferredCall.observed (.timerWorker timer)))
  | .timers jHi => timers jHi
  | .placeholder jHi => placeholder jHi
  | .idle => idle
  | .advance ticks => old (RxHistory.audit (EnvDeferredCall.observed (.advance ticks)))
  | .afterAdvance => afterAdvanceWork

theorem send_source {E : Type} (old : {α : Type} → RxHistory.Obs α → PrefixM E α)
    (schedule : PrefixM E Unit) :
    sendWith (originalHooks old) schedule = RxHistory.DeferredSource.sendWith old schedule := rfl
theorem timers_source {E : Type} (old : {α : Type} → RxHistory.Obs α → PrefixM E α)
    (cryptWork : PrefixM E Unit) (j : UInt64) :
    timersWith old (originalHooks old) cryptWork j =
      RxHistory.DeferredSource.timersWith old cryptWork j := rfl
theorem placeholder_source {E : Type} (old : {α : Type} → RxHistory.Obs α → PrefixM E α)
    (cryptWork sendWork : PrefixM E Unit) (j : UInt64) :
    placeholderWith old (originalHooks old) cryptWork sendWork j =
      RxHistory.DeferredSource.placeholderWith old cryptWork sendWork j := rfl
theorem deferred_source {E : Type} (old : {α : Type} → RxHistory.Obs α → PrefixM E α)
    (cryptWork sendWork afterXmitWork : PrefixM E Unit)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit)
    (idle afterAdvanceWork : PrefixM E Unit) (call : EnvDeferredCall) :
    deferredWith old (originalHooks old) cryptWork sendWork afterXmitWork timers placeholder idle afterAdvanceWork call =
      RxHistory.DeferredSource.deferredWith old cryptWork sendWork afterXmitWork timers placeholder idle afterAdvanceWork call := by
  cases call <;> rfl

structure QuietAtoms {E : Type} (I : List E → World → Prop) (S : List E → Prop)
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) : Prop where
  drained : ∀ what queues, PrefixPreserves I S (old (RxHistory.mixed (requireDrainedPrefix what queues)))
  saved : PrefixPreserves I S (old (RxHistory.audit getDevSavedAudit))
  wheel : ∀ d j, PrefixPreserves I S (old (RxHistory.audit (wheelNextDueAudit d j)))
  stepComplete : ∀ b, PrefixPreserves I S (old (RxHistory.audit (requireStepCompleteAudit b)))
  nothingDue : ∀ j, PrefixPreserves I S (old (RxHistory.audit (requireNothingDueAudit j)))
  idleDevice : PrefixPreserves I S (old (RxHistory.mixed requireIdleDevicePrefix))
  noCrypt : PrefixPreserves I S (old (RxHistory.audit (liftPrefix Env.requireNoCryptWork)))
  timerWorker : ∀ timer, PrefixPreserves I S (old (RxHistory.audit (liftPrefix (Env.timerWorker timer))))
  advance : ∀ ticks, PrefixPreserves I S (old (RxHistory.audit (advanceAudit ticks)))

structure HookContracts {E : Type} (I : List E → World → Prop) (S : List E → Prop)
    (hooks : Hooks E) : Prop where
  sendOne : PrefixPreserves I S hooks.sendOne
  clearOne : PrefixPreserves I S hooks.clearOne
  timer : ∀ w pid timer entry prior, PrefixPreserves I S (hooks.timer w pid timer entry prior)
  placeholder : ∀ j, PrefixPreserves I S (hooks.placeholder j)

structure QuietErases {E : Type}
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) : Prop where
  drained : ∀ what queues, ErasesPrefix (old (RxHistory.mixed (requireDrainedPrefix what queues))) (Env.requireDrained what queues)
  saved : ErasesPrefix (old (RxHistory.audit getDevSavedAudit)) (liftWG getDev)
  wheel : ∀ d j, ErasesPrefix (old (RxHistory.audit (wheelNextDueAudit d j))) (pure (TimerWheel.nextDue d j))
  stepComplete : ∀ b, ErasesPrefix (old (RxHistory.audit (requireStepCompleteAudit b))) (Env.requireStepComplete b)
  nothingDue : ∀ j, ErasesPrefix (old (RxHistory.audit (requireNothingDueAudit j))) (Env.requireNothingDue j)
  idleDevice : ErasesPrefix (old (RxHistory.mixed requireIdleDevicePrefix)) Env.requireIdleDevice
  noCrypt : ErasesPrefix (old (RxHistory.audit (liftPrefix Env.requireNoCryptWork))) Env.requireNoCryptWork
  timerWorker : ∀ timer, ErasesPrefix (old (RxHistory.audit (liftPrefix (Env.timerWorker timer)))) (Env.timerWorker timer)
  advance : ∀ ticks, ErasesPrefix (old (RxHistory.audit (advanceAudit ticks))) (Env.advance ticks)

structure HookErases {E : Type} (hooks : Hooks E) : Prop where
  sendOne : ErasesPrefix hooks.sendOne Env.runOneSendWorker
  clearOne : ErasesPrefix hooks.clearOne Env.runOneClearWorker
  timer : ∀ w pid timer entry prior, ErasesPrefix (hooks.timer w pid timer entry prior) (timerDispatchUnit w pid timer entry prior)
  placeholder : ∀ j, ErasesPrefix (hooks.placeholder j) (RxHistory.placeholderTimerPassSource j)

macro "tag_deferred_quiet " atoms:ident : tactic => `(tactic| first
  | (scheduler_preserve_at requireDrainedPrefix; exact ($atoms).drained _ _)
  | (scheduler_preserve_at getDevSavedAudit; exact ($atoms).saved)
  | (scheduler_preserve_at wheelNextDueAudit; exact ($atoms).wheel _ _)
  | (scheduler_preserve_at requireStepCompleteAudit; exact ($atoms).stepComplete _)
  | (scheduler_preserve_at requireNothingDueAudit; exact ($atoms).nothingDue _))

macro "tag_deferred_hook " contracts:ident : tactic => `(tactic| first
  | (scheduler_preserve_at Hooks.sendOne; exact ($contracts).sendOne)
  | (scheduler_preserve_at Hooks.clearOne; exact ($contracts).clearOne)
  | (scheduler_preserve_at Hooks.timer; exact ($contracts).timer _ _ _ _ _)
  | (scheduler_preserve_at Hooks.placeholder; exact ($contracts).placeholder _))

variable {E : Type} {I : List E → World → Prop} {S : List E → Prop}

theorem send_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (hooks : Hooks E) (contracts : HookContracts I S hooks)
    (schedule : PrefixM E Unit) (hs : PrefixPreserves I S schedule) :
    PrefixPreserves I S (sendWith hooks schedule) := by
  unfold sendWith
  repeat' first
    | (scheduler_preserve_at schedule; exact hs)
    | tag_deferred_hook contracts
    | deferred_raw_steps safe store

theorem timers_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietAtoms I S old)
    (hooks : Hooks E) (contracts : HookContracts I S hooks)
    (cryptWork : PrefixM E Unit) (hc : PrefixPreserves I S cryptWork) (j : UInt64) :
    PrefixPreserves I S (timersWith old hooks cryptWork j) := by
  unfold timersWith
  repeat' first
    | (scheduler_preserve_at cryptWork; exact hc)
    | tag_deferred_quiet atoms
    | tag_deferred_hook contracts
    | deferred_raw_steps safe store

theorem placeholder_preserves_saved (safe : ∀ h w,I h w→S h)
    (store : ∀ h w v,productStoreView v=productStoreView w→I h w→I h v)
    (old : {α : Type}→RxHistory.Obs α→PrefixM E α)
    (saved : PrefixPreserves I S (old (RxHistory.audit getDevSavedAudit)))
    (hooks : Hooks E) (contracts : HookContracts I S hooks)
    (cryptWork sendWork : PrefixM E Unit)
    (hc : PrefixPreserves I S cryptWork) (hs : PrefixPreserves I S sendWork) (j : UInt64) :
    PrefixPreserves I S (placeholderWith old hooks cryptWork sendWork j) := by
  unfold placeholderWith
  repeat' first
    | (scheduler_preserve_at cryptWork; exact hc)
    | (scheduler_preserve_at sendWork; exact hs)
    | (scheduler_preserve_at getDevSavedAudit; exact saved)
    | tag_deferred_hook contracts
    | deferred_raw_steps safe store

theorem placeholder_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietAtoms I S old)
    (hooks : Hooks E) (contracts : HookContracts I S hooks)
    (cryptWork sendWork : PrefixM E Unit)
    (hc : PrefixPreserves I S cryptWork) (hs : PrefixPreserves I S sendWork) (j : UInt64) :
    PrefixPreserves I S (placeholderWith old hooks cryptWork sendWork j) :=
  placeholder_preserves_saved safe store old atoms.saved hooks contracts cryptWork sendWork hc hs j

theorem deferred_preserves
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietAtoms I S old)
    (hooks : Hooks E) (contracts : HookContracts I S hooks)
    (cryptWork sendWork afterXmitWork : PrefixM E Unit)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit)
    (idle afterAdvanceWork : PrefixM E Unit)
    (hc : PrefixPreserves I S cryptWork) (hs : PrefixPreserves I S sendWork)
    (hx : PrefixPreserves I S afterXmitWork)
    (ht : ∀ j, PrefixPreserves I S (timers j)) (hp : ∀ j, PrefixPreserves I S (placeholder j))
    (hi : PrefixPreserves I S idle) (ha : PrefixPreserves I S afterAdvanceWork)
    (call : EnvDeferredCall) :
    PrefixPreserves I S (deferredWith old hooks cryptWork sendWork afterXmitWork timers placeholder idle afterAdvanceWork call) := by
  cases call with
  | drained what queues => exact atoms.drained what queues
  | idleDevice => exact atoms.idleDevice
  | noCrypt => exact atoms.noCrypt
  | crypt => exact hc
  | sendOne => exact contracts.sendOne
  | clearOne => exact contracts.clearOne
  | sendAll => exact hs
  | afterXmit => exact hx
  | timerWorker timer => exact atoms.timerWorker timer
  | timers j => exact ht j
  | placeholder j => exact hp j
  | idle => exact hi
  | advance ticks => exact atoms.advance ticks
  | afterAdvance => exact ha


/-- Transfer an existing native suffix equation through the same actual
callback result. This compares executions; it does not run either one again. -/
theorem suffix_erases {F α : Type} (hook : PrefixM E Unit) (original : PrefixM F Unit)
    (native : Leanux.M Unit) (out : α) (tail : Leanux.M α)
    (hh : ErasesPrefix hook native) (ho : ErasesPrefix original native)
    (ht : ErasesPrefix (do original; pure out) tail) :
    ErasesPrefix (do hook; pure out) tail := by
  intro w h
  have left := erasesPrefix_bind hh (fun _ => erasesPrefix_pure out) w h
  have right := erasesPrefix_bind ho (fun _ => erasesPrefix_pure out) w []
  exact left.trans (right.symm.trans (ht w []))

theorem send_erases (hooks : Hooks E) (contracts : HookErases hooks)
    (schedule : PrefixM E Unit) (hs : ErasesPrefix schedule (Env.schedule none)) :
    ErasesPrefix (sendWith hooks schedule) Env.runSendWorkers := by
  unfold sendWith Env.runSendWorkers
  repeat' first
    | exact hs
    | exact contracts.sendOne
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

/-- Select a source rule without changing the goal or constructing a proof. -/
elab "tag_deferred_erase_at " mode:ident wanted:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``ErasesPrefix do Lean.throwError "not an erasure contract"
  let args := target.getAppArgs
  let mut action := args[args.size-2]!.consumeMData.headBeta
  if mode.getId.toString == "bound" then
    unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
    let bindArgs := action.getAppArgs
    action := bindArgs[bindArgs.size-2]!.consumeMData.headBeta
  if let .fvar f := action.getAppFn then
    if (← f.getDecl).userName.eraseMacroScopes.toString == "old" then
      action := action.getAppArgs.back!.consumeMData.headBeta
  for wrapper in [``RxHistory.audit,``RxHistory.mixed,``liftPrefix] do
    if action.isAppOf wrapper then action := action.getAppArgs.back!.consumeMData.headBeta
  let actual ← match action.getAppFn with
    | .const name _ => pure name.toString
    | .fvar f => pure (← f.getDecl).userName.eraseMacroScopes.toString
    | _ => Lean.throwError "not a named action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual == expected || actual.endsWith ("." ++ expected) do
    Lean.throwError "different source head"

theorem timers_erases
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietErases old)
    (hooks : Hooks E) (contracts : HookErases hooks)
    (cryptWork : PrefixM E Unit) (hc : ErasesPrefix cryptWork Env.runCryptWorkers)
    (j : UInt64) : ErasesPrefix (timersWith old hooks cryptWork j) (Env.runTimers j) := by
  rw [← Environment.runTimersSource_eq]
  unfold timersWith Environment.runTimersSource
  repeat' first
    | maintenance_intro
    | contradiction
    | timer_audit_stopped
    | (timer_audit_bound Hooks.timer; exact suffix_erases _ _ _ _ _
        (contracts.timer _ _ _ _ _) (timerDispatchAudit_erases _ _ _ _ _)
        (timerDispatchAudit_suffix_erases _ _ _ _ _ _))
    | (tag_deferred_erase_at atom getDevSavedAudit; exact atoms.saved)
    | (tag_deferred_erase_at bound wheelNextDueAudit; apply erasesPrefix_bind_pure (atoms.wheel _ _))
    | (tag_deferred_erase_at atom requireStepCompleteAudit; exact atoms.stepComplete _)
    | (tag_deferred_erase_at atom Hooks.clearOne; exact contracts.clearOne)
    | (tag_deferred_erase_at atom Hooks.sendOne; exact contracts.sendOne)
    | (tag_deferred_erase_at atom cryptWork; exact hc)
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesPrefix_range)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (maintenance_head ite; apply erasesPrefix_ite)
    | timer_audit_erases_join
    | timer_audit_erases_join_use
    | timer_audit_reduce
    | timer_audit_reduce_match
    | timer_audit_cases
    | (with_reducible split)

theorem placeholder_erases
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietErases old)
    (hooks : Hooks E) (contracts : HookErases hooks)
    (cryptWork sendWork : PrefixM E Unit)
    (hc : ErasesPrefix cryptWork Env.runCryptWorkers)
    (hs : ErasesPrefix sendWork Env.runSendWorkers) (j : UInt64) :
    ErasesPrefix (placeholderWith old hooks cryptWork sendWork j) (Env.runTimersPlaceholder j) := by
  rw [← RxHistory.placeholderSource_eq]
  unfold placeholderWith RxHistory.placeholderSourceWithPass
  repeat' first
    | exact contracts.placeholder _
    | exact atoms.saved
    | exact hc
    | exact hs
    | exact contracts.clearOne
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesPrefix_range)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | timer_audit_erases_join
    | timer_audit_erases_join_use
    | timer_audit_reduce
    | timer_audit_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem deferred_erases
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietErases old)
    (hooks : Hooks E) (contracts : HookErases hooks)
    (cryptWork sendWork afterXmitWork : PrefixM E Unit)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit)
    (idle afterAdvanceWork : PrefixM E Unit)
    (hc : ErasesPrefix cryptWork Env.runCryptWorkers)
    (hs : ErasesPrefix sendWork Env.runSendWorkers)
    (hx : ErasesPrefix afterXmitWork Env.afterXmit)
    (ht : ∀ j, ErasesPrefix (timers j) (Env.runTimers j))
    (hp : ∀ j, ErasesPrefix (placeholder j) (Env.runTimersPlaceholder j))
    (hi : ErasesPrefix idle Env.idleTimers)
    (ha : ErasesPrefix afterAdvanceWork Env.afterAdvance)
    (call : EnvDeferredCall) :
    ErasesPrefix (deferredWith old hooks cryptWork sendWork afterXmitWork timers placeholder idle afterAdvanceWork call)
      call.original := by
  cases call with
  | drained what queues => exact atoms.drained what queues
  | idleDevice => exact atoms.idleDevice
  | noCrypt => exact atoms.noCrypt
  | crypt => exact hc
  | sendOne => exact contracts.sendOne
  | clearOne => exact contracts.clearOne
  | sendAll => exact hs
  | afterXmit => exact hx
  | timerWorker timer => exact atoms.timerWorker timer
  | timers j => exact ht j
  | placeholder j => exact hp j
  | idle => exact hi
  | advance ticks => exact atoms.advance ticks
  | afterAdvance => exact ha

/-! The remaining callers reuse C1's definitions verbatim. Their proofs need
only inert old-atom contracts and the explicit committed callbacks. -/
theorem afterXmit_preserves_drained (safe : ∀ h w,I h w→S h)
    (store : ∀ h w v,productStoreView v=productStoreView w→I h w→I h v)
    (old : {α : Type}→RxHistory.Obs α→PrefixM E α)
    (drained : ∀ what queues,PrefixPreserves I S (old (RxHistory.mixed (requireDrainedPrefix what queues))))
    (cryptWork sendWork : PrefixM E Unit)
    (hc : PrefixPreserves I S cryptWork) (hs : PrefixPreserves I S sendWork) :
    PrefixPreserves I S (RxHistory.DeferredSource.afterXmitWith old cryptWork sendWork) := by
  unfold RxHistory.DeferredSource.afterXmitWith
  repeat' first
    | (scheduler_preserve_at cryptWork; exact hc)
    | (scheduler_preserve_at sendWork; exact hs)
    | (scheduler_preserve_at requireDrainedPrefix; exact drained _ _)
    | deferred_raw_steps safe store

theorem afterXmit_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietAtoms I S old)
    (cryptWork sendWork : PrefixM E Unit)
    (hc : PrefixPreserves I S cryptWork) (hs : PrefixPreserves I S sendWork) :
    PrefixPreserves I S (RxHistory.DeferredSource.afterXmitWith old cryptWork sendWork) :=
  afterXmit_preserves_drained safe store old atoms.drained cryptWork sendWork hc hs

theorem idle_preserves_nothingDue (safe : ∀ h w,I h w→S h)
    (store : ∀ h w v,productStoreView v=productStoreView w→I h w→I h v)
    (old : {α : Type}→RxHistory.Obs α→PrefixM E α)
    (nothingDue : ∀ j,PrefixPreserves I S (old (RxHistory.audit (requireNothingDueAudit j))))
    (timers : UInt64→PrefixM E Bool) (placeholder : UInt64→PrefixM E Unit)
    (ht : ∀ j,PrefixPreserves I S (timers j)) (hp : ∀ j,PrefixPreserves I S (placeholder j)) :
    PrefixPreserves I S (RxHistory.DeferredSource.idleWith old timers placeholder) := by
  unfold RxHistory.DeferredSource.idleWith
  repeat' first
    | (scheduler_preserve_at Functor.discard
       change PrefixPreserves I S (timers _ >>= fun _=>pure ())
       exact PrefixPreserves.bind (ht _) (fun _=>PrefixPreserves.pure safe ()))
    | (scheduler_preserve_at timers; exact ht _)
    | (scheduler_preserve_at placeholder; exact hp _)
    | (scheduler_preserve_at requireNothingDueAudit; exact nothingDue _)
    | deferred_raw_steps safe store

theorem idle_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietAtoms I S old)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit)
    (ht : ∀ j, PrefixPreserves I S (timers j)) (hp : ∀ j, PrefixPreserves I S (placeholder j)) :
    PrefixPreserves I S (RxHistory.DeferredSource.idleWith old timers placeholder) :=
  idle_preserves_nothingDue safe store old atoms.nothingDue timers placeholder ht hp

theorem afterAdvance_preserves_nothingDue (safe : ∀ h w,I h w→S h)
    (store : ∀ h w v,productStoreView v=productStoreView w→I h w→I h v)
    (old : {α : Type}→RxHistory.Obs α→PrefixM E α)
    (nothingDue : ∀ j,PrefixPreserves I S (old (RxHistory.audit (requireNothingDueAudit j))))
    (timers : UInt64→PrefixM E Bool) (placeholder : UInt64→PrefixM E Unit)
    (ht : ∀ j,PrefixPreserves I S (timers j)) (hp : ∀ j,PrefixPreserves I S (placeholder j)) :
    PrefixPreserves I S (RxHistory.DeferredSource.afterAdvanceWith old timers placeholder) := by
  unfold RxHistory.DeferredSource.afterAdvanceWith
  repeat' first
    | (scheduler_preserve_at Functor.discard
       change PrefixPreserves I S (timers _ >>= fun _=>pure ())
       exact PrefixPreserves.bind (ht _) (fun _=>PrefixPreserves.pure safe ()))
    | (scheduler_preserve_at timers; exact ht _)
    | (scheduler_preserve_at placeholder; exact hp _)
    | (scheduler_preserve_at requireNothingDueAudit; exact nothingDue _)
    | deferred_raw_steps safe store

theorem afterAdvance_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietAtoms I S old)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit)
    (ht : ∀ j, PrefixPreserves I S (timers j)) (hp : ∀ j, PrefixPreserves I S (placeholder j)) :
    PrefixPreserves I S (RxHistory.DeferredSource.afterAdvanceWith old timers placeholder) :=
  afterAdvance_preserves_nothingDue safe store old atoms.nothingDue timers placeholder ht hp

theorem crypt_erases (schedule : PrefixM E Unit)
    (hs : ErasesPrefix schedule (Env.schedule none)) :
    ErasesPrefix (RxHistory.DeferredSource.cryptWith schedule) Env.runCryptWorkers := by
  unfold RxHistory.DeferredSource.cryptWith Env.runCryptWorkers
  exact erasesPrefix_bind hs (fun _ => erasesPrefix_lift _)

macro "tag_deferred_erasure_steps" : tactic => `(tactic| first
  | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
  | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
  | (maintenance_head ForIn.forIn; apply erasesPrefix_range)
  | (maintenance_head Bind.bind; apply erasesPrefix_bind)
  | timer_audit_erases_join
  | timer_audit_erases_join_use
  | timer_audit_reduce
  | timer_audit_reduce_match
  | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
  | maintenance_intro
  | trivial)

theorem afterXmit_erases
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietErases old)
    (cryptWork sendWork : PrefixM E Unit)
    (hc : ErasesPrefix cryptWork Env.runCryptWorkers)
    (hs : ErasesPrefix sendWork Env.runSendWorkers) :
    ErasesPrefix (RxHistory.DeferredSource.afterXmitWith old cryptWork sendWork) Env.afterXmit := by
  unfold RxHistory.DeferredSource.afterXmitWith Env.afterXmit
  repeat' first
    | (tag_deferred_erase_at atom cryptWork; exact hc)
    | (tag_deferred_erase_at atom sendWork; exact hs)
    | (tag_deferred_erase_at atom requireDrainedPrefix; exact atoms.drained _ _)
    | tag_deferred_erasure_steps

theorem idle_erases
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietErases old)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit)
    (ht : ∀ j, ErasesPrefix (timers j) (Env.runTimers j))
    (hp : ∀ j, ErasesPrefix (placeholder j) (Env.runTimersPlaceholder j)) :
    ErasesPrefix (RxHistory.DeferredSource.idleWith old timers placeholder) Env.idleTimers := by
  unfold RxHistory.DeferredSource.idleWith Env.idleTimers
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | (tag_deferred_erase_at atom timers; exact ht _)
    | (tag_deferred_erase_at atom placeholder; exact hp _)
    | (tag_deferred_erase_at atom requireNothingDueAudit; exact atoms.nothingDue _)
    | tag_deferred_erasure_steps

theorem afterAdvance_erases
    (old : {α : Type} → RxHistory.Obs α → PrefixM E α) (atoms : QuietErases old)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit)
    (ht : ∀ j, ErasesPrefix (timers j) (Env.runTimers j))
    (hp : ∀ j, ErasesPrefix (placeholder j) (Env.runTimersPlaceholder j)) :
    ErasesPrefix (RxHistory.DeferredSource.afterAdvanceWith old timers placeholder) Env.afterAdvance := by
  unfold RxHistory.DeferredSource.afterAdvanceWith Env.afterAdvance
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | (tag_deferred_erase_at atom timers; exact ht _)
    | (tag_deferred_erase_at atom placeholder; exact hp _)
    | (tag_deferred_erase_at atom requireNothingDueAudit; exact atoms.nothingDue _)
    | tag_deferred_erasure_steps

end Leanux.Proofs.WG.Noise.DriverTags.Deferred
