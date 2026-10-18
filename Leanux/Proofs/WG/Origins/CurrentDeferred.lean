import Leanux.Proofs.WG.Origins.CurrentDevice
import Leanux.Proofs.WG.Origins.CurrentEnvironment
import Leanux.Proofs.WG.Origins.SupportEnvironment
import Leanux.Proofs.WG.Queues.RxEnvTimersHistory

/-! Current positional checks through the existing deferred worker observers.
The same audit focus records every reached lifetime action and failed prefix. -/
namespace Leanux.Proofs.WG.CurrentDeferred
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues CurrentLifecycle CurrentTraffic ConfiguredHandshake
open Origins hiding Inv

private abbrev Audited (g : AuditM α) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.Focused)
    RxHistory.Event.audit RxHistory.auditEvent g

private theorem native_audit (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (hm : Retaining.RetainsCall a)
    (hc : ∀ history, Preserves (Inv history) a) :
    Audited (auditFocus (liftWGObserver g)) :=
  ⟨Appends.focus _ _ _,
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.native_mixed)
      g a he hm hc⟩

private theorem focused_store (a : Leanux.M α) (hf : SameProductStore a) :
    Audited (liftPrefix a) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_lift)
    _ _ a (Retaining.of_view (Origins.kernel (project := id) hf))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.product_store) a hf)

private theorem store (a : Leanux.M α) (hf : SameProductStore a) :
    CurrentChecks.Preserves (liftPrefix a) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.lift_store) a hf

private theorem sendOne : CurrentChecks.Preserves (RxHistory.audit runOneSendWorkerAudit) := by
  have h : Audited runOneSendWorkerAudit := by
    unfold Audited runOneSendWorkerAudit
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_bind)
      RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) _ _ (focused_store _ (liftWG_sameProductStore getDev getDev_sameWGStore))
    intro d
    cases d.sendWorkQueue.head? with
    | none =>
      dsimp only
      exact focused_store _ (fun initial => productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi))
    | some headPid =>
      dsimp only
      apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_bind)
        RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) _ _ (focused_store (peekUnit .sendWorker) (by
          intro initial
          exact productAmbient_spec _ _ (fun _ _ hi => hi)))
      intro unit
      cases unit <;> dsimp only
      all_goals (apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_bind) RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl))
      · exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_pure) _ _ _
      · intro pid
        exact native_audit _ _ (runFlushedSendWorkPrefix_erases _) (Retaining.runFlushedSendWork_material _) (runFlushedSendWork_preserves _)
      · exact focused_store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi))
      · intro pid
        exact native_audit _ _ (runFlushedSendWorkPrefix_erases _) (Retaining.runFlushedSendWork_material _) (runFlushedSendWork_preserves _)
  exact h.2

private theorem clearOne : CurrentChecks.Preserves (RxHistory.audit runOneClearWorkerAudit) := by
  have h : Audited runOneClearWorkerAudit := by
    unfold Audited runOneClearWorkerAudit
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_bind)
      RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) _ _ (focused_store _ (liftWG_sameProductStore getDev getDev_sameWGStore))
    intro d
    cases d.clearWorkQueue.head? with
    | none =>
      dsimp only
      exact focused_store _ (fun initial => productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi))
    | some headPid =>
      dsimp only
      apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_bind)
        RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) _ _ (focused_store (peekUnit .clearPeerWorker) (by
          intro initial
          exact productAmbient_spec _ _ (fun _ _ hi => hi)))
      intro unit
      cases unit <;> dsimp only
      all_goals (apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_bind) RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl))
      · exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_pure) _ _ _
      · intro pid
        exact native_audit _ _ (runFlushedClearWorkPrefix_erases _) (Retaining.runFlushedClearWork_material _) (runFlushedClearWork_preserves _)
      · exact focused_store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi))
      · intro pid
        exact native_audit _ _ (runFlushedClearWorkPrefix_erases _) (Retaining.runFlushedClearWork_material _) (runFlushedClearWork_preserves _)
  exact h.2

private theorem drained (what : String) (queues : List Bool) :
    CurrentChecks.Preserves (RxHistory.mixed (requireDrainedPrefix what queues)) := by
  apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.mixed_store)
    _ _ (requireDrainedPrefix_erases _ _)
  have tail : SameProductStore (do
      let d ← (liftWG getDev : Leanux.M Device)
      if d.peers.toList.any (fun x => x.2.napiScheduled) then
        invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)") := by
    apply SameView.bind (liftWG_sameProductStore getDev getDev_sameWGStore)
    intro d
    split
    · intro initial; exact productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi)
    · exact SameView.pure _ _
  unfold Env.requireDrained
  by_cases h : queues.any id = true <;> simp only [h,↓reduceIte]
  · exact SameView.bind (fun initial => productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ hi => hi)) (fun _ => tail)
  · exact tail

macro "deferred_steps" : tactic => `(tactic| first
  | (current_env_at Env.deliverSent; exact store _ deliverSent_sameKernel)
  | (current_env_at Env.requireNoCryptWork; exact store _ requireNoCryptWork_sameKernel)
  | (current_env_at getWG
     exact store _ (fun initial => productGetWG_spec (fun s => s = initial)))
  | (current_env_at modifyWG
     exact store _ (fun initial => productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (current_env_at RxHistory.audit; first | exact sendOne | exact clearOne)
  | (current_env_at requireDrainedPrefix; exact drained _ _)
  | current_env_steps)

theorem runCryptWorkers : CurrentChecks.Preserves RxHistory.runCryptWorkers :=
  PrefixPreserves.bind (CurrentEnvironment.schedule none) (fun _ => store _ deliverSent_sameKernel)

theorem runSendWorkers : CurrentChecks.Preserves RxHistory.runSendWorkers := by
  unfold RxHistory.runSendWorkers
  repeat' first
    | (current_env_at RxHistory.schedule; exact CurrentEnvironment.schedule _)
    | deferred_steps

theorem afterXmit : CurrentChecks.Preserves RxHistory.afterXmit := by
  unfold RxHistory.afterXmit
  repeat' first
    | (current_env_at RxHistory.runCryptWorkers; exact runCryptWorkers)
    | (current_env_at RxHistory.runSendWorkers; exact runSendWorkers)
    | deferred_steps

private theorem clearEndpoint_view (pid : PeerId) :
    SameView ConfiguredIdentity.view (clearPeerEndpointSrc pid) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' configured_step initial


private theorem purge_view (pid : PeerId) :
    SameView ConfiguredIdentity.view (purgeStagedPackets pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDevice.«0».Leanux.Proofs.WG.CurrentLifecycle.purgeStaged_view) pid

macro "deferred_native_step " history:term : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc
     exact current_preserves _ (clearEndpoint_view _)
       (Retaining.of_view (Retaining.clearPeerEndpointSrc_material _)) $history)
  | (rx_retention_head purgeStagedPackets
     exact current_preserves _ (purge_view _)
       (Retaining.of_view (Retaining.purgeStagedPackets_material _)) $history)
  | (rx_retention_head delTimer
     exact current_preserves _ (ConfiguredIdentity.delTimer_view _ _)
       (Retaining.of_view (Retaining.delTimer_material _ _)) $history)
  | (rx_retention_head modPeerTimer
     exact current_preserves _ (ConfiguredIdentity.modPeerTimer_view _ _ _ _)
       (Retaining.of_view (Retaining.modPeerTimer_material _ _ _ _)) $history)
  | (rx_retention_head sendQueuedHandshakeInitiation
     exact sendQueuedHandshakeInitiation_preserves _ _ $history)
  | (rx_retention_head sendKeepalive; exact sendKeepalive_preserves _ $history)
  | current_traffic_step $history)

/-- Every actual timer case preserves both identity invariants on normal return.
The zero-key duplicate-work arm uses the actual conditional release relation. -/
theorem timerCallback_preserves (pid : PeerId) (timer : PeerTimer)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (timerCallback pid timer) := by
  cases timer <;> simp only [timerCallback]
  all_goals first
    | unfold expiredRetransmitHandshake
    | unfold expiredSendKeepalive
    | unfold expiredNewHandshake
    | unfold expiredZeroKeyMaterial
    | unfold expiredSendPersistentKeepalive
  all_goals try simp (config := {zeta := false}) only
    [branch,branchCmp,peekQueuedUnit,recordQueued,discard,map_const,Function.comp_def,map_eq_pure_bind]
  all_goals repeat' deferred_native_step history

private theorem focused_forIn (xs : List γ) (init : β)
    (f : γ → β → AuditM (ForInStep β)) (hf : ∀ x z, Audited (f x z)) :
    Audited (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_pure) _ _ _
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_bind)
      RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) _ _ (hf x init)
    intro step
    cases step with
    | done z => exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_pure) _ _ _
    | yield z => exact ih z

private theorem focused_range (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → AuditM (ForInStep β)) (hf : ∀ x z, Audited (f x z)) :
    Audited (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact focused_forIn _ _ _ hf

open Lean Meta Elab Tactic in
elab "deferred_audit_at " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Audited do throwError "not audited"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let mut action := args.back!.consumeMData
  for wrapper in [``auditFocus,``liftWGObserver] do
    if action.isAppOf wrapper then
      let fields := action.getAppArgs
      unless fields.size > 0 do throwError "missing focused action"
      action := fields.back!.consumeMData
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  if expected != ``liftPrefix && action.isAppOf ``liftPrefix then
    let fields := action.getAppArgs
    unless fields.size > 0 do throwError "missing lifted action"
    action := fields.back!.consumeMData
    if action.isAppOf ``liftWG then
      let fields := action.getAppArgs
      unless fields.size > 0 do throwError "missing WG action"
      action := fields.back!.consumeMData
  unless action.getAppFn.constName? == some expected do throwError "different observer"

open Lean Meta Elab Tactic in
elab "deferred_audit_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Audited do throwError "not audited"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let action := args.back!.consumeMData
  if let .letE _ _ value body _ := action then
    replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! (args.size-1) (body.instantiate1 value)))]
  else
    let next := action.headBeta
    if !Expr.equal action next then
      replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! (args.size-1) next))]
    else
      let some _ ← matchMatcherApp? action | throwError "not a reducible observer head"
      replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

private theorem audit_bind (g : AuditM α) (f : α → AuditM β)
    (hg : Audited g) (hf : ∀ x, Audited (f x)) : Audited (g >>= f) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_bind)
    RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) g f hg hf

private theorem saved : Audited getDevSavedAudit :=
  native_audit _ _ (erasesStatePrefix_lift getDev)
    (Retaining.of_view (Origins.sameView_of_sameWG (project := id) getDev_sameWGStore))
    (fun history => (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.native_store) getDev getDev_sameWGStore history)

private theorem audit_pure (x : α) : Audited (pure x) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_pure)
    RxHistory.Event.audit RxHistory.auditEvent x

macro "deferred_audit_steps" : tactic => `(tactic| first
  | (deferred_audit_at getDevSavedAudit; exact saved)
  | (deferred_audit_at delTimerPrefix
     exact native_audit _ _ (delTimerPrefix_erases _ _) (Retaining.of_view (Retaining.delTimer_material _ _))
       (fun history => current_preserves _ (ConfiguredIdentity.delTimer_view _ _) (Retaining.of_view (Retaining.delTimer_material _ _)) history))
  | (deferred_audit_at timerCallbackPrefix
     exact native_audit _ _ (timerCallbackPrefix_erases _ _) (Retaining.timerCallback_material _ _) (timerCallback_preserves _ _))
  | (deferred_audit_at Env.timerWorker; exact focused_store _ (timerWorker_sameKernel _))
  | (deferred_audit_at getWG; exact focused_store _ (fun initial => productGetWG_spec (fun s => s = initial)))
  | (deferred_audit_at modifyWG; exact focused_store _ (fun initial => productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (deferred_audit_at throw; exact focused_store _ (HistorySupport.source_throw _ _))
  | (deferred_audit_at Env.sectionAppearsLater
     exact focused_store _ (by
       apply (ProjectedAction.iff_run _ _ _).mpr
       intro w x v hr
       cases hr
       rfl))
  | (deferred_audit_at liftPrefix
     apply focused_store
     simp only [hidden,peekUnit,peekHiddenSite,resolveUnit,modifyAmbient,invariant,unsupported]
     intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))
  | (deferred_audit_at Pure.pure; exact audit_pure _)
  | (deferred_audit_at Bind.bind; apply audit_bind)
  | (deferred_audit_at ForIn.forIn; first | apply focused_range | apply focused_forIn)
  | (deferred_audit_at ite; split)
  | deferred_audit_reduce
  | support_intro)

private theorem wheelDue (d : Device) (j : UInt64) : Audited (wheelDueAudit d j) := by
  unfold wheelDueAudit
  exact native_audit _ _ (savedPeerLookupFlatMap_erases _ _ _) (Retaining.of_view (SameView.pure _ _))
    (fun _ => preserves_pure _)

private theorem wheelNextDue (d : Device) (j : UInt64) : Audited (wheelNextDueAudit d j) := by
  unfold wheelNextDueAudit
  exact audit_bind _ _ (wheelDue d j) (fun _ =>
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_pure) _ _ _)

private theorem stepComplete (b : UInt64) : Audited (requireStepCompleteAudit b) := by
  unfold requireStepCompleteAudit
  repeat' first
    | (deferred_audit_at wheelDueAudit; exact wheelDue _ _)
    | deferred_audit_steps

private theorem nothingDue (j : UInt64) : Audited (requireNothingDueAudit j) := by
  unfold requireNothingDueAudit
  repeat' first
    | (deferred_audit_at wheelNextDueAudit; exact wheelNextDue _ _)
    | deferred_audit_steps

private theorem audited_worker (worker : Worker) (body : AuditM Unit) (hb : Audited body) :
    Audited (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first | exact hb | deferred_audit_steps

private theorem timerSection (worker : Worker) (body : AuditM Unit) (hb : Audited body) :
    Audited (runTimerSectionAudit worker body) := by
  unfold runTimerSectionAudit
  repeat' first
    | (deferred_audit_at runWorkerPrefix; exact audited_worker worker body hb)
    | deferred_audit_steps

private theorem timerDispatch (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) : Audited (timerDispatchAudit worker pid timer we step) := by
  unfold timerDispatchAudit
  repeat' first
    | (deferred_audit_at requireStepCompleteAudit; exact stepComplete _)
    | (deferred_audit_at runTimerSectionAudit; apply timerSection)
    | deferred_audit_steps

private theorem placeholderPass (j : UInt64) : Audited (RxHistory.placeholderTimerPassAudit j) := by
  unfold RxHistory.placeholderTimerPassAudit
  repeat' first
    | (deferred_audit_at wheelNextDueAudit; exact wheelNextDue _ _)
    | (deferred_audit_at runTimerSectionAudit; apply timerSection)
    | deferred_audit_steps

macro "deferred_timer_steps" : tactic => `(tactic| first
  | (environment_at "runOneSendWorkerAudit"; exact sendOne)
  | (environment_at "runOneClearWorkerAudit"; exact clearOne)
  | (environment_at "placeholderTimerPassAudit"; exact (placeholderPass _).2)
  | (environment_at "wheelNextDueAudit"; exact (wheelNextDue _ _).2)
  | (environment_at "timerDispatchAudit"; exact (timerDispatch _ _ _ _ _).2)
  | (environment_at "requireStepCompleteAudit"; exact (stepComplete _).2)
  | (environment_at "requireNothingDueAudit"; exact (nothingDue _).2)
  | (environment_at "getDevSavedAudit"; exact saved.2)
  | (current_env_at peekSiteU64
     exact store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (current_env_at hiddenJiffies
     exact store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (current_env_at getEnv
     exact store _ (by
       apply (ProjectedAction.iff_run _ _ _).mpr
       intro w x v hr
       cases hr
       rfl))
  | (current_env_at throw; exact store _ (HistorySupport.source_throw _ _))
  | (current_env_at Env.peekNextSite; exact store _ peekNextSite_sameKernel)
  | (current_env_at Env.timerWorker; exact store _ (timerWorker_sameKernel _))
  | environment_reduce
  | environment_join
  | environment_join_use
  | deferred_steps)

theorem runTimers (j : UInt64) : CurrentChecks.Preserves (RxHistory.runTimers j) := by
  change PrefixPreserves CurrentChecks.Inv CurrentChecks.Safe _
  unfold RxHistory.runTimers
  repeat' first
    | (current_env_at RxHistory.runCryptWorkers; exact runCryptWorkers)
    | deferred_timer_steps

theorem runTimersPlaceholder (j : UInt64) : CurrentChecks.Preserves (RxHistory.runTimersPlaceholder j) := by
  change PrefixPreserves CurrentChecks.Inv CurrentChecks.Safe _
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | (current_env_at RxHistory.runCryptWorkers; exact runCryptWorkers)
    | (current_env_at RxHistory.runSendWorkers; exact runSendWorkers)
    | deferred_timer_steps

theorem idleTimers : CurrentChecks.Preserves RxHistory.idleTimers := by
  change PrefixPreserves CurrentChecks.Inv CurrentChecks.Safe _
  unfold RxHistory.idleTimers
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (current_env_at RxHistory.runTimers; exact runTimers _)
    | (current_env_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder _)
    | deferred_timer_steps

theorem afterAdvance : CurrentChecks.Preserves RxHistory.afterAdvance := by
  change PrefixPreserves CurrentChecks.Inv CurrentChecks.Safe _
  unfold RxHistory.afterAdvance
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (current_env_at RxHistory.runTimers; exact runTimers _)
    | (current_env_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder _)
    | deferred_timer_steps

private theorem idleDevice : CurrentChecks.Preserves (RxHistory.mixed requireIdleDevicePrefix) := by
  apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.mixed_store)
    _ _ requireIdleDevicePrefix_erases
  unfold Env.requireIdleDevice
  apply SameView.bind requireNoCryptWork_sameKernel
  intro _
  apply SameView.bind (liftWG_sameProductStore getDev getDev_sameWGStore)
  intro d
  split
  · intro initial; exact productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ hi => hi)
  · exact SameView.pure _ _

/-- All fourteen actual deferred-call constructors retain positional checks,
including records emitted before a Stop. Incoming journals remain arbitrary. -/
theorem deferred (call : EnvDeferredCall) : CurrentChecks.Preserves (RxHistory.deferred call) := by
  cases call with
  | drained what queues => exact drained what queues
  | idleDevice => exact idleDevice
  | noCrypt => exact (focused_store _ requireNoCryptWork_sameKernel).2
  | crypt => exact runCryptWorkers
  | sendOne => exact sendOne
  | clearOne => exact clearOne
  | sendAll => exact runSendWorkers
  | afterXmit => exact afterXmit
  | timerWorker timer => exact (focused_store _ (timerWorker_sameKernel timer)).2
  | timers j => exact runTimers j
  | placeholder j => exact runTimersPlaceholder j
  | idle => exact idleTimers
  | advance ticks => exact (focused_store _ (advance_sameKernel ticks)).2
  | afterAdvance => exact afterAdvance

end Leanux.Proofs.WG.CurrentDeferred
