import Leanux.Proofs.WG.Origins.JointOwnerDevice
import Leanux.Proofs.WG.Origins.OwnerDeviceCreation
import Leanux.Proofs.WG.Origins.OwnerWorkers
import Leanux.Proofs.Logged.FocusedInvariant
import Leanux.Proofs.WG.Queues.JointSyscallLifecycle

/-! Owner checks at actual configuration and control call boundaries. Native
state preservation is normal-return only; observer contracts keep failed
prefixes and arbitrary incoming product histories. -/
namespace Leanux.Proofs.WG.OwnerControlCalls
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration OwnerBounds OwnerControls

private theorem safe (h : List RxHistory.Event) (w : World) (hi : OwnerChecks.Inv h w) :
    OwnerChecks.Safe h := hi.safe

/-- The live-state part observes WG store fields; saved checks continue to refer
only to the immutable historical worlds already in the incoming journal. -/
theorem store (h : List RxHistory.Event) (w v : World)
    (eq : wgStoreView v.wg = wgStoreView w.wg) (hi : OwnerChecks.Inv h w) :
    OwnerChecks.Inv h v := by
  have kept : OwnerChecks.Inv h {w with wg := v.wg} := OwnerWorkers.store h w _
    (by simp only [productStoreView,eq]) hi
  exact ⟨kept.current,⟨kept.boundary.audit,kept.boundary.distinct,kept.boundary.released⟩,kept.carrier,kept.checked⟩

theorem lift_spec (a : Leanux.M α)
    (ha : ∀ h, Preserves (OwnerChecks.Inv h) a) : OwnerChecks.Preserves (liftPrefix a) :=
  (PrefixEnsures.lift a safe (fun h w x v hi hr => (hoare_iff_run _ _ _).mp (ha h) w x v hi hr)).preserves

theorem lift_store (a : Leanux.M α) (ha : SameProductStore a) :
    OwnerChecks.Preserves (liftPrefix a) := by
  apply lift_spec
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact OwnerWorkers.store h w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hi

theorem lift_wgStore (a : Leanux.M α)
    (ha : SameView (fun w : World => wgStoreView w.wg) a) :
    OwnerChecks.Preserves (liftPrefix a) := by
  apply lift_spec
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact store h w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hi

theorem lift_fs (a : FS.M α) : OwnerChecks.Preserves (liftPrefix (liftFS a)) :=
  lift_spec _ (fun h => productFS_spec a (OwnerChecks.Inv h) (fun w _ _ _ hi => store h w _ rfl hi))

theorem lift_task (a : TaskM α) : OwnerChecks.Preserves (liftPrefix (liftTask a)) :=
  lift_spec _ (fun h => productTask_spec a (OwnerChecks.Inv h) (fun w _ _ hi => store h w _ rfl hi))

theorem lift_ambient (a : AmbientM α) : OwnerChecks.Preserves (liftPrefix (liftAmbient a)) :=
  lift_spec _ (fun h => productAmbient_spec a (OwnerChecks.Inv h) (fun w _ hi => store h w _ rfl hi))

theorem lift_seccomp (a : Seccomp.M α) : OwnerChecks.Preserves (liftPrefix (liftSeccomp a)) :=
  lift_spec _ (fun h => productSeccomp_spec a (OwnerChecks.Inv h) (fun w _ _ _ hi => store h w _ rfl hi))

theorem lift_get : OwnerChecks.Preserves (liftPrefix (get : Leanux.M World)) :=
  lift_spec _ (fun _ => hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))

theorem lift_modify (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    OwnerChecks.Preserves (liftPrefix (modify f)) :=
  lift_spec _ (fun h => hoare_modify _ (fun w hi => store h w (f w) (same w) hi))

private theorem socket_owner {α : Type} (a : WG.M α) (hf : SameSocket a) :
    Preserves Carrier a :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.JointOwnerDevice.«0».Leanux.Proofs.WG.JointOwnerDevice.socket_owner) a hf

theorem wgUp_preserves : Preserves Carrier WG.wgUp := by
  have opened : Preserves Carrier wgOpen := by
    unfold wgOpen
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (allocation_release_head socketInit; exact socket_owner _ (socketInit_sameSocket _))
      | (allocation_release_head sendKeepalive; exact OwnerPeerConfiguration.sendKeepalive_preserves _)
      | (allocation_release_head sendStagedPackets; exact OwnerCompletion.sendStagedPackets_preserves _)
      | owner_control_step
  unfold WG.wgUp
  repeat' first
    | (allocation_release_head wgOpen; exact opened)
    | owner_control_step

theorem netnsPreExit_preserves : Preserves Carrier netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head socketReinit
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDevice.«0».Leanux.Proofs.WG.OwnerDevice.socketReinit_preserves) _ _)
    | (allocation_release_head clearPeerEndpointSrc
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.JointOwnerDevice.«0».Leanux.Proofs.WG.JointOwnerDevice.clearEndpoint_owner) _)
    | owner_control_step

open Lean Meta Elab Tactic in
elab "owner_outer_callback" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``OwnerChecks.Preserves || target.isAppOf ``PrefixPreserves do
    throwError "not an owner prefix contract"
  let parts := target.getAppArgs
  unless parts.size > 0 do throwError "missing observer"
  unless parts.back!.consumeMData.headBeta.getAppFn.isFVar do throwError "not a callback"
  evalTactic (← `(tactic| assumption))

macro "owner_outer_step" : tactic => `(tactic| first
  | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_at unsupported; exact lift_ambient (AmbientM.unsupported _))
  | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_at skipCut; exact lift_ambient (AmbientM.skipCut _))
  | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_at liftPrefix; first
      | exact lift_fs _
      | exact lift_task _
      | exact lift_ambient _
      | exact lift_seccomp _
      | exact lift_get
      | exact lift_modify _ (fun _ => rfl))
  | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_at Pure.pure; exact PrefixPreserves.pure safe _)
  | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_at ite; apply PrefixPreserves.ite)
  | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_at dite; split)
  | (maintenance_intro; try dsimp only)
  | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_match))

/-- The callback is an arbitrary actual product observer, including its Stops.
Descriptor failure returns before calling it, exactly as in the source. -/
theorem socketCallOn (fd : Nat) (body : RxHistory.Obs Int)
    (hb : OwnerChecks.Preserves body) :
    OwnerChecks.Preserves (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold socketCallOnWith
  apply PrefixPreserves.bind (lift_fs (fdget fd))
  intro f
  apply PrefixPreserves.ite
  · intro _; exact PrefixPreserves.pure safe _
  · intro _
    exact hb.bind (fun ret => (lift_fs (fdput f)).bind (fun _ => PrefixPreserves.pure safe ret))

theorem netlinkRequest (body : RxHistory.Obs Int) (hb : OwnerChecks.Preserves body) :
    OwnerChecks.Preserves (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply PrefixPreserves.bind
    (socketCallOn _ _ ((lift_ambient (AmbientM.skipCut allocCuts)).bind
      (fun _ => hb.bind (fun ret => (lift_ambient (AmbientM.skipCut allocCuts)).bind
        (fun _ => PrefixPreserves.pure safe ret)))))
  intro ret
  exact (socketCallOn _ _ (PrefixPreserves.pure safe 0)).bind (fun _ => PrefixPreserves.pure safe ret)

theorem rtnetlinkRequest (body : RxHistory.Obs Int) (hb : OwnerChecks.Preserves body) :
    OwnerChecks.Preserves (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_at socketCallOnWith; apply socketCallOn)
    | owner_outer_step


abbrev Audited (g : AuditM α) :=
  FocusedInvariant OwnerChecks.Inv OwnerChecks.Safe RxHistory.Event.audit RxHistory.auditEvent g

theorem audit_lift (a : Leanux.M α) (ha : OwnerChecks.Preserves (liftPrefix a)) :
    Audited (liftPrefix a) := FocusedInvariant.lift _ _ a ha

private theorem audit_native (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (erases : ErasesStatePrefix g a)
    (allocation : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe g)
    (material : Origins.Retaining.RetainsCall a)
    (current : ∀ history, Preserves (CurrentLifecycle.Inv history) a)
    (owner : Preserves Carrier a) : Audited (auditFocus (liftWGObserver g)) :=
  ⟨Appends.focus _ _ _,OwnerChecks.native_mixed g a erases allocation material current
    (fun _ => hoare_consequence owner (fun _ hi => hi.2) (fun _ _ hi => hi))⟩

private theorem idle_store : SameProductStore Env.requireIdleDevice := by
  unfold Env.requireIdleDevice
  apply SameView.bind requireNoCryptWork_sameKernel
  intro _
  apply SameView.bind (liftWG_sameProductStore getDev getDev_sameWGStore)
  intro d
  split
  · intro initial; exact productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ hi => hi)
  · exact SameView.pure _ _

private theorem audit_idle : Audited (auditFocus requireIdleDevicePrefix) := by
  refine ⟨Appends.focus _ _ _,?_⟩
  apply OwnerChecks.quiet _ (Appends.focus _ _ _)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      Origins.HistorySupport.sensitive (fun _ => rfl) requireIdleDevicePrefix)
    (CurrentDeferred.deferred .idleDevice)
    (RxHistory.mixed_preserves requireIdleDevicePrefix_allocation)
  intro w h hi x v hr
  have run := (RxHistory.mixed_erases requireIdleDevicePrefix_erases w h).symm.trans hr
  exact (OwnerWorkers.store h w v ((ProjectedAction.iff_run _ _ _).mp idle_store w x v run) hi).carrier

private theorem inetdevDestroy_store : SameProductStore Env.inetdevDestroy :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.inetdevDestroy_store)

open Lean Meta Elab Tactic in
elab "owner_control_audit_at " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Audited || target.isAppOf ``FocusedInvariant do throwError "not an owner audit contract"
  let fields := target.getAppArgs
  unless fields.size > 0 do throwError "missing observer"
  let mut action := fields.back!.consumeMData.headBeta
  for wrapper in [``auditFocus,``liftWGObserver] do
    if action.isAppOf wrapper then
      let parts := action.getAppArgs
      unless parts.size > 0 do throwError "missing wrapped observer"
      action := parts.back!.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  if expected != ``liftPrefix && action.isAppOf ``liftPrefix then
    let parts := action.getAppArgs
    unless parts.size > 0 do throwError "missing lifted action"
    action := parts.back!.consumeMData.headBeta
    if action.isAppOf ``liftWG then
      let parts := action.getAppArgs
      unless parts.size > 0 do throwError "missing native action"
      action := parts.back!.consumeMData.headBeta
  unless action.getAppFn.constName? == some expected do throwError "different action head"

open Lean Meta Elab Tactic in
elab "owner_control_audit_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Audited || target.isAppOf ``FocusedInvariant || target.isAppOf ``PrefixPreserves do throwError "not an owner audit contract"
  let fields := target.getAppArgs
  unless fields.size > 0 do throwError "missing observer"
  let action := fields.back!.consumeMData
  if let .letE _ _ value body _ := action then
    replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn
      (fields.set! (fields.size-1) (body.instantiate1 value)))]
  else
    let reduced := action.headBeta
    if !Expr.equal action reduced then
      replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn
        (fields.set! (fields.size-1) reduced))]
    else
      let some _ ← matchMatcherApp? action | throwError "not an observer matcher"
      replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

macro "owner_control_audit_steps" : tactic => `(tactic| first
  | (owner_control_audit_at wgUpPrefix
     exact audit_native _ _ wgUpPrefix_erases (DeviceControlCall.allocation .up)
       Origins.Retaining.wgUp_material CurrentRemaining.wgUp_preserves wgUp_preserves)
  | (owner_control_audit_at wgDownPrefix
     exact audit_native _ _ wgDownPrefix_erases (DeviceControlCall.allocation .down)
       Origins.Retaining.wgDown_material CurrentLifecycle.wgDown_preserves OwnerDevice.wgDown_preserves)
  | (owner_control_audit_at wgDestructPrefix
     exact audit_native _ _ wgDestructPrefix_erases (DeviceLifecycleCall.allocation .destruct)
       Origins.Retaining.wgDestruct_material CurrentLifecycle.wgDestruct_preserves OwnerDevice.wgDestruct_preserves)
  | (owner_control_audit_at netnsPreExitPrefix
     exact audit_native _ _ netnsPreExitPrefix_erases (DeviceControlCall.allocation .preExit)
       (Origins.Retaining.of_view Origins.Retaining.netnsPreExit_material)
       CurrentRemaining.netnsPreExit_preserves netnsPreExit_preserves)
  | (owner_control_audit_at requireIdleDevicePrefix; exact audit_idle)
  | (owner_control_audit_at getDev; exact audit_lift _ (lift_store _ (liftWG_sameProductStore _ getDev_sameWGStore)))
  | (owner_control_audit_at mayHaveSlept; exact audit_lift _ (lift_store _ (liftWG_sameProductStore _ mayHaveSlept_sameWGStore)))
  | (owner_control_audit_at Env.inetdevDestroy
     exact audit_lift _ (lift_store _ inetdevDestroy_store))
  | (owner_control_audit_at getWG; exact audit_lift _ (lift_store _ (fun initial => productGetWG_spec (fun s => s = initial))))
  | (owner_control_audit_at getRouting
     exact audit_lift _ (lift_store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl)))
  | (owner_control_audit_at modifyEnv; exact audit_lift _ (lift_modify _ (fun _ => rfl)))
  | (owner_control_audit_at modifyRouting
     exact audit_lift _ (lift_store _ (fun initial => productRouting_spec _ (fun s => s = initial))))
  | (owner_control_audit_at liftM
     exact audit_lift _ (lift_store _ (fun initial => productRouting_spec _ (fun s => s = initial))))
  | (owner_control_audit_at liftPrefix
     apply audit_lift
     simp only [hidden,peekUnit,resolveUnit,modifyAmbient,unsupported,skipCut]
     exact lift_ambient _)
  | (owner_control_audit_at Pure.pure; exact FocusedInvariant.pure _ _ safe _)
  | (owner_control_audit_at Bind.bind; apply FocusedInvariant.bind
      (encode := RxHistory.Event.audit) (decode := RxHistory.auditEvent) (fun _ => rfl))
  | (owner_control_audit_at ite; apply FocusedInvariant.ite)
  | owner_control_audit_reduce
  | support_intro)

private theorem audit_worker (worker : Worker) (body : AuditM Unit) (hb : Audited body) :
    Audited (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first | exact hb | owner_control_audit_steps

theorem up : OwnerChecks.Preserves (RxHistory.audit envWgUpAudit) := by
  have contract : Audited envWgUpAudit := by
    unfold envWgUpAudit
    repeat' owner_control_audit_steps
  exact contract.2

theorem down : OwnerChecks.Preserves (RxHistory.audit envWgDownAudit) := by
  have contract : Audited envWgDownAudit := by
    unfold envWgDownAudit
    repeat' owner_control_audit_steps
  exact contract.2

theorem delete : OwnerChecks.Preserves (RxHistory.audit envWgDeleteAudit) := by
  have contract : Audited envWgDeleteAudit := by
    unfold envWgDeleteAudit
    repeat' owner_control_audit_steps
  exact contract.2

theorem netnsCleanup : OwnerChecks.Preserves (RxHistory.audit envNetnsCleanupAudit) := by
  have contract : Audited envNetnsCleanupAudit := by
    unfold envNetnsCleanupAudit
    repeat' first
      | (owner_control_audit_at runWorkerPrefix; apply audit_worker)
      | owner_control_audit_steps
  exact contract.2


private theorem syscall_tail_preserves (call : Syscall) (dispatch : RxHistory.Obs Int)
    (sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit)
    (hd : OwnerChecks.Preserves dispatch) (hs : OwnerChecks.Preserves sendWorkers)
    (ht : OwnerChecks.Preserves timers) (hr : OwnerChecks.Preserves route)
    (hx : OwnerChecks.Preserves xmit) (ha : OwnerChecks.Preserves advance)
    (hc : OwnerChecks.Preserves cleanup) :
    OwnerChecks.Preserves (do
      let ret ← dispatch
      for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
      liftPrefix (liftFS taskWorkRun)
      match call with
      | .wgSet _ | .wgInject .. => sendWorkers; timers
      | .wgUp => sendWorkers; timers; route
      | .wgXmit .. => xmit; timers
      | .wgBatch .. => timers
      | .wgAdvance _ => advance
      | .wgNetnsClose => cleanup
      | _ => pure ()
      match call with
      | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
      | .wgAddroute .. | .wgAddaddr .. =>
        let shape := Net.Fib.shape (← liftPrefix getRouting)
        liftPrefix (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie",shape)]})
      | _ => pure ()
      pure ret) := by
  have routing : OwnerChecks.Preserves (liftPrefix (getRouting : Leanux.M Net.Routing)) :=
    lift_store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run; rfl)
  apply PrefixPreserves.bind hd
  intro ret
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn _ _ _ safe
    intro c acc
    exact (lift_seccomp (Seccomp.enterHarnessCall c)).bind (fun _ => PrefixPreserves.pure safe _)
  · intro _
    apply PrefixPreserves.bind (lift_fs taskWorkRun)
    intro _
    cases call
    all_goals dsimp only
    all_goals repeat' first
      | owner_outer_callback
      | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_at getRouting; exact routing)
      | owner_outer_step

private theorem syscall_entry_preserves (call : Syscall) (body : RxHistory.Obs Int)
    (hb : OwnerChecks.Preserves body) : OwnerChecks.Preserves (do
  liftPrefix (modify fun w => { w with fs := {w.fs with userOut := none, userFds := none}, seccomp := {w.seccomp with emitted := {}, translatedLen := none} })
  liftPrefix (modifyWG fun g => {g with queuedThisCall := []})
  liftPrefix (modifyAmbient fun a => {a with steps := #[],extraOut := [],fired := #[],netRxSections := 0,netRxSection := 0})
  match syscallNr call with
  | some nr => liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none =>
    if call.isNet && (← liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  body) := by
  have current : OwnerChecks.Preserves (liftPrefix Leanux.getCurrent) := by
    unfold Leanux.getCurrent
    exact lift_fs (StateT.lift TaskM.getCurrent)
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  apply PrefixPreserves.bind
  · apply lift_modify
    intro w
    rfl
  intro _
  apply PrefixPreserves.bind
  · apply lift_modify
    intro w
    rfl
  intro _
  apply PrefixPreserves.bind
  · apply lift_modify
    intro w
    rfl
  intro _
  cases hn : syscallNr call
  all_goals repeat' first
    | owner_outer_callback
    | (change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _; current_env_at Leanux.getCurrent; exact current)
    | owner_outer_step
    | owner_control_audit_reduce

/-- Exact entry resets, dispatch, wait callbacks and final FIB observation.
Every callback retains its full actual product observer domain. -/
theorem syscallWith_preserves (call : Syscall) (dispatch : RxHistory.Obs Int)
    (sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit)
    (hd : OwnerChecks.Preserves dispatch) (hs : OwnerChecks.Preserves sendWorkers)
    (ht : OwnerChecks.Preserves timers) (hr : OwnerChecks.Preserves route)
    (hx : OwnerChecks.Preserves xmit) (ha : OwnerChecks.Preserves advance)
    (hc : OwnerChecks.Preserves cleanup) :
    OwnerChecks.Preserves (syscallWith (fun {_} a => liftPrefix a)
      dispatch sendWorkers timers route xmit advance cleanup call) := by
  exact syscall_entry_preserves call _
    (syscall_tail_preserves call dispatch sendWorkers timers route xmit advance cleanup hd hs ht hr hx ha hc)

/-- Concrete dispatch of set-device attributes invokes the existing observer
once inside both actual netlink socket transactions. -/
theorem dispatchSet (attrs : DeviceAttrs) :
    OwnerChecks.Preserves (RxHistory.syscallDispatch (.wgSet attrs)) := by
  change OwnerChecks.Preserves (RxHistory.audit (netlinkRequestAudit
    (auditFocus (liftWGObserver (wgSetDevicePrefix attrs)))))
  rw [netlinkRequestAudit_factor]
  unfold RxHistory.audit
  rw [← netlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (auditFocus (liftWGObserver (wgSetDevicePrefix attrs))) (Appends.focus _ _ _)]
  exact netlinkRequest _ (JointOwnerDevice.wgSetDevice_checked attrs)

theorem create : OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver wgCreatePrefix)) := by
  apply OwnerChecks.native_mixed _ _ wgCreatePrefix_erases wgCreatePrefix_allocation
    Origins.Retaining.wgCreate_material CurrentLifecycle.wgCreate_preserves
  intro history
  exact hoare_consequence OwnerDeviceCreation.wgCreate_preserves
    (fun _ hi => hi.2) (fun _ _ hi => hi)

theorem dispatchCreate : OwnerChecks.Preserves (RxHistory.syscallDispatch .wgCreate) := by
  change OwnerChecks.Preserves (RxHistory.audit (rtnetlinkRequestAudit
    (auditFocus (liftWGObserver wgCreatePrefix))))
  rw [rtnetlinkRequestAudit_factor]
  unfold RxHistory.audit
  rw [← rtnetlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (auditFocus (liftWGObserver wgCreatePrefix)) (Appends.focus _ _ _)]
  exact rtnetlinkRequest _ create

theorem audit_socket (fd : Nat) (body : AuditM Int) (append : Appends body)
    (hb : OwnerChecks.Preserves (RxHistory.audit body)) :
    OwnerChecks.Preserves (RxHistory.audit (socketCallOnAudit fd body)) := by
  rw [socketCallOnAudit_factor]
  apply OwnerChecks.congr (socketCallOn fd _ hb)
  intro w h
  exact socketCallOnWith_focuses RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    fd (FocusesUnder.focus body) append w h True.intro

theorem dispatchUp : OwnerChecks.Preserves (RxHistory.syscallDispatch .wgUp) := by
  apply audit_socket SENDER_FD envWgUpAudit
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.up).1 up

theorem dispatchDown : OwnerChecks.Preserves (RxHistory.syscallDispatch .wgDown) := by
  apply audit_socket SENDER_FD envWgDownAudit
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.down).1 down

theorem dispatchDelete : OwnerChecks.Preserves (RxHistory.syscallDispatch .wgDelete) := by
  change OwnerChecks.Preserves (RxHistory.audit (rtnetlinkRequestAudit envWgDeleteAudit))
  rw [rtnetlinkRequestAudit_factor]
  unfold RxHistory.audit
  rw [← rtnetlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    _ (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.delete).1]
  exact rtnetlinkRequest _ delete

theorem dispatchNetnsClose : OwnerChecks.Preserves (RxHistory.syscallDispatch .wgNetnsClose) := by
  change OwnerChecks.Preserves (RxHistory.audit (liftPrefix Leanux.netnsClose))
  exact (audit_lift _ (lift_wgStore _ SyscallFrames.netnsClose_sameWGStore)).2

private theorem carrier_scalar (w v : World) (hi : Carrier w.wg)
    (same : envScalarView v = envScalarView w) : Carrier v.wg := by
  have fields : v.wg.dev.map (fun d => (d.nextPeer,d.nextKeypairId,d.keypairs,d.rxSkbs)) =
      w.wg.dev.map (fun d => (d.nextPeer,d.nextKeypairId,d.keypairs,d.rxSkbs)) := by
    have eq := congrArg (fun s : ProductStore43 =>
      s.2.2.2.dev.map (fun d => (d.nextPeer,d.nextKeypairId,d.keypairs,d.rxSkbs))) same
    simpa only [envScalarView,envScalarStore,productStoreView,wgStoreView,
      envScalarDevice,Option.map_map,Function.comp_def] using eq
  have old (d : Device) (hd : v.wg.dev = some d) :
      ∃ before, w.wg.dev = some before ∧ before.nextPeer = d.nextPeer ∧
        before.nextKeypairId = d.nextKeypairId ∧ before.keypairs = d.keypairs ∧ before.rxSkbs = d.rxSkbs := by
    have eq : w.wg.dev.map (fun d => (d.nextPeer,d.nextKeypairId,d.keypairs,d.rxSkbs)) =
        some (d.nextPeer,d.nextKeypairId,d.keypairs,d.rxSkbs) :=
      fields.symm.trans (by simp only [hd,Option.map_some])
    obtain ⟨before,hb,props⟩ := Option.map_eq_some_iff.mp eq
    exact ⟨before,hb,by simpa only [Prod.mk.injEq] using props⟩
  constructor
  · intro d hd id key hk valid pid word
    obtain ⟨before,hb,peer,_,keys,_⟩ := old d hd
    rw [← peer]
    exact hi.owners before hb id key (by simpa only [keys] using hk) valid pid word
  · intro d id pkt hd hp other key ho hk
    have eq : other = d := Option.some.inj (ho.symm.trans hd)
    subst other
    obtain ⟨before,hb,_,_,keys,rx⟩ := old d hd
    exact hi.compatible before id pkt hb (by simpa only [rx] using hp)
      before key hb (by simpa only [keys] using hk)
  · intro d hd id pkt hp
    obtain ⟨before,hb,_,frontier,_,rx⟩ := old d hd
    rw [← frontier]
    exact hi.rxKeys before hb id pkt (by simpa only [rx] using hp)

/-- MTU and address-device flags may change; owner and captured identity
checks are retained without requiring an exact device or product-store frame. -/
theorem mtu (n : Nat) : OwnerChecks.Preserves (RxHistory.audit (setMtuAudit n)) := by
  apply OwnerChecks.combine _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.mtu) n).2
    (RxHistory.audit_preserves _ (setMtuAudit_preserves n))
  · intro w h hi x v hr
    have run := (RxHistory.audit_erases (setMtuAudit_erases n) w h).symm.trans hr
    exact carrier_scalar w v hi.carrier
      ((ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w x v run)
  · intro w h hi
    change OwnerChecks.Checks (h ++ ((h.filterMap RxHistory.auditEvent).drop
      (h.filterMap RxHistory.auditEvent).length).map RxHistory.Event.audit)
    simpa using hi.checked

open NetlinkDump JointOwnerConfiguration

private theorem dump_preserves (a : WG.M α) (frame : SameDump a)
    (history : List SessionOrigin.Receipt) : Preserves (JointOwnerConfiguration.Inv history) a := by
  apply (pinned_const _private.Leanux.Proofs.WG.Origins.JointOwnerConfiguration.«0».Leanux.Proofs.WG.JointOwnerConfiguration.combine) a history
  · apply ConfiguredHandshake.current_preserves a
      (frame.of_factor (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state)
        ConfiguredIdentity.view (fun _ => rfl))
      (Origins.Retaining.of_view (Origins.Retaining.dump_material frame)) history
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v finalAmbient hi hr
    exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
      hi (congrArg WGStoreView.dev
        ((ProjectedAction.iff_run_ambient _ _ _).mp frame w ambient result v finalAmbient hr))

private theorem dump_readPeer (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (getPeer pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.JointOwnerConfiguration.«0».Leanux.Proofs.WG.JointOwnerConfiguration.combine) _ history
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentLifecycle.«0».Leanux.Proofs.WG.CurrentLifecycle.readPeer_preserves) pid history)
    (OwnerControls.readPeer pid)

macro "owner_dump_step " history:term : tactic => `(tactic| first
  | (rx_retention_head getPeer; exact dump_readPeer _ $history)
  | (rx_retention_head getPeerDump
     exact dump_preserves _ ((getPeerDump_sameWGWorld _ _ _).factor dumpView) $history)
  | (rx_retention_head getNlSock
     exact dump_preserves _ ((getNlSock_sameWGWorld _).factor dumpView) $history)
  | (rx_retention_head setNlSock
     exact dump_preserves _ (setNlSock_sameDump _ _) $history)
  | (rx_retention_head lookupInterface
     exact dump_preserves _ ((lookupInterface_sameWGWorld _).factor dumpView) $history)
  | (rx_retention_head coalesce
     exact dump_preserves _ ((coalesce_sameWGWorld _).factor dumpView) $history)
  | joint_configuration_step $history)

theorem wgGetDeviceDone_preserves (ctx : DumpCtx) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' owner_dump_step history

theorem deviceDumpTail_preserves (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' owner_dump_step history

theorem wgGetDeviceDump_preserves (ctx : DumpCtx) (seq : Nat) (skb : NlSkb)
    (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource
       exact dump_preserves _ ((deviceDumpHeader_sameWGStore _ _ _ _).factor dumpStore) history)
    | (rx_retention_head deviceDumpTailSource; exact deviceDumpTail_preserves _ _ _ _ _ history)
    | owner_dump_step history

theorem netlinkDump_preserves (fd : Nat) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (netlinkDump fd) := by
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact wgGetDeviceDump_preserves _ _ _ history)
    | (rx_retention_head wgGetDeviceDone; exact wgGetDeviceDone_preserves _ history)
    | owner_dump_step history

theorem netlinkDumpStart_preserves (fd : Nat) (ref : DeviceRef)
    (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact netlinkDump_preserves _ history)
    | owner_dump_step history

theorem netlinkRecvmsg_preserves (fd : Nat) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact netlinkDump_preserves _ history)
    | owner_dump_step history

theorem wgGetDevice_preserves (ref : DeviceRef) (history : List SessionOrigin.Receipt) :
    Preserves (JointOwnerConfiguration.Inv history) (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact netlinkDumpStart_preserves _ _ history)
    | (rx_retention_head netlinkRecvmsg; exact netlinkRecvmsg_preserves _ history)
    | owner_dump_step history

/-- Every existing dump observer keeps the identical lifetime journal and
actual cursor payments, including failed prefixes and normal errno returns. -/
theorem dump_checked (call : NetlinkDumpCall) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver call.observed)) := by
  apply OwnerConfiguration.native_mixed call.observed call.original call.erases call.allocation
  · cases call with
    | peer pid ctx skb => exact Origins.Retaining.of_view ((getPeerDump_sameWGWorld pid ctx skb).factor Origins.view)
    | chunk ctx seq skb => exact Origins.Retaining.of_view (Origins.Retaining.wgGetDeviceDump_material ctx seq skb)
    | done ctx => exact Origins.Retaining.of_view (Origins.Retaining.wgGetDeviceDone_material ctx)
    | dump fd => exact Origins.Retaining.of_view (Origins.Retaining.netlinkDump_material fd)
    | start fd ref => exact Origins.Retaining.of_view (Origins.Retaining.netlinkDumpStart_material fd ref)
    | receive fd => exact Origins.Retaining.of_view (Origins.Retaining.netlinkRecvmsg_material fd)
    | device ref => exact Origins.Retaining.of_view (Origins.Retaining.wgGetDevice_material ref)
  · intro allocation history
    apply hoare_consequence (P := JointOwnerConfiguration.Inv history)
      (Q := fun _ => JointOwnerConfiguration.Inv history) ?_
      (fun _ hi => hi.2) (fun _ _ hi => hi)
    cases call with
    | peer pid ctx skb => exact dump_preserves _ ((getPeerDump_sameWGWorld pid ctx skb).factor dumpView) history
    | chunk ctx seq skb => exact wgGetDeviceDump_preserves ctx seq skb history
    | done ctx => exact wgGetDeviceDone_preserves ctx history
    | dump fd => exact netlinkDump_preserves fd history
    | start fd ref => exact netlinkDumpStart_preserves fd ref history
    | receive fd => exact netlinkRecvmsg_preserves fd history
    | device ref => exact wgGetDevice_preserves ref history

private theorem dump_store (h : List RxHistory.Event) (w v : World)
    (same : dumpView v.wg = dumpView w.wg) (hi : OwnerChecks.Inv h w) :
    OwnerChecks.Inv h v := by
  let repaired : World := {v with wg := {v.wg with nlSock7 := w.wg.nlSock7, nlSock8 := w.wg.nlSock8}}
  have frame : wgStoreView repaired.wg = wgStoreView w.wg :=
    congrArg (fun s : WGStoreView => {s with nlSock7 := w.wg.nlSock7, nlSock8 := w.wg.nlSock8}) same
  have kept := store h w repaired frame hi
  exact ⟨kept.current,
    ⟨⟨allocationDumpStable _ _ _ same hi.boundary.audit.1,hi.boundary.audit.2⟩,
      kept.boundary.distinct,kept.boundary.released⟩,
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
      kept.carrier (show v.wg.dev = repaired.wg.dev from rfl),kept.checked⟩

/-- Native socket-record updates retain the original dump mask while the
focused outer observer keeps all incoming checks and failed prefixes. -/
theorem audit_dump_lift (a : WG.M α) (frame : SameDump a) :
    Audited (liftPrefix (liftWG a)) := by
  apply audit_lift
  apply viewLiftPrefix_preserves (fun w : World => dumpView w.wg) safe
  · exact fun h w v eq hi => dump_store h w v eq hi
  · exact sameView_liftWG (fun w : World => dumpView w.wg) dumpView a frame
      (fun _ _ _ eq => eq)

/-- The same arbitrary appending audit body runs inside both original socket
transactions. Its focused OwnerChecks contract is the only body premise. -/
theorem audit_netlink (body : AuditM Int) (hb : Audited body) :
    OwnerChecks.Preserves (RxHistory.audit (netlinkRequestAudit body)) := by
  rw [netlinkRequestAudit_factor]
  unfold RxHistory.audit
  rw [← netlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) body hb.1]
  exact netlinkRequest _ hb.2

end Leanux.Proofs.WG.OwnerControlCalls
