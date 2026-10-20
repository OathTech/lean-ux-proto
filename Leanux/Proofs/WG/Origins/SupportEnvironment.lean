import Leanux.Proofs.WG.Origins.SupportCallers
import Leanux.Proofs.WG.Queues.RxEnvControlsHistory

/-! Concrete environment composition on the existing persistent journal.
Quiet audit leaves are proved from their actual operations. Scheduler and timer
continuations retain the same stateful support and positional probe contracts. -/
namespace Leanux.Proofs.WG.Origins.HistorySupport
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Retaining Std.Do

theorem focused_forIn (enc : E → Event) (dec : Event → Option E)
    (hd : ∀ e, dec (enc e) = some e) (xs : List γ) (init : β)
    (f : γ → β → PrefixM E (ForInStep β)) (hf : ∀ x z, Focused enc dec (f x z)) :
    Focused enc dec (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact focused_pure _ _ _
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply focused_bind enc dec hd _ _ (hf x init)
    intro step
    cases step with
    | done z => exact focused_pure _ _ _
    | yield z => exact ih z

theorem focused_range (enc : E → Event) (dec : Event → Option E)
    (hd : ∀ e, dec (enc e) = some e) (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → PrefixM E (ForInStep β)) (hf : ∀ x z, Focused enc dec (f x z)) :
    Focused enc dec (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact focused_forIn enc dec hd _ _ _ hf

abbrev Audited (a : AuditM α) := Focused RxHistory.Event.audit RxHistory.auditEvent a

theorem audited_life (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (he : ErasesPrefix g a) (ha : ProductRetainsCall a) :
    Audited (auditFocus g) := ⟨Appends.focus _ _ _, mixed g a he ha⟩

private theorem audited_native (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (ha : RetainsCall a) :
    Audited (auditFocus (liftWGObserver g)) :=
  audited_life _ _ (liftWGObserver_erases he) (RetainsCall.product ha)

private theorem mtu_material (n : Nat) :
    SameView (fun w : World => view w.wg) (Env.setMtu n) := by
  apply (setMtu_sameEnvScalar n).of_factor
    (fun k : ProductStore43 => k.2.2.2.dev.map materialState) (fun w => view w.wg)
  intro w
  simp [view,envScalarView,envScalarStore,productStoreView,wgStoreView,
    envScalarDevice,materialState,Option.map_map,Function.comp_def]

-- The old global getK frame is superseded at the actual getter by the
-- canonical product read rule; the observation remains the original 43 fields.
macro "environment_kernel" : tactic => `(tactic| first
  | exact deliverSent_sameKernel
  | exact requireNoCryptWork_sameKernel
  | exact peekNextSite_sameKernel
  | exact timerWorker_sameKernel _
  | exact advance_sameKernel _
  | exact senderSource_sameKernel _ _ _ _
  | exact xmitPackets_sameKernel _ _ _ _
  | exact routeIntoWg0_sameKernel
  | exact wgDeladdr_sameKernel _
  | exact wgDelroute_sameKernel _
  | exact observeTail_sameKernel
  | (intro initial; exact productGetWG_spec (fun s => s = initial))
  | (intro initial; exact productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl))
  | (intro initial; exact productRouting_spec _ (fun s => s = initial))
  | support_kernel)

macro "environment_material" : tactic => `(tactic| (
  intro initial
  refine hoare_consequence (m := Except Stop)
    (P := fun w : World => RetainsView initial (view w.wg))
    (Q := fun _ (w : World) => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _)
    (fun _ _ h => h)
  try material_lower
  try simp (config := {zeta := false}) only
    [peekHiddenSite,recordBudget,budgetExhausted,peekUnit,resolveUnit,skipCut,
      peekSiteU64,hiddenJiffies,getRouting,modifyRouting]
  repeat' first
    | (index_material_head Env.setMtu; exact (mtu_material _).wp (RetainsView initial))
    | (index_material_head Env.deliverSent; exact (kernel (project := id) (deliverSent_sameKernel)).wp (RetainsView initial))
    | (index_material_head Env.requireNoCryptWork; exact (kernel (project := id) (requireNoCryptWork_sameKernel)).wp (RetainsView initial))
    | (index_material_head Env.peekNextSite; exact (kernel (project := id) (peekNextSite_sameKernel)).wp (RetainsView initial))
    | (index_material_head Env.pendingDevice; exact (kernel (project := id) (pendingDevice_sameKernel _ _)).wp (RetainsView initial))
    | (index_material_head Env.timerWorker; exact (kernel (project := id) (timerWorker_sameKernel _)).wp (RetainsView initial))
    | (index_material_head Env.advance; exact (kernel (project := id) (advance_sameKernel _)).wp (RetainsView initial))
    | (index_material_head Env.senderSource; exact (kernel (project := id) (senderSource_sameKernel _ _ _ _)).wp (RetainsView initial))
    | (index_material_head Env.xmitPackets; exact (kernel (project := id) (xmitPackets_sameKernel _ _ _ _)).wp (RetainsView initial))
    | (index_material_head Env.routeIntoWg0; exact (kernel (project := id) (routeIntoWg0_sameKernel)).wp (RetainsView initial))
    | (index_material_head Env.wgDeladdr; exact (kernel (project := id) (wgDeladdr_sameKernel _)).wp (RetainsView initial))
    | (index_material_head Env.wgDelroute; exact (kernel (project := id) (wgDelroute_sameKernel _)).wp (RetainsView initial))
    | (index_material_head Environment.observeTail; exact (kernel (project := id) (observeTail_sameKernel)).wp (RetainsView initial))
    | (index_material_head Env.sectionAppearsLater; unfold Env.sectionAppearsLater)
    | (index_material_head Env.inetdevDestroy; unfold Env.inetdevDestroy)
    | (index_material_head Env.fixtureSend; unfold Env.fixtureSend)
    | (index_material_head getRouting; unfold getRouting)
    | (index_material_head modifyRouting; unfold modifyRouting)
    | (index_material_head getWG; unfold getWG)
    | (index_material_head getAmbient; unfold getAmbient)
    | (index_material_head modifyWG; unfold modifyWG)
    | (index_material_head modifyAmbient; unfold modifyAmbient)
    | (index_material_head liftM; unfold liftM)
    | (index_material_head skipCut; unfold skipCut)
    | (index_material_head mayHaveSlept; unfold mayHaveSlept)
    | material_basic (RetainsView initial)
    | traffic_product_basic initial))

open Lean Meta Elab Tactic in
elab "environment_at " wanted:str : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Audited || target.isAppOf ``Focused ||
      target.isAppOf ``Preserves || target.isAppOf ``PrefixPreserves do
    throwError "not an environment support contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let mut action := args.back!.consumeMData
  for _ in [:5] do
    if action.isAppOf ``RxHistory.audit || action.isAppOf ``RxHistory.mixed ||
        action.isAppOf ``auditFocus || action.isAppOf ``liftWGObserver then
      unless action.getAppArgs.size > 0 do throwError "missing wrapped observer"
      action := action.getAppArgs.back!.consumeMData
  action := action.headBeta
  let name := action.getAppFn.constName?.map Name.toString |>.getD ""
  unless name.endsWith wanted.getString do throwError "different observer head: {name}"

open Lean Meta Elab Tactic in
elab "environment_match" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Audited || target.isAppOf ``Focused ||
      target.isAppOf ``Preserves || target.isAppOf ``PrefixPreserves do
    throwError "not an environment support contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let action := args.back!.consumeMData
  let some _ ← matchMatcherApp? action | throwError "not an observer matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

open Lean Meta Elab Tactic in
elab "environment_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Audited || target.isAppOf ``Focused ||
      target.isAppOf ``Preserves || target.isAppOf ``PrefixPreserves do
    throwError "not an environment support contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let rec head : Nat → Expr → Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else head n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e
          else head n (mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Expr.equal e next then e else head n next
        | _ => e
  let i := args.size - 1
  let action := args[i]!
  let reduced := head 64 action
  if Expr.equal action reduced then throwError "unchanged observer head"
  replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! i reduced))]

open Lean Meta Elab Tactic in
elab "environment_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Audited || target.isAppOf ``Focused ||
      target.isAppOf ``Preserves || target.isAppOf ``PrefixPreserves do
    throwError "not an environment support contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let i := args.size - 1
  let action := args[i]!.consumeMData
  let .letE name ty value body _ := action | throwError "not a shared continuation"
  unless name.toString.startsWith "__do_jp" do throwError "not a shared continuation"
  let property := fun a => mkAppN target.getAppFn (args.set! i a)
  let contract ← forallTelescope ty fun xs _ => mkForallFVars xs (property (mkAppN value xs))
  let valueProof ← mkFreshExprSyntheticOpaqueMVar contract
  let (proof, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun xs _ => mkForallFVars xs (property (mkAppN f xs))
    withLocalDeclD `environment_continuation contract fun hf => do
      let next ← mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 f))
      pure (← mkLambdaFVars #[f,hf] next, next.mvarId!)
  goal.assign (mkApp2 proof value valueProof)
  replaceMainGoal [valueProof.mvarId!,next]

open Lean Meta Elab Tactic in
elab "environment_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Audited || target.isAppOf ``Focused ||
      target.isAppOf ``Preserves || target.isAppOf ``PrefixPreserves do
    throwError "not an environment support contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let action := args.back!.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `environment_continuation then
      let proof := mkAppN decl.toExpr action.getAppArgs
      if ← withReducible (isDefEq (← inferType proof) target) then
        goal.assign proof
        replaceMainGoal []
        return
  throwError "no continuation contract"

elab "environment_intro" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isForall do Lean.throwError "not a continuation"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro x))

macro "audit_steps" : tactic => `(tactic| first
  | environment_intro
  | environment_reduce
  | environment_join
  | environment_join_use
  | (environment_at "getDevSavedAudit"; exact audited_native _ _ (erasesStatePrefix_lift getDev)
      (of_view (sameView_of_sameWG (project := id) getDev_sameWGStore)))
  | (environment_at "liftWGPrefix"; exact audited_native _ _ (erasesStatePrefix_lift _) (by support_native_material))
  | (environment_at "runFlushedSendWorkPrefix"; exact audited_native _ _ (runFlushedSendWorkPrefix_erases _) (runFlushedSendWork_material _))
  | (environment_at "runFlushedClearWorkPrefix"; exact audited_native _ _ (runFlushedClearWorkPrefix_erases _) (runFlushedClearWork_material _))
  | (environment_at "delTimerPrefix"; exact audited_native _ _ (delTimerPrefix_erases _ _) (of_view (delTimer_material _ _)))
  | (environment_at "timerCallbackPrefix"; exact audited_native _ _ (timerCallbackPrefix_erases _ _) (timerCallback_material _ _))
  | (environment_at "liftPrefix"; apply focused_lift; environment_material)
  | (environment_at "Pure.pure"; exact focused_pure _ _ _)
  | (environment_at "Bind.bind"; apply focused_bind RxHistory.Event.audit RxHistory.auditEvent (fun e => rfl))
  | (environment_at "ForIn.forIn"; first
      | apply focused_range RxHistory.Event.audit RxHistory.auditEvent (fun e => rfl)
      | apply focused_forIn RxHistory.Event.audit RxHistory.auditEvent (fun e => rfl))
  | (environment_at "ite"; apply focused_ite)
  | environment_match)

private theorem audited_worker (worker : Worker) (body : AuditM Unit) (hb : Audited body) :
    Audited (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first | assumption | audit_steps

private theorem sendOne : Audited runOneSendWorkerAudit := by
  unfold runOneSendWorkerAudit
  repeat' audit_steps
private theorem clearOne : Audited runOneClearWorkerAudit := by
  unfold runOneClearWorkerAudit
  repeat' audit_steps

-- The current wheel scans every saved peer occurrence and then selects by
-- bucket order. The removed raw-expiry/fire helpers had no remaining source.
private theorem wheelDue (d : Device) (j : UInt64) : Audited (wheelDueAudit d j) := by
  unfold wheelDueAudit
  exact audited_native _ _ (savedPeerLookupFlatMap_erases _ _ _)
    (of_view (SameView.pure _ _))

private theorem wheelNextDue (d : Device) (j : UInt64) :
    Audited (wheelNextDueAudit d j) := by
  unfold wheelNextDueAudit
  apply focused_bind RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) _ _ (wheelDue d j)
  intro due
  exact focused_pure _ _ _

private theorem stepComplete (b : UInt64) : Audited (requireStepCompleteAudit b) := by
  unfold requireStepCompleteAudit
  repeat' first
    | (environment_at "wheelDueAudit"; exact wheelDue _ _)
    | audit_steps

private theorem nothingDue (j : UInt64) : Audited (requireNothingDueAudit j) := by
  unfold requireNothingDueAudit
  repeat' first
    | (environment_at "wheelNextDueAudit"; exact wheelNextDue _ _)
    | audit_steps

private theorem timerSection (worker : Worker) (body : AuditM Unit) (hb : Audited body) :
    Audited (runTimerSectionAudit worker body) := by
  unfold runTimerSectionAudit
  repeat' first
    | (environment_at "runWorkerPrefix"; exact audited_worker worker body hb)
    | audit_steps

private theorem timerDispatch (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) :
    Audited (timerDispatchAudit worker pid timer we step) := by
  unfold timerDispatchAudit
  repeat' first
    | (environment_at "requireStepCompleteAudit"; exact stepComplete _)
    | (environment_at "runTimerSectionAudit"; apply timerSection)
    | audit_steps

private theorem placeholderPass (j : UInt64) : Audited (RxHistory.placeholderTimerPassAudit j) := by
  unfold RxHistory.placeholderTimerPassAudit
  repeat' first
    | (environment_at "wheelNextDueAudit"; exact wheelNextDue _ _)
    | (environment_at "runTimerSectionAudit"; apply timerSection)
    | audit_steps

private theorem sendOne_support : Preserves (RxHistory.audit runOneSendWorkerAudit) := sendOne.2
private theorem clearOne_support : Preserves (RxHistory.audit runOneClearWorkerAudit) := clearOne.2
private theorem placeholder_support (j : UInt64) :
    Preserves (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) := (placeholderPass j).2

private theorem drained_material (what : String) (qs : List Bool) :
    ProductRetainsCall (Env.requireDrained what qs) := by
  unfold Env.requireDrained
  simp only [pendingDeviceUnits]
  support_material

private theorem idleDevice_material : ProductRetainsCall Env.requireIdleDevice := by
  unfold Env.requireIdleDevice
  environment_material

macro "environment_steps" : tactic => `(tactic| first
  | environment_intro
  | environment_reduce
  | environment_join
  | environment_join_use
  | (environment_at "runOneSendWorkerAudit"; exact sendOne_support)
  | (environment_at "runOneClearWorkerAudit"; exact clearOne_support)
  | (environment_at "placeholderTimerPassAudit"; exact placeholder_support _)
  | (environment_at "wheelNextDueAudit"; exact (wheelNextDue _ _).2)
  | (environment_at "timerDispatchAudit"; exact (timerDispatch _ _ _ _ _).2)
  | (environment_at "requireStepCompleteAudit"; exact (stepComplete _).2)
  | (environment_at "requireNothingDueAudit"; exact (nothingDue _).2)
  | (environment_at "getDevSavedAudit"; exact (audited_native _ _ (erasesStatePrefix_lift getDev)
      (of_view (sameView_of_sameWG (project := id) getDev_sameWGStore))).2)
  | (environment_at "requireDrainedPrefix"; exact mixed _ _ (requireDrainedPrefix_erases _ _) (drained_material _ _))
  | (environment_at "requireIdleDevicePrefix"; exact mixed _ _ requireIdleDevicePrefix_erases idleDevice_material)
  | (environment_at "wgReceivePrefix"; exact mixed _ _ (liftWGObserver_erases (wgReceivePrefix_erases _ _))
      (RetainsCall.product (wgReceive_material _ _)))
  | (environment_at "wgXmitPrefix"; exact mixed _ _ (liftWGObserver_erases (wgXmitPrefix_erases _ _ _ _))
      (RetainsCall.product (wgXmit_material _ _ _ _)))
  | (environment_at "liftPrefix"; apply lift_retains; environment_material)
  | support_steps)

theorem runWorker (worker : Worker) (body : Obs Unit) (hb : Preserves body) :
    Preserves (runWorkerPrefix worker body) :=
  runWorkerPrefix_preserves safe (fun _ _ _ he hi => hi.kernel he) worker hb

theorem runCryptWorkers : Preserves RxHistory.runCryptWorkers :=
  PrefixPreserves.bind (schedule none) (fun _ => lift_kernel _ deliverSent_sameKernel)

theorem runSendWorkers : Preserves RxHistory.runSendWorkers := by
  unfold RxHistory.runSendWorkers
  repeat' first | (environment_at "RxHistory.schedule"; exact schedule _) | environment_steps

theorem afterXmit : Preserves RxHistory.afterXmit := by
  unfold RxHistory.afterXmit
  repeat' first
    | (environment_at "RxHistory.runCryptWorkers"; exact runCryptWorkers)
    | (environment_at "RxHistory.runSendWorkers"; exact runSendWorkers)
    | environment_steps

theorem runTimers (jHi : UInt64) : Preserves (RxHistory.runTimers jHi) := by
  unfold RxHistory.runTimers
  repeat' first | (environment_at "RxHistory.runCryptWorkers"; exact runCryptWorkers) | environment_steps

theorem runTimersPlaceholder (jHi : UInt64) : Preserves (RxHistory.runTimersPlaceholder jHi) := by
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | (environment_at "RxHistory.runCryptWorkers"; exact runCryptWorkers)
    | (environment_at "RxHistory.runSendWorkers"; exact runSendWorkers)
    | environment_steps

theorem idleTimers : Preserves RxHistory.idleTimers := by
  unfold RxHistory.idleTimers
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (environment_at "RxHistory.runTimers"; exact runTimers _)
    | (environment_at "RxHistory.runTimersPlaceholder"; exact runTimersPlaceholder _)
    | environment_steps

theorem afterAdvance : Preserves RxHistory.afterAdvance := by
  unfold RxHistory.afterAdvance
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (environment_at "RxHistory.runTimers"; exact runTimers _)
    | (environment_at "RxHistory.runTimersPlaceholder"; exact runTimersPlaceholder _)
    | environment_steps


theorem audit_of {a : AuditM α} (h : Audited a) : Preserves (RxHistory.audit a) := h.2

private theorem multicast (family addr : Nat) : Audited (xmitMulticastLoopAudit family addr) := by
  unfold xmitMulticastLoopAudit
  repeat' first
    | (environment_at "loopbackSendPrefix"; exact audited_native _ _ (loopbackSendPrefix_erases _ _) (of_view (sameView_of_sameWG (project := id) (loopbackSend_kernel _ _))))
    | audit_steps

macro "control_steps" : tactic => `(tactic| first
  | (environment_at "wgUpPrefix"; exact audited_native _ _ wgUpPrefix_erases wgUp_material)
  | (environment_at "wgDownPrefix"; exact audited_native _ _ wgDownPrefix_erases wgDown_material)
  | (environment_at "wgDeletePrefix"; exact audited_native _ _ wgDeletePrefix_erases wgDelete_material)
  | (environment_at "wgDestructPrefix"; exact audited_native _ _ wgDestructPrefix_erases wgDestruct_material)
  | (environment_at "netnsPreExitPrefix"; exact audited_native _ _ netnsPreExitPrefix_erases (of_view netnsPreExit_material))
  | (environment_at "requireIdleDevicePrefix"; exact audited_life _ _ requireIdleDevicePrefix_erases idleDevice_material)
  | (environment_at "runWorkerPrefix"; apply audited_worker)
  | audit_steps)

private theorem up : Audited envWgUpAudit := by
  unfold envWgUpAudit
  repeat' control_steps
private theorem down : Audited envWgDownAudit := by
  unfold envWgDownAudit
  repeat' control_steps
private theorem delete : Audited envWgDeleteAudit := by
  unfold envWgDeleteAudit
  repeat' control_steps
private theorem cleanup : Audited envNetnsCleanupAudit := by
  unfold envNetnsCleanupAudit
  repeat' control_steps

theorem handshakeReceiveWorker : Preserves RxHistory.handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ safe receiveStep (nestedResched _) _ _

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves (RxHistory.inject family port msg tos ll dest) := by
  unfold RxHistory.inject
  repeat' first
    | (environment_at "RxHistory.runCryptWorkers"; exact runCryptWorkers)
    | (environment_at "runWorkerPrefix"; apply runWorker)
    | environment_steps

theorem afterBatch : Preserves RxHistory.afterBatch := by
  unfold RxHistory.afterBatch
  repeat' first
    | (environment_at "RxHistory.runCryptWorkers"; exact runCryptWorkers)
    | (environment_at "RxHistory.runSendWorkers"; exact runSendWorkers)
    | (environment_at "RxHistory.schedule"; exact schedule _)
    | environment_steps

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    Preserves (RxHistory.flood count port family messages) := by
  unfold RxHistory.flood
  repeat' first
    | (environment_at "RxHistory.afterBatch"; exact afterBatch)
    | (environment_at "RxHistory.pollScheduledInline"; exact pollScheduledInline)
    | (environment_at "runWorkerPrefix"; apply runWorker)
    | environment_steps

theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Preserves (RxHistory.batchItem d cqes item) := by
  unfold RxHistory.batchItem
  repeat' first
    | (environment_at "RxHistory.pollScheduledInline"; exact pollScheduledInline)
    | (environment_at "xmitMulticastLoopAudit"; exact audit_of (multicast _ _))
    | (environment_at "runWorkerPrefix"; apply runWorker)
    | environment_steps

theorem batch (items : List Env.BatchItem) : Preserves (RxHistory.batch items) := by
  unfold RxHistory.batch
  repeat' first
    | (environment_at "RxHistory.afterBatch"; exact afterBatch)
    | (environment_at "RxHistory.batchItem"; exact batchItem _ _ _)
    | environment_steps

theorem observe : Preserves RxHistory.observe :=
  PrefixPreserves.bind idleTimers (fun _ => lift_kernel _ observeTail_sameKernel)

/-- Fourteen concrete deferred calls, including scheduler-bearing timer suffixes.
The incoming support is supplied; this is not an initialization theorem. -/
theorem deferred (call : EnvDeferredCall) : Preserves (RxHistory.deferred call) := by
  cases call with
  | drained what queues => exact mixed _ _ (requireDrainedPrefix_erases _ _) (drained_material _ _)
  | idleDevice => exact mixed _ _ requireIdleDevicePrefix_erases idleDevice_material
  | noCrypt => exact audit_of (focused_lift _ _ _ (of_view (kernel requireNoCryptWork_sameKernel)))
  | crypt => exact runCryptWorkers
  | sendOne => exact sendOne_support
  | clearOne => exact clearOne_support
  | sendAll => exact runSendWorkers
  | afterXmit => exact afterXmit
  | timerWorker timer => exact audit_of (focused_lift _ _ _ (of_view (kernel (timerWorker_sameKernel _))))
  | timers j => exact runTimers j
  | placeholder j => exact runTimersPlaceholder j
  | idle => exact idleTimers
  | advance ticks => exact audit_of (focused_lift _ _ _ (of_view (kernel (advance_sameKernel _))))
  | afterAdvance => exact afterAdvance

/-- Every existing remaining-environment observer is composed at its actual
poll, scheduler and origin-bearing calls; arbitrary audit computations are not
assumed to preserve receiving material. -/
theorem remaining (call : EnvRemainingCall) : Preserves (RxHistory.remaining call) := by
  cases call with
  | up => exact audit_of up
  | mtu n => exact audit_of (focused_lift _ _ _ (of_view (mtu_material n)))
  | route => exact audit_of (focused_lift _ _ _ (of_view (kernel routeIntoWg0_sameKernel)))
  | down => exact audit_of down
  | delete => exact audit_of delete
  | deladdr family => exact audit_of (focused_lift _ _ _ (of_view (kernel (wgDeladdr_sameKernel family))))
  | delroute family => exact audit_of (focused_lift _ _ _ (of_view (kernel (wgDelroute_sameKernel family))))
  | observe => exact observe
  | inject family port msg tos ll dest => exact inject family port msg tos ll dest
  | flood count port family messages => exact flood count port family messages
  | inlinePoll => exact pollScheduledInline
  | afterBatch => exact afterBatch
  | batch items => exact batch items
  | cleanup => exact audit_of cleanup
  | multicast family addr => exact audit_of (multicast family addr)

end Leanux.Proofs.WG.Origins.HistorySupport
