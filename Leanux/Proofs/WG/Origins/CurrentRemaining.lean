import Leanux.Proofs.WG.Origins.CurrentDeferred
import Leanux.Proofs.WG.Queues.RxEnvControlsHistory

/-! Current positional checks through the existing environment traffic and
control observers. Incoming histories and all reached Stops remain in scope. -/
namespace Leanux.Proofs.WG.CurrentRemaining
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues CurrentLifecycle CurrentTraffic ConfiguredHandshake
open Origins hiding Inv

private theorem multicast (family addr : Nat) :
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited) (xmitMulticastLoopAudit family addr) := by
  unfold xmitMulticastLoopAudit
  repeat' first
    | (deferred_audit_at loopbackSendPrefix
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.native_audit) _ _ (loopbackSendPrefix_erases _ _)
         (Retaining.of_view (Origins.sameView_of_sameWG (project := id) (loopbackSend_kernel _ _)))
         (fun history => current_preserves _ (ConfiguredIdentity.sameWG (project := id) (loopbackSend_kernel _ _))
           (Retaining.of_view (Origins.sameView_of_sameWG (project := id) (loopbackSend_kernel _ _))) history))
    | deferred_audit_steps

theorem runWorker (worker : Worker) (body : RxHistory.Obs Unit)
    (hb : CurrentChecks.Preserves body) : CurrentChecks.Preserves (runWorkerPrefix worker body) :=
  runWorkerPrefix_preserves
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.safe)
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.store)
    worker hb

theorem handshakeReceiveWorker : CurrentChecks.Preserves RxHistory.handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.safe)
    CurrentReceiveChecks.receiveStep (CurrentEnvironment.nestedResched _) _ _

private theorem lift_store (a : Leanux.M α) (hf : SameProductStore a) :
    CurrentChecks.Preserves (liftPrefix a) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.lift_store) a hf

private theorem native_mixed (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (hm : Retaining.RetainsCall a)
    (hc : ∀ history, Preserves (Inv history) a) :
    CurrentChecks.Preserves (RxHistory.mixed (liftWGObserver g)) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.native_mixed) g a he hm hc

macro "remaining_steps" : tactic => `(tactic| first
  | (current_env_at wgReceivePrefix
     exact native_mixed _ _ (wgReceivePrefix_erases _ _)
       (Retaining.wgReceive_material _ _) (CurrentRx.wgReceive_preserves _ _))
  | (current_env_at wgXmitPrefix
     exact native_mixed _ _ (wgXmitPrefix_erases _ _ _ _)
       (Retaining.wgXmit_material _ _ _ _) (CurrentStack.wgXmit_preserves _ _ _ _))
  | (environment_at "xmitMulticastLoopAudit"; exact (multicast _ _).2)
  | (current_env_at RxHistory.runCryptWorkers; exact CurrentDeferred.runCryptWorkers)
  | (current_env_at RxHistory.runSendWorkers; exact CurrentDeferred.runSendWorkers)
  | (current_env_at RxHistory.schedule; exact CurrentEnvironment.schedule _)
  | (current_env_at RxHistory.pollScheduledInline; exact CurrentWorkers.pollScheduledInline)
  | (current_env_at runWorkerPrefix; apply runWorker)
  | (current_env_at requireNotPending
     exact lift_store _ (liftWG_sameProductStore _ (SameView.pure _ _)))
  | (current_env_at Env.fixtureSend
     exact lift_store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (current_env_at getRouting
     exact lift_store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (current_env_at Env.senderSource; exact lift_store _ (senderSource_sameKernel _ _ _ _))
  | (current_env_at Env.xmitPackets; exact lift_store _ (xmitPackets_sameKernel _ _ _ _))
  | (current_env_at liftM
     exact lift_store _ (fun initial => productRouting_spec _ (fun s => s = initial)))
  | (current_env_at ite; apply PrefixPreserves.ite)
  | deferred_timer_steps)

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    CurrentChecks.Preserves (RxHistory.inject family port msg tos ll dest) := by
  change PrefixPreserves CurrentChecks.Inv CurrentChecks.Safe _
  unfold RxHistory.inject
  repeat' remaining_steps

theorem afterBatch : CurrentChecks.Preserves RxHistory.afterBatch := by
  change PrefixPreserves CurrentChecks.Inv CurrentChecks.Safe _
  unfold RxHistory.afterBatch
  repeat' remaining_steps

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    CurrentChecks.Preserves (RxHistory.flood count port family messages) := by
  change PrefixPreserves CurrentChecks.Inv CurrentChecks.Safe _
  unfold RxHistory.flood
  repeat' first
    | (current_env_at RxHistory.afterBatch; exact afterBatch)
    | remaining_steps

theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    CurrentChecks.Preserves (RxHistory.batchItem d cqes item) := by
  change PrefixPreserves CurrentChecks.Inv CurrentChecks.Safe _
  unfold RxHistory.batchItem
  repeat' remaining_steps

theorem batch (items : List Env.BatchItem) : CurrentChecks.Preserves (RxHistory.batch items) := by
  change PrefixPreserves CurrentChecks.Inv CurrentChecks.Safe _
  unfold RxHistory.batch
  repeat' first
    | (current_env_at RxHistory.afterBatch; exact afterBatch)
    | (current_env_at RxHistory.batchItem; exact batchItem _ _ _)
    | remaining_steps

theorem observe : CurrentChecks.Preserves RxHistory.observe :=
  PrefixPreserves.bind CurrentDeferred.idleTimers (fun _ => lift_store _ observeTail_sameKernel)

private theorem socketInit_preserves (port : Nat) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (socketInit port) := by
  apply current_preserves
  · apply (socketInit_sameSocket port).of_factor
      (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state) ConfiguredIdentity.view
    intro w
    simp only [socketView,socketDevice,wgOwnedView,wgStoreView,ConfiguredIdentity.view,
      ConfiguredIdentity.state,Option.map_map,Function.comp_def]
    rfl
  · exact Retaining.of_view (Retaining.socketControl_material (project := id) _
      ((socketInit_sameSocket port).factor WGOwnedView.toWGStoreView))

/-- Native opening preserves the supplied current identity even when socket
initialization returns an errno. Only normal endpoints are asserted. -/
theorem wgUp_preserves (history : List SessionOrigin.Receipt) : Preserves (Inv history) wgUp := by
  have openSpec : Preserves (Inv history) wgOpen := by
    unfold wgOpen
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (rx_retention_head socketInit; exact socketInit_preserves _ history)
      | (rx_retention_head sendStagedPackets; exact sendStagedPackets_preserves _ history)
      | (rx_retention_head sendKeepalive; exact sendKeepalive_preserves _ history)
      | current_traffic_step history
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact openSpec)
    | current_lifecycle_step history

/-- The actual pre-exit call retains identity while clearing carrier, sockets
and endpoint sources; it keeps all branch records and native Stops. -/
theorem netnsPreExit_preserves (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketReinit
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDevice.«0».Leanux.Proofs.WG.CurrentLifecycle.socketReinit_preserves) _ _ history)
    | (rx_retention_head get
       exact hoare_get _ (fun w hi => hi))
    | deferred_native_step history

private theorem mtu_view (n : Nat) :
    SameView (fun w : World => ConfiguredIdentity.view w.wg) (Env.setMtu n) := by
  apply (setMtu_sameEnvScalar n).of_factor
    (fun s : ProductStore43 => s.2.2.2.dev.map ConfiguredIdentity.state)
    (fun w => ConfiguredIdentity.view w.wg)
  intro w
  simp only [envScalarView,envScalarStore,productStoreView,wgStoreView,
    envScalarDevice,ConfiguredIdentity.view,ConfiguredIdentity.state,Option.map_map,Function.comp_def]
  rfl

private theorem mtu (n : Nat) :
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited)
      (setMtuAudit n) := by
  have material := (pinned_const _private.Leanux.Proofs.WG.Origins.SupportEnvironment.«0».Leanux.Proofs.WG.Origins.HistorySupport.mtu_material) n
  apply (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.focused_lift)
    RxHistory.Event.audit RxHistory.auditEvent (Env.setMtu n) (Retaining.of_view material)
  intro history
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi hr
  have viewEq := (ProjectedAction.iff_run _ _ _).mp (mtu_view n) w result v hr
  constructor
  · intro cell hc
    exact hi.1 cell (viewEq.symm.trans hc)
  · exact hi.2.retain (CurrentIdentity.retains_of_configured_view
      ((ProjectedAction.iff_run _ _ _).mp (Retaining.of_view material) w result v hr) viewEq)

private theorem audit_native (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (hm : Retaining.RetainsCall a)
    (hc : ∀ history, Preserves (Inv history) a) :
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited) (auditFocus (liftWGObserver g)) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.native_audit) g a he hm hc

private theorem audit_store (a : Leanux.M α) (hf : SameProductStore a) :
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited) (liftPrefix a) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.focused_store) a hf

private theorem audit_idle :
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited) (auditFocus requireIdleDevicePrefix) :=
  ⟨Appends.focus _ _ _,(pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.idleDevice)⟩

private theorem audit_worker (worker : Worker) (body : AuditM Unit) (hb : (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited) body) :
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited) (runWorkerPrefix worker body) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.audited_worker) worker body hb

private theorem inetdevDestroy_store : SameProductStore Env.inetdevDestroy := by
  have routing {α : Type} (a : Net.M α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun initial => productRouting_spec a (fun s => s = initial)
  have get : SameProductStore getRouting :=
    routing ((fun (r : Net.State) => r.toRouting) <$> (get : Net.M Net.State))
  have modify (f : Net.Routing → Net.Routing) : SameProductStore (modifyRouting f) :=
    routing (modify (fun (r : Net.State) => {r with toRouting := f r.toRouting}) : Net.M Unit)
  have list {α β : Type} (xs : List α) (init : β)
      (f : α → β → Leanux.M (ForInStep β)) (hf : ∀ x b, SameProductStore (f x b)) :
      SameProductStore (forIn xs init f) :=
    fun initial => list_view_spec productStoreView (fun s => s = initial) xs init f (fun x b => hf x b initial)
  env_operation_source [Env.inetdevDestroy] using [routing,get,modify,list]

macro "remaining_control_steps" : tactic => `(tactic| first
  | (deferred_audit_at wgUpPrefix
     exact audit_native _ _ wgUpPrefix_erases Retaining.wgUp_material wgUp_preserves)
  | (deferred_audit_at wgDownPrefix
     exact audit_native _ _ wgDownPrefix_erases Retaining.wgDown_material CurrentLifecycle.wgDown_preserves)
  | (deferred_audit_at wgDestructPrefix
     exact audit_native _ _ wgDestructPrefix_erases Retaining.wgDestruct_material CurrentLifecycle.wgDestruct_preserves)
  | (deferred_audit_at netnsPreExitPrefix
     exact audit_native _ _ netnsPreExitPrefix_erases (Retaining.of_view Retaining.netnsPreExit_material) netnsPreExit_preserves)
  | (deferred_audit_at requireIdleDevicePrefix; exact audit_idle)
  | (deferred_audit_at runWorkerPrefix; apply audit_worker)
  | (deferred_audit_at getDev; exact audit_store _ (liftWG_sameProductStore _ getDev_sameWGStore))
  | (deferred_audit_at mayHaveSlept; exact audit_store _ (liftWG_sameProductStore _ mayHaveSlept_sameWGStore))
  | (deferred_audit_at Env.inetdevDestroy; exact audit_store _ inetdevDestroy_store)
  | (deferred_audit_at getRouting
     exact audit_store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (deferred_audit_at modifyEnv
     exact audit_store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (deferred_audit_at modifyRouting
     exact audit_store _ (fun initial => productRouting_spec _ (fun s => s = initial)))
  | (deferred_audit_at liftM
     exact audit_store _ (fun initial => productRouting_spec _ (fun s => s = initial)))
  | (deferred_audit_at skipCut
     exact audit_store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | deferred_audit_steps)

private theorem up :
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited) envWgUpAudit := by
  unfold envWgUpAudit
  repeat' remaining_control_steps

private theorem down :
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited) envWgDownAudit := by
  unfold envWgDownAudit
  repeat' remaining_control_steps

private theorem delete :
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited) envWgDeleteAudit := by
  unfold envWgDeleteAudit
  repeat' remaining_control_steps

private theorem cleanup :
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.Audited) envNetnsCleanupAudit := by
  unfold envNetnsCleanupAudit
  repeat' remaining_control_steps

/-- All fifteen remaining environment cases preserve current checks on their
actual journals. This transports supplied invariants; it does not assert
initialization or arbitrary configuration-call closure. -/
theorem remaining (call : EnvRemainingCall) : CurrentChecks.Preserves (RxHistory.remaining call) := by
  cases call with
  | up => exact up.2
  | mtu value => exact (mtu value).2
  | route => exact (audit_store _ routeIntoWg0_sameKernel).2
  | down => exact down.2
  | delete => exact delete.2
  | deladdr family => exact (audit_store _ (wgDeladdr_sameKernel family)).2
  | delroute family => exact (audit_store _ (wgDelroute_sameKernel family)).2
  | observe => exact observe
  | inject family port msg tos ll dest => exact inject family port msg tos ll dest
  | flood count port family messages => exact flood count port family messages
  | inlinePoll => exact CurrentWorkers.pollScheduledInline
  | afterBatch => exact afterBatch
  | batch items => exact batch items
  | cleanup => exact cleanup.2
  | multicast family addr => exact (multicast family addr).2

end Leanux.Proofs.WG.CurrentRemaining
