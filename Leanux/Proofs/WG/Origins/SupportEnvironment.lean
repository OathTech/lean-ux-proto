import Leanux.Proofs.WG.Origins.SupportCallers
import Leanux.Proofs.WG.Queues.RxEnvControlsHistory

/-! Concrete environment composition on the existing persistent journal.
Quiet audit leaves are proved from their actual operations. Scheduler and timer
continuations retain the same stateful support and positional probe contracts. -/
namespace Leanux.Proofs.WG.Origins.HistorySupport
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Retaining

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

theorem audited_life (g : MixedM α) (a : M α) (he : ErasesPrefix g a) (ha : RetainsCall a) :
    Audited (auditFocus g) := ⟨Appends.focus _ _ _, mixed g a he ha⟩

private theorem mtu_material (n : Nat) : SameView view (Env.setMtu n) := by
  apply (setMtu_sameEnvScalar n).of_factor (fun k : Kernel => k.wg.map materialState) view
  intro w
  simp [view,envScalarView,envScalarKernel,envScalarDevice,materialState,Option.map_map,Function.comp_def]

private theorem source_getK : SameKernel getK := by
  intro w x v hr
  cases hr
  rfl

macro "environment_kernel" : tactic => `(tactic| first
  | with_reducible exact source_getK
  | with_reducible exact deliverSent_sameKernel
  | with_reducible exact requireNoCryptWork_sameKernel
  | with_reducible exact peekNextSite_sameKernel
  | with_reducible exact timerWorker_sameKernel _
  | with_reducible exact advance_sameKernel _
  | with_reducible exact senderSource_sameKernel _ _ _ _
  | with_reducible exact fixtureSend_sameKernel
  | with_reducible exact routeLookup_sameKernel _ _ _
  | with_reducible exact xmitPackets_sameKernel _ _ _ _
  | with_reducible exact skipCut_sameKernel _
  | with_reducible exact hiddenJiffies_sameKernel _
  | with_reducible exact peekSiteU64_sameKernel _
  | with_reducible exact routeIntoWg0_sameKernel
  | with_reducible exact wgDeladdr_sameKernel _
  | with_reducible exact wgDelroute_sameKernel _
  | with_reducible exact observeTail_sameKernel
  | support_kernel)

macro "environment_material" : tactic => `(tactic| first
  | with_reducible exact invariant_material _ _
  | with_reducible exact unsupported_material _ _
  | with_reducible exact of_view (mtu_material _)
  | with_reducible exact of_view (requireNotPending_material _ _)
  | (apply of_view; apply kernel; environment_kernel))

macro "audit_steps" : tactic => `(tactic| first
  | with_reducible exact audited_life _ _ (erasesPrefix_lift _) (of_view (kernel getDev_sameKernel))
  | with_reducible exact audited_life _ _ (runFlushedSendWorkPrefix_erases _) (runFlushedSendWork_material _)
  | with_reducible exact audited_life _ _ (runFlushedClearWorkPrefix_erases _) (runFlushedClearWork_material _)
  | with_reducible exact audited_life _ _ (delTimerPrefix_erases _ _) (of_view (delTimer_material _ _))
  | with_reducible exact audited_life _ _ (timerCallbackPrefix_erases _ _) (timerCallback_material _ _)
  | (with_reducible apply focused_lift; environment_material)
  | with_reducible exact focused_pure _ _ _
  | with_reducible apply focused_bind RxHistory.Event.audit RxHistory.auditEvent (fun e => rfl)
  | with_reducible apply focused_range RxHistory.Event.audit RxHistory.auditEvent (fun e => rfl)
  | with_reducible apply focused_forIn RxHistory.Event.audit RxHistory.auditEvent (fun e => rfl)
  | with_reducible apply focused_ite
  | (with_reducible intro x; try dsimp only)
  | with_reducible split)

private theorem audited_worker (worker : Worker) (body : AuditM Unit) (hb : Audited body) :
    Audited (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first | exact hb | audit_steps

private theorem sendOne : Audited runOneSendWorkerAudit := by
  unfold runOneSendWorkerAudit
  repeat' audit_steps
private theorem clearOne : Audited runOneClearWorkerAudit := by
  unfold runOneClearWorkerAudit
  repeat' audit_steps

private theorem duePeers (d : Device) (t : PeerTimer) (j : UInt64) : Audited (duePeersAudit d t j) :=
  audited_life _ _ (savedPeerLookupFlatMap_erases _ _ _) (of_view (kernel (sameKernel_pure _)))
private theorem dueEntries (d : Device) (j : UInt64) : Audited (dueEntriesAudit d j) :=
  audited_life _ _ (savedPeerLookupFlatMap_erases _ _ _) (of_view (kernel (sameKernel_pure _)))

private theorem timerSection (worker : Worker) (body : AuditM Unit) (hb : Audited body) :
    Audited (runTimerSectionAudit worker body) := by
  unfold runTimerSectionAudit
  repeat' first | with_reducible exact audited_worker worker body hb | audit_steps

private theorem fireAfterScan (worker : Worker) (timer : PeerTimer) (j : UInt64) (due : List PeerId) :
    Audited (fireTimerAfterScanAudit worker timer j due) := by
  unfold fireTimerAfterScanAudit
  repeat' first | with_reducible apply timerSection | audit_steps

private theorem fire (worker : Worker) (j : UInt64) : Audited (fireTimerAudit worker j) := by
  unfold fireTimerAudit
  repeat' first
    | with_reducible exact duePeers _ _ _
    | with_reducible exact fireAfterScan _ _ _ _
    | audit_steps

private theorem placeholderPass (j : UInt64) : Audited (RxHistory.placeholderTimerPassAudit j) := by
  unfold RxHistory.placeholderTimerPassAudit
  repeat' first
    | with_reducible exact dueEntries _ _
    | with_reducible apply timerSection
    | audit_steps

private theorem sendOne_support : Preserves (RxHistory.audit runOneSendWorkerAudit) := sendOne.2
private theorem clearOne_support : Preserves (RxHistory.audit runOneClearWorkerAudit) := clearOne.2
private theorem fire_support (w : Worker) (j : UInt64) : Preserves (RxHistory.audit (fireTimerAudit w j)) := (fire w j).2
private theorem placeholder_support (j : UInt64) : Preserves (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) := (placeholderPass j).2

private theorem drained_material (what : String) (qs : List Bool) : RetainsCall (Env.requireDrained what qs) := by
  apply of_view
  apply kernel
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.requireDrained,getDev,getK,invariant,unsupported]

private theorem idleDevice_material : RetainsCall Env.requireIdleDevice := by
  apply of_view
  apply kernel
  apply sameKernel_of_wp
  intro k
  have hn := sameKernel_wp _ requireNoCryptWork_sameKernel (fun s => s = k)
  mvcgen [Env.requireIdleDevice,hn,getDev,getK,invariant,unsupported]

macro "environment_steps" : tactic => `(tactic| first
  | with_reducible exact lift_kernel _ source_getK
  | with_reducible exact sendOne_support
  | with_reducible exact clearOne_support
  | with_reducible exact fire_support _ _
  | with_reducible exact placeholder_support _
  | with_reducible exact mixed _ _ (requireDrainedPrefix_erases _ _) (drained_material _ _)
  | with_reducible exact mixed _ _ requireIdleDevicePrefix_erases idleDevice_material
  | with_reducible exact mixed _ _ (wgReceivePrefix_erases _ _) (wgReceive_material _ _)
  | with_reducible exact mixed _ _ (wgXmitPrefix_erases _ _ _ _) (wgXmit_material _ _ _ _)
  | (with_reducible apply lift_retains; environment_material)
  | support_steps)

theorem runWorker (worker : Worker) (body : Obs Unit) (hb : Preserves body) :
    Preserves (runWorkerPrefix worker body) :=
  runWorkerPrefix_preserves safe (fun _ _ _ he hi => hi.kernel he) worker hb

theorem runCryptWorkers : Preserves RxHistory.runCryptWorkers :=
  PrefixPreserves.bind (schedule none) (fun _ => lift_kernel _ deliverSent_sameKernel)

theorem runSendWorkers : Preserves RxHistory.runSendWorkers := by
  unfold RxHistory.runSendWorkers
  repeat' first | with_reducible exact schedule _ | environment_steps

theorem afterXmit : Preserves RxHistory.afterXmit := by
  unfold RxHistory.afterXmit
  repeat' first
    | with_reducible exact runCryptWorkers
    | with_reducible exact runSendWorkers
    | environment_steps

theorem runTimers (jHi : UInt64) : Preserves (RxHistory.runTimers jHi) := by
  unfold RxHistory.runTimers
  repeat' first | with_reducible exact runCryptWorkers | environment_steps

theorem runTimersPlaceholder (jHi : UInt64) : Preserves (RxHistory.runTimersPlaceholder jHi) := by
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | with_reducible exact runCryptWorkers
    | with_reducible exact runSendWorkers
    | environment_steps

theorem idleTimers : Preserves RxHistory.idleTimers := by
  unfold RxHistory.idleTimers
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first | with_reducible exact runTimers _ | environment_steps

theorem afterAdvance : Preserves RxHistory.afterAdvance := by
  unfold RxHistory.afterAdvance
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | with_reducible exact runTimers _
    | with_reducible exact runTimersPlaceholder _
    | environment_steps


theorem audit_of {a : AuditM α} (h : Audited a) : Preserves (RxHistory.audit a) := h.2

private theorem multicast (family addr : Nat) : Audited (xmitMulticastLoopAudit family addr) := by
  unfold xmitMulticastLoopAudit
  repeat' first
    | with_reducible exact audited_life _ _ (loopbackSendPrefix_erases _ _) (of_view (kernel (loopbackSend_kernel _ _)))
    | audit_steps

macro "control_steps" : tactic => `(tactic| first
  | with_reducible exact audited_life _ _ wgUpPrefix_erases wgUp_material
  | with_reducible exact audited_life _ _ wgDownPrefix_erases wgDown_material
  | with_reducible exact audited_life _ _ wgDeletePrefix_erases wgDelete_material
  | with_reducible exact audited_life _ _ netnsPreExitPrefix_erases (of_view netnsPreExit_material)
  | with_reducible exact audited_life _ _ requireIdleDevicePrefix_erases idleDevice_material
  | with_reducible apply audited_worker
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
    | with_reducible exact runCryptWorkers
    | with_reducible apply runWorker
    | environment_steps

theorem afterBatch : Preserves RxHistory.afterBatch := by
  unfold RxHistory.afterBatch
  repeat' first
    | with_reducible exact runCryptWorkers
    | with_reducible exact runSendWorkers
    | with_reducible exact schedule _
    | environment_steps

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    Preserves (RxHistory.flood count port family messages) := by
  unfold RxHistory.flood
  repeat' first
    | with_reducible exact afterBatch
    | with_reducible exact pollScheduledInline
    | with_reducible apply runWorker
    | environment_steps

theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Preserves (RxHistory.batchItem d cqes item) := by
  unfold RxHistory.batchItem
  repeat' first
    | with_reducible exact pollScheduledInline
    | with_reducible exact audit_of (multicast _ _)
    | with_reducible apply runWorker
    | environment_steps

theorem batch (items : List Env.BatchItem) : Preserves (RxHistory.batch items) := by
  unfold RxHistory.batch
  repeat' first
    | with_reducible exact afterBatch
    | with_reducible exact batchItem _ _ _
    | environment_steps

theorem observe : Preserves RxHistory.observe :=
  PrefixPreserves.bind idleTimers (fun _ => lift_kernel _ observeTail_sameKernel)

/-- Fifteen concrete deferred calls, including scheduler-bearing timer suffixes.
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
  | fire worker j => exact fire_support _ _
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
