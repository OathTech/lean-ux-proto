import Leanux.Proofs.WG.Origins.RetainingDump
import Leanux.Proofs.WG.Origins.SupportEnvironment
import Leanux.Proofs.WG.Queues.RxRunnerHistory

/-! Configuration, dump and descriptor boundaries preserve receiving-material
support on the existing committed journal. The concrete dispatcher uses the
origin-bearing observers for traffic; no whole old audit-dispatch frame is
assumed. Initialization and indexed Stops are handled on the original Runner. -/
namespace Leanux.Proofs.WG.Origins.HistorySupport
open Lean Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Retaining KernelFrames Std.Do

set_option pp.structureInstances false

private theorem wg_material {a : M α} (ha : SameWGKernel a) : RetainsCall a :=
  of_view (sameView_of_sameWG ha)

private theorem nextFile_material (n : Nat) :
    RetainsCall (modifyK fun k => { k with nextFile := n }) := by
  apply of_view
  intro w x v hr
  cases hr
  rfl

macro "runner_wg" : tactic => `(tactic| first
  | with_reducible exact FSFrames.fdget_sameWGKernel _
  | with_reducible exact FSFrames.fdput_sameWGKernel _
  | with_reducible exact getFiles_sameWGKernel
  | with_reducible exact modifyFiles_sameWGKernel _
  | with_reducible exact setFile_sameWGKernel _ _
  | with_reducible exact freeFile_sameWGKernel _
  | with_reducible exact setFdtSlot_sameWGKernel _ _
  | with_reducible exact setFdtOpen_sameWGKernel _ _
  | with_reducible exact setFdtCloexec_sameWGKernel _ _
  | with_reducible exact FSFrames.sysEventfd2_sameWGKernel _ _
  | with_reducible exact FSFrames.sysDup_sameWGKernel _
  | with_reducible exact FSFrames.ksysDup3_sameWGKernel _ _ _
  | with_reducible exact FSFrames.sysClose_sameWGKernel _
  | with_reducible exact FSFrames.ksysRead_sameWGKernel _ _
  | with_reducible exact FSFrames.ksysWrite_sameWGKernel _ _ _
  | with_reducible exact FSFrames.sysPipe2_sameWGKernel _
  | with_reducible exact FSFrames.sysFcntl_sameWGKernel _ _ _
  | with_reducible exact EventpollFrames.sysEpollCreate1_sameWGKernel _
  | with_reducible exact EventpollFrames.sysEpollCtl_sameWGKernel _ _ _ _ _
  | with_reducible exact EventpollFrames.sysEpollWait_sameWGKernel _ _ _
  | with_reducible exact SeccompFrames.sysSeccompInstall_sameWGKernel _ _ _ _ _ _
  | with_reducible exact SeccompFrames.sysSeccompProbeSelf_sameWGKernel _ _
  | with_reducible exact SeccompFrames.sysSeccompProbeChild_sameWGKernel _ _ _
  | with_reducible exact SeccompFrames.sysSeccompPrctl_sameWGKernel _ _
  | with_reducible exact SeccompFrames.sysSeccompCapdrop_sameWGKernel
  | with_reducible exact SeccompFrames.sysSeccompQuery_sameWGKernel _ _ _
  | with_reducible exact SeccompFrames.enterHarnessCall_sameWGKernel _
  | with_reducible exact SignalFrames.getCurrent_sameWGKernel
  | with_reducible exact FSFrames.taskWorkRun_sameWGKernel
  | with_reducible exact SyscallFrames.netnsClose_sameWGKernel
  | with_reducible exact skipCutExactly_sameWGKernel _ _ _)

macro "runner_material" : tactic => `(tactic| first
  | with_reducible exact nextFile_material _
  | (apply wg_material; runner_wg)
  | with_reducible exact of_view (dump_material (setNlSock_sameDumpKernel _ _))
  | with_reducible exact of_view (kernel (getNlSock_sameKernel _))
  | environment_material
  | exact wg_material (by intro w x v hr; cases hr; rfl)
  | exact wg_material (by intro w x v hr; cases hr))

macro "runner_audit_steps" : tactic => `(tactic| first
  | (with_reducible apply focused_lift; runner_material)
  | with_reducible exact focused_pure _ _ _
  | with_reducible apply focused_bind RxHistory.Event.audit RxHistory.auditEvent (fun e => rfl)
  | with_reducible apply focused_ite
  | (with_reducible intro x; try dsimp only)
  | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars))

theorem socketOn_audited (fd : Nat) (body : AuditM Int) (hb : Audited body) :
    Audited (socketCallOnAudit fd body) := by
  unfold socketCallOnAudit
  repeat' first | exact hb | runner_audit_steps

theorem socket_audited (body : AuditM Int) (hb : Audited body) :
    Audited (socketCallAudit body) := socketOn_audited _ _ hb

theorem netlink_audited (body : AuditM Int) (hb : Audited body) :
    Audited (netlinkRequestAudit body) := by
  unfold netlinkRequestAudit
  repeat' first | exact hb | with_reducible apply socket_audited | runner_audit_steps

theorem rtnetlink_audited (body : AuditM Int) (hb : Audited body) :
    Audited (rtnetlinkRequestAudit body) := by
  unfold rtnetlinkRequestAudit
  repeat' first | exact hb | with_reducible apply socketOn_audited | runner_audit_steps

private theorem up_audited : Audited envWgUpAudit := by
  refine ⟨?_, remaining .up⟩
  unfold envWgUpAudit auditFocus
  support_appends
private theorem down_audited : Audited envWgDownAudit := by
  refine ⟨?_, remaining .down⟩
  unfold envWgDownAudit auditFocus
  support_appends
private theorem delete_audited : Audited envWgDeleteAudit := by
  refine ⟨?_, remaining .delete⟩
  unfold envWgDeleteAudit auditFocus
  support_appends
private theorem multicast_audited (family addr : Nat) : Audited (xmitMulticastLoopAudit family addr) := by
  refine ⟨?_, remaining (.multicast family addr)⟩
  unfold xmitMulticastLoopAudit auditFocus
  support_appends

elab "runner_at " wanted:str : tactic => do
  let t ← Lean.Elab.Tactic.getMainTarget
  let some arg := t.getAppArgs.back? | Lean.throwError "expected action argument"
  let a := arg.headBeta
  let name := a.getAppFn.constName?.map Lean.Name.toString |>.getD ""
  unless name.endsWith wanted.getString do
    Lean.throwError "different source head: {name}"

macro "dispatch_audit_steps" : tactic => `(tactic| first
  | with_reducible exact audited_life _ _ (wgSetDevicePrefix_erases _) (wgSetDevice_material _)
  | with_reducible exact audited_life _ _ (wgGetDevicePrefix_erases _) (of_view (wgGetDevice_material _))
  | with_reducible exact audited_life _ _ (netlinkDumpStartPrefix_erases _ _) (of_view (netlinkDumpStart_material _ _))
  | with_reducible exact audited_life _ _ (netlinkRecvmsgPrefix_erases _) (of_view (netlinkRecvmsg_material _))
  | with_reducible exact audited_life _ _ (wgXmitPrefix_erases _ _ _ _) (wgXmit_material _ _ _ _)
  | with_reducible exact audited_life _ _ wgCreatePrefix_erases wgCreate_material
  | with_reducible exact up_audited
  | with_reducible exact down_audited
  | with_reducible exact delete_audited
  | with_reducible exact multicast_audited _ _
  | (runner_at "setMtuAudit"; exact ⟨Appends.lift _, remaining (.mtu _)⟩)
  | (runner_at "wgDeladdrAudit"; exact ⟨Appends.lift _, remaining (.deladdr _)⟩)
  | (runner_at "wgDelrouteAudit"; exact ⟨Appends.lift _, remaining (.delroute _)⟩)
  | (runner_at "advanceAudit"; exact ⟨Appends.lift _, deferred (.advance _)⟩)
  | with_reducible apply netlink_audited
  | with_reducible apply rtnetlink_audited
  | with_reducible apply socketOn_audited
  | runner_audit_steps)

theorem socketOn (fd : Nat) (body : Obs Int) (hb : Preserves body) :
    Preserves (RxHistory.socketCallOn fd body) := by
  unfold RxHistory.socketCallOn
  repeat' first
    | exact hb
    | (with_reducible apply lift_retains; runner_material)
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | with_reducible split


private theorem dispatch_eventfd2 (count flags : UInt32) :
    Audited (dispatchAudit (.eventfd2 count flags)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_dup (fildes : Nat) :
    Audited (dispatchAudit (.dup fildes)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_dup3 (oldfd newfd : Nat) (flags : UInt32) :
    Audited (dispatchAudit (.dup3 oldfd newfd flags)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_close (fd : Nat) :
    Audited (dispatchAudit (.close fd)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_read (fd count : Nat) :
    Audited (dispatchAudit (.read fd count)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_write (fd count : Nat) (buf : ByteArray) :
    Audited (dispatchAudit (.write fd count buf)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_pipe2 (flags : UInt32) :
    Audited (dispatchAudit (.pipe2 flags)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_fcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) :
    Audited (dispatchAudit (.fcntl fd cmd arg)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_epollCreate1 (flags : UInt32) :
    Audited (dispatchAudit (.epollCreate1 flags)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_epollCtl (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    Audited (dispatchAudit (.epollCtl epfd op fd events data)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_epollWait (epfd : Nat) (maxevents timeout : Int) :
    Audited (dispatchAudit (.epollWait epfd maxevents timeout)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgSet (attrs : WG.DeviceAttrs) :
    Audited (dispatchAudit (.wgSet attrs)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgGet (device : WG.DeviceRef) :
    Audited (dispatchAudit (.wgGet device)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgGetStart (device : WG.DeviceRef) :
    Audited (dispatchAudit (.wgGetStart device)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgGetRecv  :
    Audited (dispatchAudit (.wgGetRecv )) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgUp  :
    Audited (dispatchAudit (.wgUp )) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgXmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Audited (dispatchAudit (.wgXmit family addr payload opts)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgSetMtu (mtu : Nat) :
    Audited (dispatchAudit (.wgSetMtu mtu)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgDeladdr (family : Nat) :
    Audited (dispatchAudit (.wgDeladdr family)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgDelroute (family : Nat) :
    Audited (dispatchAudit (.wgDelroute family)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgAdvance (ticks : Nat) :
    Audited (dispatchAudit (.wgAdvance ticks)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_seccompInstall (via : Seccomp.InstallVia) (flags : UInt32) (filter : Option ClassicProg) (len : Option Nat) (bad : Seccomp.BadPtr) (mode : Nat) :
    Audited (dispatchAudit (.seccompInstall via flags filter len bad mode)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_seccompProbe (nr : Int) (args : Array UInt64) (where_ : Seccomp.ProbeWhere) (strict : Option Seccomp.StrictVia) :
    Audited (dispatchAudit (.seccompProbe nr args where_ strict)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_seccompPrctl (cmd : Seccomp.PrctlCmd) (args : Array UInt64) :
    Audited (dispatchAudit (.seccompPrctl cmd args)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_seccompCapdrop  :
    Audited (dispatchAudit (.seccompCapdrop )) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_seccompQuery (cmd : Seccomp.QueryCmd) (action flags : UInt32) :
    Audited (dispatchAudit (.seccompQuery cmd action flags)) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgCreate  :
    Audited (dispatchAudit (.wgCreate )) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgDown  :
    Audited (dispatchAudit (.wgDown )) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgDelete  :
    Audited (dispatchAudit (.wgDelete )) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

private theorem dispatch_wgNetnsClose  :
    Audited (dispatchAudit (.wgNetnsClose )) := by
  unfold dispatchAudit
  repeat' dispatch_audit_steps

/-- Each origin-bearing dispatch arm uses its existing eventful observer.
The remaining arms retain full receiving material through the actual source. -/
theorem syscallDispatch (call : Syscall) : Preserves (RxHistory.syscallDispatch call) := by
  cases call with
  | eventfd2 count flags => exact audit_of (dispatch_eventfd2 count flags)
  | dup fildes => exact audit_of (dispatch_dup fildes)
  | dup3 oldfd newfd flags => exact audit_of (dispatch_dup3 oldfd newfd flags)
  | close fd => exact audit_of (dispatch_close fd)
  | read fd count => exact audit_of (dispatch_read fd count)
  | write fd count buf => exact audit_of (dispatch_write fd count buf)
  | pipe2 flags => exact audit_of (dispatch_pipe2 flags)
  | fcntl fd cmd arg => exact audit_of (dispatch_fcntl fd cmd arg)
  | epollCreate1 flags => exact audit_of (dispatch_epollCreate1 flags)
  | epollCtl epfd op fd events data => exact audit_of (dispatch_epollCtl epfd op fd events data)
  | epollWait epfd maxevents timeout => exact audit_of (dispatch_epollWait epfd maxevents timeout)
  | wgSet attrs => exact audit_of (dispatch_wgSet attrs)
  | wgGet device => exact audit_of (dispatch_wgGet device)
  | wgGetStart device => exact audit_of (dispatch_wgGetStart device)
  | wgGetRecv  => exact audit_of (dispatch_wgGetRecv )
  | wgUp  => exact audit_of (dispatch_wgUp )
  | wgXmit family addr payload opts => exact audit_of (dispatch_wgXmit family addr payload opts)
  | wgSetMtu mtu => exact audit_of (dispatch_wgSetMtu mtu)
  | wgObserve =>
    unfold RxHistory.syscallDispatch
    repeat' first
      | with_reducible exact observe
      | with_reducible apply socketOn
      | (with_reducible apply lift_retains; runner_material)
      | with_reducible exact PrefixPreserves.pure safe _
      | with_reducible apply PrefixPreserves.bind
      | (with_reducible intro x; try dsimp only)
  | wgInject family port message tos ll dest => exact socketOn _ _ (inject family port message tos ll dest)
  | wgDeladdr family => exact audit_of (dispatch_wgDeladdr family)
  | wgDelroute family => exact audit_of (dispatch_wgDelroute family)
  | wgFlood count port family messages => exact flood count port family messages
  | wgBatch items waitMs => exact batch items
  | wgAdvance ticks => exact audit_of (dispatch_wgAdvance ticks)
  | seccompInstall via flags filter len bad mode => exact audit_of (dispatch_seccompInstall via flags filter len bad mode)
  | seccompProbe nr args where_ strict => exact audit_of (dispatch_seccompProbe nr args where_ strict)
  | seccompPrctl cmd args => exact audit_of (dispatch_seccompPrctl cmd args)
  | seccompCapdrop  => exact audit_of (dispatch_seccompCapdrop )
  | seccompQuery cmd action flags => exact audit_of (dispatch_seccompQuery cmd action flags)
  | wgCreate  => exact audit_of (dispatch_wgCreate )
  | wgDown  => exact audit_of (dispatch_wgDown )
  | wgDelete  => exact audit_of (dispatch_wgDelete )
  | wgNetnsClose  => exact audit_of (dispatch_wgNetnsClose )

private theorem route_support : Preserves (RxHistory.audit routeIntoWg0Audit) := remaining .route
private theorem cleanup_support : Preserves (RxHistory.audit envNetnsCleanupAudit) := remaining .cleanup

/-- Every original syscall continuation retains the same support: ordinary
negative errno returns still execute their source-designated worker suffix. -/
theorem syscall (call : Syscall) : Preserves (RxHistory.syscall call) := by
  unfold RxHistory.syscall
  try simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | contradiction
    | with_reducible exact syscallDispatch _
    | with_reducible exact runSendWorkers
    | with_reducible exact idleTimers
    | with_reducible exact route_support
    | with_reducible exact afterXmit
    | with_reducible exact afterAdvance
    | with_reducible exact cleanup_support
    | (with_reducible apply lift_retains; runner_material)
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq,reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem history_empty : HistorySafe [] := by
  constructor
  · simp [HistoryAdapters.Valid,Origins.Valid]
  · intro pre e post he
    have hm : e ∈ ([] : List Event) := by rw [he]; simp
    cases hm

/-- The source fixture starts absent or with an empty key store, for every
combination of fixture flags; no trace/parser premise is required. -/
theorem support_initial (rlimit : Nat) (net bare foreign stepped child : Bool) (w : World)
    (hw : w.k = Runner.initialKernel rlimit net bare foreign stepped child) : SupportInv [] w := by
  refine ⟨history_empty,?_⟩
  change Origins.Inv [] w
  have hd : w.k.wg = (if net && !bare then some {ifindex := 3,ifname := "wg0"} else none) := by
    simp [hw,Runner.initialKernel]
  intro epoch keys hv id key hk valid
  by_cases active : (net && !bare) = true
  · simp only [view,hd,active,↓reduceIte,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hv
    obtain ⟨rfl,rfl⟩ := hv
    simp at hk
  · simp [view,hd,active] at hv

/-- Seccomp prefill changes no complete WG field. Failed prefill emits no
journal event and is handled by the outer Runner failure postcondition. -/
theorem support_prefill (trace : Runner.Trace) (w : World)
    (hr : Env.seccompPrefill trace.seccompPrefill
      (Runner.initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild)
        = .ok w.k) : SupportInv [] w := by
  let before := {w with k := Runner.initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild}
  have hi : SupportInv [] before := support_initial _ _ _ _ _ _ before rfl
  have hd := congrArg WGKernelView.wg (prefill_wgKernel trace.seccompPrefill before.k w.k hr)
  have hv : view w = view before := congrArg (fun d => d.map materialState) hd
  refine ⟨hi.1,hi.2.retain ?_⟩
  unfold Retains
  rw [hv]
  exact RetainsView.refl _

theorem runAtSupport_wp {g : Obs α} (hg : Preserves g) (index : Nat) (w : World) :
    ⦃fun h => ⌜SupportInv h w⌝⦄ runAtPrefix index w g
    ⦃post⟨fun out h => ⌜SupportInv h out.2⌝,fun _ h => ⌜HistorySafe h⌝⟩⦄ :=
  runAtPrefix_wp (show PrefixEnsures SupportInv HistorySafe g (fun _ => SupportInv) from hg) index w

/-- Successful calls carry their actual returned accumulator World. An indexed
Stop or end guard retains the checked committed history, without a failed World. -/
theorem runnerTail_support_wp (trace : Runner.Trace) (w : World) :
    ⦃fun h => ⌜SupportInv h w⌝⦄ RxHistory.runnerTail RxHistory.syscall trace w
    ⦃post⟨fun _ h => ⌜HistorySafe h⌝,fun _ h => ⌜HistorySafe h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtSupport_wp (syscall call) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtSupport_wp (lift_kernel skipAmbient skipAmbient_sameKernel) index w
  unfold RxHistory.runnerTail
  mvcgen [syscall_spec,ambient_spec]
  all_goals try exact
    ((post⟨fun out h => ⌜SupportInv h out.2.1⌝,fun _ h => ⌜HistorySafe h⌝⟩) :
      Invariant trace.ops.toList
        (World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json)
        (.except (Nat × Stop) (.arg (List Event) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜SupportInv h r.2⌝,fun _ h => ⌜HistorySafe h⌝⟩) :
      Invariant r.2.steps.toList (Array Json)
        (.except (Nat × Stop) (.arg (List Event) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜SupportInv h r.2⌝,fun _ h => ⌜HistorySafe h⌝⟩) :
      Invariant r.2.fired.toList (Array Json)
        (.except (Nat × Stop) (.arg (List Event) .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try trivial
  all_goals try (solve | rename_i history hi; exact SupportInv.kernel hi rfl)
  all_goals try exact safe _ _ (by assumption)
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intros; exact safe _ _ (by assumption))

/-- Initialized committed origin support for every typed trace and both
placeholder settings. This does not add origin receipts from copied trials. -/
theorem executeTraceHistory_support_wp (trace : Runner.Trace) (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ RxHistory.executeTraceHistory trace placeholders
    ⦃post⟨fun _ h => ⌜HistorySafe h⌝,fun _ h => ⌜HistorySafe h⌝⟩⦄ := by
  have tail_spec (w : World) := runnerTail_support_wp trace w
  unfold RxHistory.executeTraceHistory RxHistory.executeTraceWith
  mvcgen [tail_spec]
  all_goals try dsimp +zetaDelta only at *
  all_goals try trivial
  all_goals
    rename_i history hh
    subst history
    first
    | exact support_initial trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild _ rfl
    | exact support_prefill trace _ (by assumption)
    | exact history_empty

/-- Every outcome retains actual receipt validity and strict-prefix material
support at successful decrypt and saved probe entries. Original JSON/indexed
Stop erasure is inherited from the unchanged observer. -/
theorem executeTraceHistory_support (trace : Runner.Trace) (placeholders : Bool) :
    HistorySafe (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 := by
  have hs := (prefixOuter_wp_iff _ _ _ _).mp (executeTraceHistory_support_wp trace placeholders) [] rfl
  cases hr : runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) [] with
  | mk result hist => cases result <;> simpa only [hr] using hs

end Leanux.Proofs.WG.Origins.HistorySupport
