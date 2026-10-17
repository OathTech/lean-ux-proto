import Leanux.Proofs.WG.Origins.RetainingDump
import Leanux.Proofs.WG.Origins.SupportEnvironment
import Leanux.Proofs.WG.Queues.RxRunnerHistory

/-! Configuration, dump and descriptor boundaries preserve receiving-material
support on the existing committed journal. The concrete dispatcher uses the
origin-bearing observers for traffic; no whole old audit-dispatch frame is
assumed. Initialization and indexed Stops are handled on the original Runner. -/
namespace Leanux.Proofs.WG.Origins.HistorySupport
open Lean Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Retaining Leanux.Runner Std.Do

set_option pp.structureInstances false

/-- The conditional observation transport keeps arbitrary actual state stacks. -/
private theorem wg_material {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => wgStoreView (project s)) a) :
    ProjectedRetainsCall project a := of_view (sameView_of_sameWG ha)

/- Inspect the actual source carrier before applying the Task adapter;
other native lifts are left for their own canonical rules. -/
open Lean Meta Elab Tactic in
elab "support_runner_task_lift" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let action := args[args.size-3]!.consumeMData
  let some name := action.getAppFn.constName? | throwError "not a lift"
  unless [``monadLift, ``MonadLift.monadLift, ``MonadLiftT.monadLift, ``liftTask].contains name
      && !action.getAppArgs.isEmpty do throwError "not a Task lift"
  let source := action.getAppArgs.back!
  let type ← whnf (← inferType source)
  let .forallE _ state _ _ := type | throwError "not a native state action"
  unless state.isConstOf ``TaskWorld do throwError "not the Task carrier"
  let proof ← mkAppM ``productTask_spec #[source,args[args.size-2]!]
  replaceMainGoal (← goal.apply proof)
  evalTactic (← `(tactic| exact fun _ _ _ hi => hi))

open Lean Meta Elab Tactic in
elab "support_runner_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let action := args[args.size-3]!.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `material_continuation then
      let proof := mkAppN decl.toExpr action.getAppArgs
      if ← isDefEq (← inferType proof) target then
        goal.assign proof
        replaceMainGoal []
        return
  throwError "no applicable local continuation"

/-- Actual component adapters replace the old per-filesystem and per-seccomp
frame family. This rule observes only the unchanged receiving-material store. -/
macro "runner_material" : tactic => `(tactic| (
  intro initial
  refine hoare_consequence (m := Except Stop)
    (P := fun w : World => RetainsView initial (view w.wg))
    (Q := fun _ (w : World) => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _)
    (fun _ _ h => h)
  try material_lower
  repeat' first
    | support_runner_join_use
    | (index_material_head liftFS; exact productFS_spec _ _ (fun _ _ _ _ hi => hi))
    | (index_material_head liftTask; exact productTask_spec _ _ (fun _ _ _ hi => hi))
    | (index_material_head liftSeccomp; exact productSeccomp_spec _ _ (fun _ _ _ _ hi => hi))
    | (index_material_head getFiles; unfold getFiles)
    | (index_material_head modifyFiles; unfold modifyFiles)
    | (index_material_head modifyTask; unfold modifyTask)
    | (index_material_head getTask; unfold getTask)
    | (index_material_head getCurrent
       unfold Leanux.getCurrent
       change Hoare (liftFS (StateT.lift TaskM.getCurrent)) _ _
       exact productFS_spec (StateT.lift TaskM.getCurrent) _ (fun _ _ _ _ hi => hi))
    | support_runner_task_lift
    | (index_material_head netnsClose
       exact ProjectedRetainsCall.wp (wg_material (project := World.wg) SyscallFrames.netnsClose_sameWGStore) initial)
    | (index_material_head liftWG; first
        | exact ProjectedRetainsCall.wp
            (RetainsCall.product (of_view (dump_material (project := id) (setNlSock_sameDump _ _)))) initial
        | exact ProjectedRetainsCall.wp
            (RetainsCall.product (of_view ((getNlSock_sameWGWorld _).factor view))) initial)
    | (index_material_head Env.wgDelroute; unfold Env.wgDelroute)
    | (index_material_head Env.wgAddroute; unfold Env.wgAddroute)
    | (index_material_head Env.wgAddaddr; unfold Env.wgAddaddr)
    | (index_material_head Env.fixtureSend; unfold Env.fixtureSend)
    | (index_material_head skipCut; unfold skipCut)
    | (index_material_head skipCutExactly; unfold skipCutExactly)
    | (index_material_head Env.xmitPackets
       exact (kernel (project := id) (xmitPackets_sameKernel _ _ _ _)).wp (RetainsView initial))
    | (index_material_head modifyWG; unfold modifyWG)
    | (index_material_head modifyAmbient; unfold modifyAmbient)
    | (index_material_head getRouting; unfold getRouting)
    | (index_material_head modifyRouting; unfold modifyRouting)
    | (index_material_head liftM; unfold liftM)
    | (index_material_head invariant; unfold invariant)
    | (index_material_head unsupported; unfold unsupported)
    | (index_material_head branch; unfold branch)
    | traffic_product_basic initial))

macro "runner_audit_steps" : tactic => `(tactic| first
  | contradiction
  | (environment_at "liftPrefix"; apply focused_lift; runner_material)
  | (environment_at "Pure.pure"; exact focused_pure _ _ _)
  | (environment_at "Bind.bind"; apply focused_bind RxHistory.Event.audit RxHistory.auditEvent (fun e => rfl))
  | (environment_at "ite"; apply focused_ite)
  | environment_intro
  | environment_join
  | environment_join_use
  | environment_reduce
  | environment_match)

theorem socketOn_audited (fd : Nat) (body : AuditM Int) (hb : Audited body) :
    Audited (socketCallOnAudit fd body) := by
  unfold socketCallOnAudit
  repeat' first | exact hb | runner_audit_steps

theorem socket_audited (body : AuditM Int) (hb : Audited body) :
    Audited (socketCallAudit body) := socketOn_audited _ _ hb

theorem netlink_audited (body : AuditM Int) (hb : Audited body) :
    Audited (netlinkRequestAudit body) := by
  unfold netlinkRequestAudit
  repeat' first | exact hb | (environment_at "socketCallAudit"; apply socket_audited) | runner_audit_steps

theorem rtnetlink_audited (body : AuditM Int) (hb : Audited body) :
    Audited (rtnetlinkRequestAudit body) := by
  unfold rtnetlinkRequestAudit
  repeat' first | exact hb | (environment_at "socketCallOnAudit"; apply socketOn_audited) | runner_audit_steps

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

private theorem runner_audited_native (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (ha : RetainsCall a) :
    Audited (auditFocus (liftWGObserver g)) :=
  audited_life _ _ (liftWGObserver_erases he) (RetainsCall.product ha)

macro "dispatch_audit_steps" : tactic => `(tactic| first
  | contradiction
  | (environment_at "netnsCloseAudit"; unfold netnsCloseAudit)
  | (environment_at "wgSetDevicePrefix"; exact runner_audited_native _ _ (wgSetDevicePrefix_erases _) (wgSetDevice_material _))
  | (environment_at "wgGetDevicePrefix"; exact runner_audited_native _ _ (wgGetDevicePrefix_erases _) (of_view (wgGetDevice_material _)))
  | (environment_at "netlinkDumpStartPrefix"; exact runner_audited_native _ _ (netlinkDumpStartPrefix_erases _ _) (of_view (netlinkDumpStart_material _ _)))
  | (environment_at "netlinkRecvmsgPrefix"; exact runner_audited_native _ _ (netlinkRecvmsgPrefix_erases _) (of_view (netlinkRecvmsg_material _)))
  | (environment_at "wgXmitPrefix"; exact runner_audited_native _ _ (wgXmitPrefix_erases _ _ _ _) (wgXmit_material _ _ _ _))
  | (environment_at "wgCreatePrefix"; exact runner_audited_native _ _ wgCreatePrefix_erases wgCreate_material)
  | (environment_at "envWgUpAudit"; exact up_audited)
  | (environment_at "envWgDownAudit"; exact down_audited)
  | (environment_at "envWgDeleteAudit"; exact delete_audited)
  | (environment_at "xmitMulticastLoopAudit"; exact multicast_audited _ _)
  | (environment_at "setMtuAudit"; exact ⟨Appends.lift _, remaining (.mtu _)⟩)
  | (environment_at "wgDeladdrAudit"; exact ⟨Appends.lift _, remaining (.deladdr _)⟩)
  | (environment_at "advanceAudit"; exact ⟨Appends.lift _, deferred (.advance _)⟩)
  | (environment_at "netlinkRequestAudit"; apply netlink_audited)
  | (environment_at "rtnetlinkRequestAudit"; apply rtnetlink_audited)
  | (environment_at "socketCallOnAudit"; apply socketOn_audited)
  | runner_audit_steps)

macro "runner_support_steps" : tactic => `(tactic| first
  | contradiction
  | environment_reduce
  | environment_join
  | environment_join_use
  | (environment_at "liftPrefix"; apply lift_retains; runner_material)
  | support_steps)

theorem socketOn (fd : Nat) (body : Obs Int) (hb : Preserves body) :
    Preserves (RxHistory.socketCallOn fd body) := by
  unfold RxHistory.socketCallOn
  repeat' first
    | exact hb
    | runner_support_steps

private theorem dispatch_eventfd2 (count flags : UInt32) :
    Audited (dispatchAudit (.eventfd2 count flags)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_dup (fildes : Nat) :
    Audited (dispatchAudit (.dup fildes)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_dup3 (oldfd newfd : Nat) (flags : UInt32) :
    Audited (dispatchAudit (.dup3 oldfd newfd flags)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_close (fd : Nat) :
    Audited (dispatchAudit (.close fd)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_read (fd count : Nat) :
    Audited (dispatchAudit (.read fd count)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_write (fd count : Nat) (buf : ByteArray) :
    Audited (dispatchAudit (.write fd count buf)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_pipe2 (flags : UInt32) :
    Audited (dispatchAudit (.pipe2 flags)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_fcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) :
    Audited (dispatchAudit (.fcntl fd cmd arg)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_epollCreate1 (flags : UInt32) :
    Audited (dispatchAudit (.epollCreate1 flags)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_epollCtl (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    Audited (dispatchAudit (.epollCtl epfd op fd events data)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_epollWait (epfd : Nat) (maxevents timeout : Int) :
    Audited (dispatchAudit (.epollWait epfd maxevents timeout)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgSet (attrs : WG.DeviceAttrs) :
    Audited (dispatchAudit (.wgSet attrs)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgGet (device : WG.DeviceRef) :
    Audited (dispatchAudit (.wgGet device)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgGetStart (device : WG.DeviceRef) :
    Audited (dispatchAudit (.wgGetStart device)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgGetRecv  :
    Audited (dispatchAudit (.wgGetRecv )) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgUp  :
    Audited (dispatchAudit (.wgUp )) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgXmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Audited (dispatchAudit (.wgXmit family addr payload opts)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgSetMtu (mtu : Nat) :
    Audited (dispatchAudit (.wgSetMtu mtu)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgDeladdr (family : Nat) :
    Audited (dispatchAudit (.wgDeladdr family)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgDelroute_full (family : Nat) (named : Bool)
    (dst plen oif typeCode metric : Nat) :
    Audited (dispatchAudit (.wgDelroute family named dst plen oif typeCode metric)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgDelroute (family : Nat) :
    Audited (dispatchAudit (.wgDelroute family false 0 0 0 0 0)) :=
  dispatch_wgDelroute_full family false 0 0 0 0 0

private theorem dispatch_wgAddroute (dst plen oif typeCode metric mtu : Nat) (nlflags : Nat) :
    Audited (dispatchAudit (.wgAddroute dst plen oif typeCode metric mtu nlflags)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgAddaddr (addr plen : Nat) :
    Audited (dispatchAudit (.wgAddaddr addr plen)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgAdvance (ticks : Nat) :
    Audited (dispatchAudit (.wgAdvance ticks)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_seccompInstall (via : Seccomp.InstallVia) (flags : UInt32) (filter : Option ClassicProg) (len : Option Nat) (bad : Seccomp.BadPtr) (mode : Nat) :
    Audited (dispatchAudit (.seccompInstall via flags filter len bad mode)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_seccompProbe (nr : Int) (args : Array UInt64) (where_ : Seccomp.ProbeWhere) (strict : Option Seccomp.StrictVia) :
    Audited (dispatchAudit (.seccompProbe nr args where_ strict)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_seccompPrctl (cmd : Seccomp.PrctlCmd) (args : Array UInt64) :
    Audited (dispatchAudit (.seccompPrctl cmd args)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_seccompCapdrop  :
    Audited (dispatchAudit (.seccompCapdrop )) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_seccompQuery (cmd : Seccomp.QueryCmd) (action flags : UInt32) :
    Audited (dispatchAudit (.seccompQuery cmd action flags)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgCreate  :
    Audited (dispatchAudit (.wgCreate )) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgDown  :
    Audited (dispatchAudit (.wgDown )) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgDelete  :
    Audited (dispatchAudit (.wgDelete )) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' dispatch_audit_steps

private theorem dispatch_wgNetnsClose  :
    Audited (dispatchAudit (.wgNetnsClose )) := by
  simp (config := {zeta := false}) only [dispatchAudit]
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
    simp (config := {zeta := false}) only [RxHistory.syscallDispatch]
    repeat' first
      | (environment_at "observe"; exact observe)
      | (environment_at "socketCallOn"; apply socketOn)
      | runner_support_steps
  | wgInject family port message tos ll dest => exact socketOn _ _ (inject family port message tos ll dest)
  | wgDeladdr family => exact audit_of (dispatch_wgDeladdr family)
  | wgDelroute family named dst plen oif typeCode metric => exact audit_of (dispatch_wgDelroute_full family named dst plen oif typeCode metric)
  | wgAddroute dst plen oif typeCode metric mtu nlflags => exact audit_of (dispatch_wgAddroute dst plen oif typeCode metric mtu nlflags)
  | wgAddaddr addr plen => exact audit_of (dispatch_wgAddaddr addr plen)
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
  repeat' first
    | (environment_at "syscallDispatch"; exact syscallDispatch _)
    | (environment_at "runSendWorkers"; exact runSendWorkers)
    | (environment_at "idleTimers"; exact idleTimers)
    | (environment_at "routeIntoWg0Audit"; exact route_support)
    | (environment_at "afterXmit"; exact afterXmit)
    | (environment_at "afterAdvance"; exact afterAdvance)
    | (environment_at "envNetnsCleanupAudit"; exact cleanup_support)
    | runner_support_steps

theorem history_empty : HistorySafe [] := by
  constructor
  · simp [HistoryAdapters.Valid,Origins.Valid]
  · intro pre e post he
    have hm : e ∈ ([] : List Event) := by rw [he]; simp
    cases hm

/-- The source fixture starts absent or with an empty key store for all flags.
Only the original seven WG fields are required of the product input. -/
theorem support_initial (net bare : Bool) (w : World)
    (hw : wgStoreView w.wg = wgStoreView (Runner.initialWG net bare)) : SupportInv [] w := by
  refine ⟨history_empty,?_⟩
  change Origins.Inv [] w.wg
  have hd := congrArg WGStoreView.dev hw
  change w.wg.dev = (if net && !bare then some {ifindex := 3,ifname := "wg0"} else none) at hd
  intro epoch keys hv id key hk valid
  by_cases active : (net && !bare) = true
  · simp only [view,hd,active,↓reduceIte,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hv
    obtain ⟨rfl,rfl⟩ := hv
    simp at hk
  · simp [view,hd,active] at hv

-- Seccomp prefill now operates only on SeccompWorld × TaskWorld. Its old
-- WG frame is type-given; initialization below keeps the actual WG input.

theorem runAtSupport_wp {g : Obs α} (hg : Preserves g) (index : Nat) (w : World) :
    ⦃fun h => ⌜SupportInv h w⌝⦄ runAtPrefix index w g
    ⦃post⟨fun out h => ⌜SupportInv h out.2⌝,fun _ h => ⌜HistorySafe h⌝⟩⦄ :=
  runAtPrefix_wp (show PrefixEnsures SupportInv HistorySafe g (fun _ => SupportInv) from hg) index w

private theorem supportRunnerTriple_ite {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps]
    {α : Type u} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c]
    (a b : m α) (ha : c → Triple a P Q) (hb : ¬c → Triple b P Q) :
    Triple (if c then a else b) P Q := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using ha h
  · simpa only [h, ↓reduceIte] using hb h

private theorem supportRunnerTriple_dite {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps]
    {α : Type u} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c]
    (a : c → m α) (b : ¬c → m α)
    (ha : ∀ h, Triple (a h) P Q) (hb : ∀ h, Triple (b h) P Q) :
    Triple (if h : c then a h else b h) P Q := by
  by_cases h : c
  · simpa only [h, ↓reduceDIte] using ha h
  · simpa only [h, ↓reduceDIte] using hb h

private theorem supportRunner_throw_bind {Event α β : Type} (e : Nat × Stop)
    (f : α → PrefixOuter Event β) :
    ((throw e : PrefixOuter Event α) >>= f) = throw e := rfl

/-- Select only the actual returned World in a runner accumulator. Other
results retain the current history assertion. -/
private def supportRunnerWorldAssertion (w : World) : Assertion
    (.except (Nat × Stop) (.arg (List Event) .pure)) :=
  fun h => ⌜SupportInv h w⌝

private def supportRunnerResultAssertion (type pre : Lean.Expr) : Lean.MetaM Lean.Expr := do
  Lean.Meta.withLocalDeclD `out type fun out => do
    let world? ←
      if ← Lean.Meta.isDefEq type (Lean.mkConst ``World) then pure (some out)
      else if type.isAppOf ``Prod then
        let args := type.getAppArgs
        if ← Lean.Meta.isDefEq args[0]! (Lean.mkConst ``World) then
          pure (some (Lean.mkProj ``Prod 0 out))
        else if ← Lean.Meta.isDefEq args[1]! (Lean.mkConst ``World) then
          pure (some (Lean.mkProj ``Prod 1 out))
        else pure none
      else pure none
    let assertion ← match world? with
      | some w => Lean.Meta.mkAppM ``supportRunnerWorldAssertion #[w]
      | none => pure pre
    Lean.Meta.mkLambdaFVars #[out] assertion

elab "support_runner_wp_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``Triple && ty.getAppArgs.size ≥ 3 do Lean.throwError "not a triple"
  let args := ty.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different action"

elab "support_runner_wp_call " name:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Triple && target.getAppArgs.size ≥ 3 do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``runAtPrefix && action.getAppArgs.size > 0 do Lean.throwError "not an indexed call"
  let .const actual _ := action.getAppArgs.back!.consumeMData.getAppFn
    | Lean.throwError "not a named observer"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different indexed observer"

elab "support_runner_wp_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let .app (.app (.app front action) pre) post := target | Lean.throwError "missing action"
  let rec head : Nat → Lean.Expr → Lean.Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE _ _ value body _ => head n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE _ _ value body _ => head n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Lean.Expr.equal next e then e else head n next
        | _ => e
  let mut next := head 64 action
  if (← Lean.Meta.matchMatcherApp? next).isSome then
    if let .reduced reduced ← Lean.Meta.reduceMatcher? next then next := reduced
  if Lean.Expr.equal action next then Lean.throwError "head unchanged"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp3 front next pre post)]

elab "support_runner_wp_match" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple && target.getAppArgs.size ≥ 3 do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless (← Lean.Meta.matchMatcherApp? action).isSome do Lean.throwError "not a head matcher"
  Lean.Elab.Tactic.replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

elab "support_runner_wp_throw_bind" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let aa := action.getAppArgs
  let .const name _ := aa[aa.size - 2]!.consumeMData.getAppFn
    | Lean.throwError "not a throw"
  unless name.toString.endsWith ".throw" do Lean.throwError "not a throw"
  Lean.Elab.Tactic.evalTactic (← `(tactic| rw [supportRunner_throw_bind]))

elab "support_runner_wp_bind" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let aa := action.getAppArgs
  let x := aa[aa.size - 2]!
  let type ← Lean.Meta.inferType x
  let result := type.getAppArgs.back!
  let q ← supportRunnerResultAssertion result args[args.size - 2]!
  let mut proof ← Lean.Meta.mkConstWithFreshMVarLevels ``Triple.bind
  let mut type ← Lean.Meta.inferType proof
  let mut goals : List Lean.MVarId := []
  while let .forallE name domain body _ := type.consumeMData do
    let argument ←
      match name.toString with
      | "m" => pure args[0]!
      | "ps" => pure args[1]!
      | "α" => pure result
      | "β" => pure args[3]!
      | "P" => pure args[args.size - 2]!
      | "Q" => pure q
      | "R" => pure args.back!
      | "x" => pure x
      | "f" => pure aa.back!
      | "hx" | "hf" =>
        let hole ← Lean.Meta.mkFreshExprMVar domain
        goals := goals ++ [hole.mvarId!]
        pure hole
      | _ => Lean.Meta.synthInstance domain
    unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType argument) domain do
      Lean.throwError "canonical bind parameter {name} has the wrong type"
    proof := Lean.mkApp proof argument
    type := body.instantiate1 argument
  goal.assign proof
  Lean.Elab.Tactic.replaceMainGoal goals

elab "support_runner_wp_array" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``ForIn.forIn do Lean.throwError "not forIn"
  let aa := action.getAppArgs
  let init := aa[aa.size - 2]!
  let result ← Lean.Meta.inferType init
  let q ← supportRunnerResultAssertion result args[args.size - 2]!
  let qterm ← Lean.PrettyPrinter.delab q
  let qtype ← Lean.PrettyPrinter.delab (← Lean.Meta.inferType q)
  let qsyntax ← `(term| ($qterm : $qtype))
  let err ← Lean.Meta.whnf (Lean.mkProj ``Prod 1 args.back!)
  let esyntax ← Lean.PrettyPrinter.delab err
  let psyntax ← Lean.PrettyPrinter.delab args[1]!
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    apply Triple.entails_wp_of_pre_post (ps := $psyntax) (Q' := ($qsyntax, $esyntax))))
  let rest := (← Lean.Elab.Tactic.getGoals).tail
  Lean.Elab.Tactic.setGoals [(← Lean.Elab.Tactic.getMainGoal)]
  Lean.Elab.Tactic.evalTactic (← `(tactic| rw [← Array.forIn_toList]))
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply Spec.forIn_list_const_inv))
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro hd acc))
  Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getGoals) ++ rest)

theorem runnerTail_support_wp (trace : Trace) (w : World) :
    ⦃fun h => ⌜SupportInv h w⌝⦄ RxHistory.runnerTail RxHistory.syscall trace w
    ⦃post⟨fun _ h => ⌜HistorySafe h⌝, fun _ h => ⌜HistorySafe h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtSupport_wp (syscall call) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtSupport_wp (lift_kernel skipAmbient (by
      intro initial
      exact productAmbient_spec _ _ (fun _ _ hi => hi))) index w
  unfold RxHistory.runnerTail
  repeat' first
    | (support_runner_wp_call RxHistory.syscall; apply Triple.entails_wp_of_pre_post (syscall_spec _ _ _))
    | (support_runner_wp_call liftPrefix; apply Triple.entails_wp_of_pre_post (ambient_spec _ _))
    | (support_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter Event) (ps := .except (Nat × Stop) (.arg (List Event) .pure)))
    | (support_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List Event)) (ps := .arg (List Event) .pure)))
    | support_runner_wp_throw_bind
    | support_runner_wp_bind
    | support_runner_wp_array
    | support_runner_wp_reduce
    | (support_runner_wp_head ite; apply supportRunnerTriple_ite)
    | (support_runner_wp_head dite; apply supportRunnerTriple_dite)
    | maintenance_intro
    | support_runner_wp_match
  all_goals try dsimp only [supportRunnerWorldAssertion] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; exact SupportInv.kernel hi rfl)
  all_goals try (solve | intro history hi; exact safe _ _ hi)


theorem executeTraceHistory_support_wp (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ RxHistory.executeTraceHistory trace placeholders
    ⦃post⟨fun _ h => ⌜HistorySafe h⌝, fun _ h => ⌜HistorySafe h⌝⟩⦄ := by
  have tail_spec (w : World) := runnerTail_support_wp trace w
  have boot_store (foreign : Bool) : SameView (fun w => wgStoreView w.wg)
      (do Net.Fib.bootTables
          if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit) := by
    apply SameView.bind
    · intro initial
      exact productRouting_spec _ (fun s => s.2.2.2 = initial)
    · intro _
      split
      · intro initial
        exact productRouting_spec _ (fun s => s.2.2.2 = initial)
      · exact SameView.pure _ _
  have boot_initial (w v : World) (x : Unit)
      (hr : (do Net.Fib.bootTables
                if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit).run w = .ok (x, v))
      (hi : wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare)) :
      wgStoreView v.wg = wgStoreView (initialWG trace.net trace.bare) :=
    ((ProjectedAction.iff_run _ _ _).mp (boot_store trace.foreign) w x v hr).trans hi
  unfold RxHistory.executeTraceHistory RxHistory.executeTraceWith
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild)
  all_goals repeat' first
    | (support_runner_wp_head RxHistory.runnerTail; apply Triple.entails_wp_of_pre_post (tail_spec _))
    | (support_runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter Event) (ps := .except (Nat × Stop) (.arg (List Event) .pure)))
    | (support_runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List Event)) (ps := .arg (List Event) .pure)))
    | support_runner_wp_throw_bind
    | support_runner_wp_bind
    | support_runner_wp_array
    | support_runner_wp_reduce
    | (support_runner_wp_head ite; apply supportRunnerTriple_ite)
    | (support_runner_wp_head dite; apply supportRunnerTriple_dite)
    | maintenance_intro
    | support_runner_wp_match
  all_goals try dsimp only [supportRunnerWorldAssertion] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; exact SupportInv.kernel hi rfl)
  all_goals try (solve | intro history hi; exact safe _ _ hi)
  all_goals
    intro history hi
    change history = [] at hi
    subst history
    first
    | change HistorySafe []
      exact history_empty
    | apply support_initial trace.net trace.bare
      first
      | rfl
      | rename_i hrun
        have hb := boot_initial _ _ _ hrun (by rfl)
        exact hb

/-- Every outcome retains actual receipt validity and strict-prefix material
support at successful decrypt and saved probe entries. Original JSON/indexed
Stop erasure is inherited from the unchanged observer. -/
theorem executeTraceHistory_support (trace : Runner.Trace) (placeholders : Bool) :
    HistorySafe (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 := by
  have hs := (prefixOuter_wp_iff _ _ _ _).mp (executeTraceHistory_support_wp trace placeholders) [] rfl
  cases hr : runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) [] with
  | mk result hist => cases result <;> simpa only [hr] using hs

end Leanux.Proofs.WG.Origins.HistorySupport
