import Leanux.Proofs.WG.AllowedIps.RoutingDumpFrames
import Leanux.Proofs.Framing.Syscalls
import Leanux.Proofs.WG.Lifetimes.SyscallDispatchAudit

/-! Literal original syscall wrappers and dispatch retain routing completions.
Ordinary negative results execute their actual cleanup and waiting suffixes;
Stops retain the completed journal and skip the remaining source continuation. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

def SyscallAddressShape : Syscall → Prop
  | .wgSet a => DeviceAddressShape a
  | _ => True

private theorem state_safe (initial : FlatTable × FlatTable) :
    ∀ h (w : World), GlobalCompletionState initial h w.wg → CompletionSafe initial h := fun _ _ hi => hi.1

private theorem lift_kernel (initial : FlatTable × FlatTable) (a : Leanux.M α) (ha : SameProductStore a) :
    PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg) (CompletionSafe initial) (liftPrefix a) :=
  global_completion_same World.wg initial a (routing_kernel a (ha.of_factor
    (fun store : ProductStore43 => store.2.2.2) (fun w : World => wgStoreView w.wg) (fun _ => rfl)))

private theorem lift_wg (initial : FlatTable × FlatTable) (a : Leanux.M α) (ha : SameView (fun w : World => wgStoreView w.wg) a) :
    PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg) (CompletionSafe initial) (liftPrefix a) :=
  global_completion_same World.wg initial a (wgKernel_routing a ha)

def socketCallOnObserved (fd : Nat) (body : PrefixM RoutingCompletion Int) : PrefixM RoutingCompletion Int := do
  let f ← liftPrefix (liftFS (fdget fd))
  if f.file.isNone then return -EBADF
  let ret ← body
  liftPrefix (liftFS (fdput f))
  return ret

def socketCallObserved (body : PrefixM RoutingCompletion Int) : PrefixM RoutingCompletion Int := socketCallOnObserved NETLINK_FD body

def netlinkRequestObserved (handler : PrefixM RoutingCompletion Int) : PrefixM RoutingCompletion Int := do
  let ret ← socketCallObserved do
    liftPrefix (skipCut allocCuts)
    let ret ← handler
    liftPrefix (skipCut allocCuts)
    pure ret
  _ ← socketCallObserved (pure 0)
  return ret

def rtnetlinkRequestObserved (handler : PrefixM RoutingCompletion Int) : PrefixM RoutingCompletion Int := do
  let fs ← liftPrefix getFiles
  let t := fs.fdt
  let some fd := (List.range t.maxFds).find? (fun n => n ≥ fs.nextFd && !(t.openFds.getD n true))
    | liftPrefix (unsupported "no free descriptor in the table for the temporary rtnetlink socket (expansion)")
  if fd ≥ (← liftPrefix (getTask .task)).rlimitNofile then
    liftPrefix (unsupported "no descriptor below RLIMIT_NOFILE for the temporary rtnetlink socket (the guest fails)")
  let fid := (← liftPrefix get).fs.nextFile
  liftPrefix (liftFS (setFile fid { fFlags := O_RDWR, fMode := FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED, fCount := 1, fOp := some (.fixture "rtnetlink"), fInode := some (.fixture "rtnetlink") }))
  liftPrefix (modify fun w => { w with fs := {w.fs with nextFile := fid + 1} })
  liftPrefix (liftFS (setFdtSlot fd (some fid)))
  liftPrefix (liftFS (setFdtOpen fd true))
  liftPrefix (liftFS (setFdtCloexec fd false))
  -- the request's, the acknowledgement's and the notifications' skbs are
  -- below the cut (allocation cut sites), as in `netlinkRequest`
  let ret ← socketCallOnObserved fd do
    liftPrefix (skipCut allocCuts)
    let ret ← handler
    liftPrefix (skipCut allocCuts)
    pure ret
  _ ← socketCallOnObserved fd (pure 0)
  -- close(fd) after the window
  liftPrefix (liftFS (setFdtSlot fd none))
  liftPrefix (liftFS (setFdtOpen fd false))
  liftPrefix (modifyFiles fun fs => { fs with nextFd := fd })
  liftPrefix (liftFS (freeFile fid))
  return ret

abbrev netnsCloseObserved : PrefixM RoutingCompletion Int := liftPrefix netnsClose

macro "routing_wrapper_erasure" : tactic => `(tactic|
  first | assumption | control_audit_erases)

macro "routing_syscall_component" initial:term : tactic => `(tactic|
  first
    | (audit_contract_head getCurrent; apply lift_wg $initial
       intro view
       unfold Leanux.getCurrent
       change Hoare (liftFS (StateT.lift TaskM.getCurrent)) _ _
       exact productFS_spec (StateT.lift TaskM.getCurrent)
         (fun w => wgStoreView w.wg = view) (fun _ _ _ _ hi => hi))
    | (audit_contract_head liftFS; apply lift_wg $initial
       intro view; exact productFS_spec _ _ (fun _ _ _ _ hi => hi))
    | (audit_contract_head liftTask; apply lift_wg $initial
       intro view; exact productTask_spec _ _ (fun _ _ _ hi => hi))
    | (audit_contract_head liftSeccomp; apply lift_wg $initial
       intro view; exact productSeccomp_spec _ _ (fun _ _ _ _ hi => hi))
    | (audit_contract_head liftPrefix; apply lift_wg $initial; first
        | (intro view; exact productAmbient_spec _ _ (fun _ _ hi => hi))
        | (apply (ProjectedAction.iff_run _ _ _).mpr
           intro w x v hr
           cases hr
           rfl)))

macro "routing_wrapper_preservation" initial:term : tactic => `(tactic|
  first
    | assumption
    | (audit_contract PrefixPreserves; apply PrefixEnsures.preserves)
    | routing_syscall_component $initial
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure (state_safe $initial) _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind
        (Q := fun _ h (w : World) => GlobalCompletionState $initial h w.wg))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_intro
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars))

theorem socketCallOnObserved_erases (fd : Nat) (body : PrefixM RoutingCompletion Int) (original : Leanux.M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (socketCallOnObserved fd body) (socketCallOn fd original) := by
  unfold socketCallOnObserved socketCallOn
  repeat' routing_wrapper_erasure

theorem socketCallOnObserved_global (initial : FlatTable × FlatTable) (fd : Nat)
    (body : PrefixM RoutingCompletion Int)
    (hb : PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg) (CompletionSafe initial) body) :
    PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg) (CompletionSafe initial) (socketCallOnObserved fd body) := by
  apply PrefixEnsures.preserves
  unfold socketCallOnObserved
  repeat' routing_wrapper_preservation initial

theorem netlinkRequestObserved_erases (body : PrefixM RoutingCompletion Int) (original : Leanux.M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (netlinkRequestObserved body) (netlinkRequest original) := by
  unfold netlinkRequestObserved netlinkRequest socketCallObserved socketCall
  repeat' first | (maintenance_head socketCallOnObserved; apply socketCallOnObserved_erases) | routing_wrapper_erasure

theorem netlinkRequestObserved_global (initial : FlatTable × FlatTable) (body : PrefixM RoutingCompletion Int)
    (hb : PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg) (CompletionSafe initial) body) :
    PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg) (CompletionSafe initial) (netlinkRequestObserved body) := by
  have hcut : PrefixPreserves
      (fun h (w : World) => GlobalCompletionState initial h w.wg)
      (CompletionSafe initial) (liftPrefix (skipCut allocCuts)) := by
    apply lift_wg initial
    intro view
    exact productAmbient_spec _ _ (fun _ _ hi => hi)
  unfold netlinkRequestObserved socketCallObserved
  refine PrefixPreserves.bind (socketCallOnObserved_global initial _ _ ?_) ?_
  · refine PrefixPreserves.bind hcut ?_
    intro _
    refine PrefixPreserves.bind hb ?_
    intro ret
    refine PrefixPreserves.bind hcut ?_
    intro _
    exact PrefixPreserves.pure (state_safe initial) ret
  · intro ret
    refine PrefixPreserves.bind
      (socketCallOnObserved_global initial _ _ (PrefixPreserves.pure (state_safe initial) 0)) ?_
    intro _
    exact PrefixPreserves.pure (state_safe initial) ret

theorem rtnetlinkRequestObserved_erases (body : PrefixM RoutingCompletion Int) (original : Leanux.M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (rtnetlinkRequestObserved body) (rtnetlinkRequest original) := by
  unfold rtnetlinkRequestObserved rtnetlinkRequest
  repeat' first | (maintenance_head socketCallOnObserved; apply socketCallOnObserved_erases) | routing_wrapper_erasure

theorem rtnetlinkRequestObserved_global (initial : FlatTable × FlatTable) (body : PrefixM RoutingCompletion Int)
    (hb : PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg) (CompletionSafe initial) body) :
    PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg) (CompletionSafe initial) (rtnetlinkRequestObserved body) := by
  apply PrefixEnsures.preserves
  unfold rtnetlinkRequestObserved
  repeat' first | (audit_contract_head socketCallOnObserved; apply socketCallOnObserved_global initial) | routing_wrapper_preservation initial

def dispatchObserved : Syscall → PrefixM RoutingCompletion Int
  | .eventfd2 count flags => liftPrefix (liftFS (sysEventfd2 count flags))
  | .dup fildes => liftPrefix (liftFS (sysDup fildes))
  | .dup3 oldfd newfd flags => liftPrefix (liftFS (ksysDup3 oldfd newfd flags))
  | .close fd => liftPrefix (liftFS (sysClose fd))
  | .read fd count => liftPrefix (liftFS (ksysRead fd count))
  | .write fd count buf => liftPrefix (liftFS (ksysWrite fd buf count))
  | .pipe2 flags => liftPrefix (liftFS (sysPipe2 flags))
  | .fcntl fd cmd arg => liftPrefix (liftFS (sysFcntl fd cmd arg))
  | .epollCreate1 flags => liftPrefix (liftFS (sysEpollCreate1 flags))
  | .epollCtl epfd op fd events data => liftPrefix (liftFS (sysEpollCtl epfd op fd events data))
  | .epollWait epfd maxevents timeout => liftPrefix (liftFS (sysEpollWait epfd maxevents timeout))
  | .wgSet attrs => netlinkRequestObserved (liftWGObserver (wgSetDeviceObserved attrs))
  | .wgGet device => netlinkRequestObserved do
    match ← liftPrefix (liftWG (wgGetDevice device)) with
    | .error e => return e
    | .ok device =>
      liftPrefix (modifyAmbient fun w => { w with extraOut := [("device", device)] })
      return 0
  -- W2 (4.2): one system call each on the stepped socket, the netlink
  -- core's chunk allocations below the cut as in `netlinkRequestObserved`. The
  -- stepped operations that run no WireGuard code are outside the domain
  -- [AGENT, coordinator 2026-10-12: the WireGuard boundary, the af_netlink.c
  -- loop unanchored]: `-EAGAIN` (nothing queued), and a receive that pops
  -- only `NLMSG_DONE` or an acknowledgement (the dump call that produced
  -- it ran in the previous operation).
  | .wgGetStart device => socketCallOnObserved DUMP_FD do
    liftPrefix (skipCut allocCuts)
    -- netlink_autobind (af_netlink.c:803-830) on the socket's first sendmsg:
    -- its port id, the process's, is the fixture socket's, so the collision
    -- draws once (:820); the port id reaches no modeled path (a cut)
    let sock ← liftPrefix (liftWG (WG.getNlSock DUMP_FD))
    if !sock.bound then
      liftPrefix (skipCutExactly .netlinkAutobindPort 1 allocCuts)
      liftPrefix (liftWG (WG.setNlSock DUMP_FD { sock with bound := true }))
    liftPrefix (liftWG (netlinkDumpStart DUMP_FD device))
    liftPrefix (skipCut allocCuts)
    return 0
  | .wgGetRecv => socketCallOnObserved DUMP_FD do
    liftPrefix (skipCut allocCuts)
    let some messages ← liftPrefix (liftWG (netlinkRecvmsg DUMP_FD))
      | liftPrefix (unsupported "wg_get_recv with nothing queued (-EAGAIN): no WireGuard code runs")
    liftPrefix (skipCut allocCuts)
    -- the chunk carrying the DONE and a start error's acknowledgement run no
    -- WireGuard code but carry the dump's data or the lookup's error code; a
    -- lone NLMSG_DONE (one that did not fit its chunk) carries nothing and
    -- stays outside the domain, as does the `-EBUSY` acknowledgement
    -- (netlinkDumpStart stops at the start)
    if messages.all (· matches .done ..) then
      liftPrefix (unsupported "wg_get_recv popping a lone NLMSG_DONE: no WireGuard code runs")
    liftPrefix (modifyAmbient fun w => { w with extraOut := [("messages", Lean.Json.arr (messages.map (·.toJson)).toArray)] })
    return 0
  | .wgUp => socketCallOnObserved SENDER_FD (liftPrefix Env.wgUp)
  | .wgXmit family addr payload opts => socketCallOnObserved SENDER_FD do
    -- W9: the sender's `sendto` routes on the fixture's tables
    -- (the environment routing tables): into wg0 by the default route the guest adds after
    -- a successful wg_up (and removes with a down, a deletion or
    -- `wg_delroute`), else `-ENETUNREACH`; a local destination never
    -- reaches wg0
    let r ← match ← liftPrefix (Net.routeLookup family 0 addr) with
      | .error err => return err
      | .ok r => pure r
    if r.dev != WG0_IFINDEX then liftPrefix (unsupported "a transmit to a local address (not into wg0)")
    -- W4: an MTU change below the family's floor took its routes down with
    -- its IP device, and the fixture re-adds them only at the next wg_up
    if let some d := (← liftPrefix getWG).dev then
      if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
        liftPrefix (unsupported "a transmit after an MTU change took the family's routes into wg0 down")
    -- udp_sendmsg returns the datagram's length once the device took it
    liftPrefix Env.fixtureSend
    let opts := { opts with routeMtu := opts.routeMtu <|> (if r.mtu != 0 then some r.mtu else none) }
    match ← liftPrefix (Env.xmitPackets family addr payload opts) with
    | .error e => return e   -- refused by the sender's IP layer before any output
    | .ok (pkts, mtu) =>
      liftPrefix (Env.xmitMulticastLoop family addr)
      if family == 4 then liftPrefix (Net.neighbourClassify WG0_IFINDEX)
      let ret ← liftPrefix (liftWG (wgXmit family addr pkts mtu))
      return if ret == 0 then payload.length else ret
  | .wgSetMtu mtu => socketCallOnObserved SENDER_FD (liftPrefix (Env.setMtu mtu))
  | .wgInject family port message tos ll dest => socketCallOnObserved SENDER_FD (liftPrefix (Env.inject family port message tos ll dest))
  | .wgDeladdr family => rtnetlinkRequestObserved (liftPrefix (Env.wgDeladdr family))
  | .wgDelroute family named dst plen oif typeCode metric =>
    rtnetlinkRequestObserved (liftPrefix (Env.wgDelroute family named dst plen oif typeCode metric))
  | .wgAddroute dst plen oif typeCode metric mtu nlflags =>
    rtnetlinkRequestObserved (liftPrefix (Env.wgAddroute dst plen oif typeCode metric mtu nlflags))
  | .wgAddaddr addr plen => rtnetlinkRequestObserved (liftPrefix (Env.wgAddaddr addr plen))
  | .wgFlood count port family messages => liftPrefix (Env.flood count port family messages)
  -- W7: the io_uring submission's descriptor plumbing (the ring's fdget, each
  -- send's fget of the sender) is the fixture's, as the flood's is: not modeled
  | .wgBatch items _ => liftPrefix (Env.batch items)
  | .wgObserve => do
    -- the fixture's observation happens whether or not the listener is still
    -- open (W8: after wg_netns_close the `recvfrom(4)` is -EBADF and the
    -- datagrams null, the sender's inbox and the stats are read as always)
    let (ret, observed) ← liftPrefix Env.observe
    liftPrefix (modifyAmbient fun w => { w with extraOut := ["datagrams", "replies", "stats"].map fun k => (k, observed.getObjValD k) })
    socketCallOnObserved LISTEN4_FD (pure ret)
  | .wgAdvance ticks => do
    -- `ioctl(3, KCOV_LEANUX_TIME_ADVANCE, &ticks)`: `CLASS(fd, f)(fd)`
    -- (fs/ioctl.c), then the LEANUX case of `kcov_ioctl` (a cut point but
    -- for its kind-304 record)
    let f ← liftPrefix (liftFS (fdget KCOV_FD))
    if f.file.isNone then liftPrefix (unsupported "wg_advance after the trace closed the KCOV descriptor")
    let ret ← liftPrefix (Env.advance ticks)
    liftPrefix (liftFS (fdput f))
    return ret
  | .wgCreate => rtnetlinkRequestObserved (liftPrefix (liftWG wgCreate))
  | .wgDown => socketCallOnObserved SENDER_FD (liftPrefix Env.wgDown)
  | .wgDelete => rtnetlinkRequestObserved envWgDeleteObserved
  | .wgNetnsClose => netnsCloseObserved
  | .seccompInstall via flags filter len bad mode => liftPrefix (liftSeccomp (Seccomp.sysSeccompInstall via flags filter len bad mode))
  | .seccompProbe nr args .self _ => liftPrefix (liftSeccomp (Seccomp.sysSeccompProbeSelf nr args))
  | .seccompProbe nr args .child strict => liftPrefix (liftSeccomp (Seccomp.sysSeccompProbeChild nr args strict))
  | .seccompPrctl cmd args => liftPrefix (liftSeccomp (Seccomp.sysSeccompPrctl cmd args))
  | .seccompCapdrop => liftPrefix (liftSeccomp (Seccomp.sysSeccompCapdrop))
  | .seccompQuery cmd action flags => liftPrefix (liftSeccomp (Seccomp.sysSeccompQuery cmd action flags))

def syscallObserved (call : Syscall) : PrefixM RoutingCompletion Int := do
  liftPrefix (modify fun w => { w with fs := { w.fs with userOut := none, userFds := none }, seccomp := { w.seccomp with emitted := {}, translatedLen := none } })
  liftPrefix (modifyWG fun g => { g with queuedThisCall := [] })
  liftPrefix (modifyAmbient fun a => { a with steps := #[], extraOut := [], fired := #[], netRxSections := 0, netRxSection := 0 })
  -- seccomp: the entry path of the operation's own call once a mode is set
  -- (a harness call by design 6.2 rule 1: a cache hit); a probe enters itself
  match syscallNr call with
  | some nr => liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none =>
    if call.isNet && (← liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  let ret ← dispatchObserved call
  -- harness calls whose entry falls inside the window after the operation's (fixture knowledge)
  for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
  liftPrefix (liftFS taskWorkRun)
  -- the guest waits inside the operations that can queue the handshake send
  -- worker (and in wg_inject); the worker runs during that wait
  -- worker; D3: a timer may fire in these waits (`liftPrefix Env.idleTimers`)
  match call with
  | .wgSet _ | .wgInject .. => liftPrefix Env.runSendWorkers; liftPrefix Env.idleTimers
  -- W9 (design 14.3b): the guest's route adds follow the up's wait
  | .wgUp => liftPrefix Env.runSendWorkers; liftPrefix Env.idleTimers; liftPrefix Env.routeIntoWg0
  | .wgXmit .. => liftPrefix Env.afterXmit; liftPrefix Env.idleTimers
  | .wgBatch .. => liftPrefix Env.idleTimers   -- W7: the batch runs its queued units itself
  -- D3: the guest waits after the advance; the next tick runs the due timers
  | .wgAdvance _ => liftPrefix Env.afterAdvance
  -- W8: the namespace's teardown section runs in the guest's wait
  | .wgNetnsClose => liftPrefix Env.netnsCleanup
  | _ => pure ()
  match call with
  | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
  | .wgAddroute .. | .wgAddaddr .. =>
    let shape := Net.Fib.shape (← liftPrefix getRouting)
    liftPrefix (modifyAmbient fun w => { w with extraOut := w.extraOut ++ [("fib_trie", shape)] })
  | _ => pure ()
  return ret


/-- Select the actual native action inside a product observer lift. -/
elab "routing_lift_head " name:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless ty.isAppOf ``PrefixEnsures && args.size ≥ 2 do
    Lean.throwError "not a prefix contract"
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``liftPrefix && !action.getAppArgs.isEmpty do
    Lean.throwError "not a product lift"
  let native := action.getAppArgs.back!.consumeMData
  unless native.isAppOf ``liftWG && !native.getAppArgs.isEmpty do
    Lean.throwError "not a native WG adapter"
  let .const actual _ := native.getAppArgs.back!.consumeMData.getAppFn
    | Lean.throwError "not a named native action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different native action"

macro "routing_syscall_erasure" : tactic => `(tactic|
  first
    | (maintenance_head netnsCloseObserved; exact erasesPrefix_lift _)
    | (maintenance_head wgSetDeviceObserved; exact liftWGObserver_erases (wgSetDeviceObserved_erases _))
    | (maintenance_head envWgDeleteObserved; exact envWgDeleteObserved_erases)
    | (maintenance_head netlinkRequestObserved; apply netlinkRequestObserved_erases)
    | (maintenance_head rtnetlinkRequestObserved; apply rtnetlinkRequestObserved_erases)
    | (maintenance_head socketCallOnObserved; apply socketCallOnObserved_erases)
    | (maintenance_head ForIn.forIn; apply erasesPrefix_forIn)
    | control_audit_erases)

theorem dispatchObserved_erases (call : Syscall) : ErasesPrefix (dispatchObserved call) (dispatch call) := by
  cases call
  case seccompProbe nr args target strict =>
    cases target <;> exact erasesPrefix_lift _
  all_goals unfold dispatchObserved dispatch
  all_goals repeat' routing_syscall_erasure

macro "routing_dispatch_preservation" initial:ident shape:ident : tactic => `(tactic|
  first
    | contradiction
    | (audit_contract PrefixPreserves; apply PrefixEnsures.preserves)
    | (audit_contract_head netlinkRequestObserved; apply netlinkRequestObserved_global $initial)
    | (audit_contract_head rtnetlinkRequestObserved; apply rtnetlinkRequestObserved_global $initial)
    | (audit_contract_head socketCallOnObserved; apply socketCallOnObserved_global $initial)
    | (maintenance_head wgSetDeviceObserved; exact
        (wgSetDeviceObserved_global $initial _ (by simpa only [SyscallAddressShape] using $shape)).liftWGObserver)
    | (maintenance_head envWgDeleteObserved; exact envWgDeleteObserved_global $initial)
    | (audit_contract_head netnsCloseObserved; exact lift_wg $initial _ SyscallFrames.netnsClose_sameWGStore)
    | (routing_lift_head wgCreate; simpa only [liftWGObserver_lift] using (wgCreate_global_completion $initial).liftWGObserver)
    | (routing_lift_head wgGetDevice; exact global_completion_lift World.wg $initial _ (wgGetDevice_routing _).liftWG)
    | (routing_lift_head netlinkDumpStart; exact global_completion_lift World.wg $initial _ (netlinkDumpStart_routing _ _).liftWG)
    | (routing_lift_head netlinkRecvmsg; exact global_completion_lift World.wg $initial _ (netlinkRecvmsg_routing _).liftWG)
    | (routing_lift_head wgXmit; exact global_completion_lift World.wg $initial _ (wgXmit_routing _ _ _ _).liftWG)
    | (audit_contract_head Env.wgUp; exact global_completion_lift World.wg $initial _ envWgUp_routing)
    | (audit_contract_head Env.wgDown; exact global_completion_lift World.wg $initial _ envWgDown_routing)
    | (audit_contract_head Env.inject; exact global_completion_lift World.wg $initial _ (inject_routing _ _ _ _ _ _))
    | (audit_contract_head Env.flood; exact global_completion_lift World.wg $initial _ (flood_routing _ _ _ _))
    | (audit_contract_head Env.batch; exact global_completion_lift World.wg $initial _ (batch_routing _))
    | (audit_contract_head Env.observe; exact global_completion_lift World.wg $initial _ observe_routing)
    | (audit_contract_head Env.runSendWorkers; exact global_completion_lift World.wg $initial _ runSendWorkers_routing)
    | (audit_contract_head Env.idleTimers; exact global_completion_lift World.wg $initial _ idleTimers_routing)
    | (audit_contract_head Env.afterXmit; exact global_completion_lift World.wg $initial _ afterXmit_routing)
    | (audit_contract_head Env.afterAdvance; exact global_completion_lift World.wg $initial _ afterAdvance_routing)
    | (audit_contract_head Env.netnsCleanup; exact global_completion_lift World.wg $initial _ netnsCleanup_routing)
    | (audit_contract_head Env.setMtu; exact global_completion_same World.wg $initial _ (envSetMtu_routing _))
    | (audit_contract_head Env.wgDeladdr; exact global_completion_same World.wg $initial _ (wgDeladdr_routing _))
    | (audit_contract_head Env.advance; exact global_completion_same World.wg $initial _ (advance_routing _))
    | (audit_contract_head Env.xmitMulticastLoop; exact global_completion_same World.wg $initial _ (xmitMulticastLoop_routing _ _))
    | (audit_contract_head Env.routeIntoWg0; exact global_completion_same World.wg $initial _ routeIntoWg0_routing)
    | (audit_contract_head Env.wgDelroute; apply lift_wg $initial; unfold Env.wgDelroute; syscall_routing_store)
    | (audit_contract_head Env.wgAddroute; apply lift_wg $initial; unfold Env.wgAddroute; syscall_routing_store)
    | (audit_contract_head Env.wgAddaddr; apply lift_wg $initial; unfold Env.wgAddaddr; syscall_routing_store)
    | (routing_lift_head getNlSock; apply lift_wg $initial
       exact sameView_liftWG _ id _ (getNlSock_sameWGWorld _) (fun _ _ _ hi => congrArg wgStoreView hi))
    | (routing_lift_head setNlSock; apply global_completion_same World.wg $initial
       exact sameView_liftWG _ routingView _ (dump_routing_native _ (setNlSock_sameDump _ _)) (fun _ _ _ hi => hi))
    | (audit_contract_head Env.xmitPackets; exact lift_kernel $initial _ (xmitPackets_sameKernel _ _ _ _))
    | (audit_contract_head Env.fixtureSend; unfold Env.fixtureSend)
    | (audit_contract_head netnsClose; exact lift_wg $initial _ SyscallFrames.netnsClose_sameWGStore)
    | (control_audit_routing; apply lift_wg $initial
       intro view; exact productRouting_spec _ (fun store => store.2.2.2 = view))
    | routing_syscall_component $initial
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure (state_safe $initial) _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind
        (Q := fun _ h (w : World) => GlobalCompletionState $initial h w.wg))
    | (maintenance_head ForIn.forIn; apply PrefixEnsures.forInInvariant _ _ _
        (fun _ h (w : World) => GlobalCompletionState $initial h w.wg) _ (fun _ => state_safe $initial))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_intro
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars))

theorem dispatchObserved_global (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : SyscallAddressShape call) :
    PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg)
      (CompletionSafe initial) (dispatchObserved call) := by
  apply PrefixEnsures.preserves
  cases call <;> unfold dispatchObserved
  all_goals repeat' routing_dispatch_preservation initial shape

theorem syscallObserved_erases (call : Syscall) : ErasesPrefix (syscallObserved call) (syscall call) := by
  unfold syscallObserved syscall
  repeat' first
    | (maintenance_head dispatchObserved; exact dispatchObserved_erases _)
    | routing_syscall_erasure

theorem syscallObserved_global (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : SyscallAddressShape call) :
    PrefixPreserves (fun h (w : World) => GlobalCompletionState initial h w.wg)
      (CompletionSafe initial) (syscallObserved call) := by
  apply PrefixEnsures.preserves
  unfold syscallObserved
  repeat' first
    | (audit_contract_head dispatchObserved; exact dispatchObserved_global initial _ shape)
    | routing_dispatch_preservation initial shape

end Leanux.Proofs.WG.Configuration
