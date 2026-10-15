import Leanux.Proofs.WG.AllowedIps.RoutingDumpFrames
import Leanux.Proofs.Framing.Syscalls
import Leanux.Proofs.Framing.Seccomp
import Leanux.Proofs.WG.Lifetimes.SyscallsAudit

/-! Literal original syscall wrappers and dispatch retain routing completions.
Ordinary negative results execute their actual cleanup and waiting suffixes;
Stops retain the completed journal and skip the remaining source continuation. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.Lifetimes Std.Do
open Leanux.Proofs.Framing.KernelFrames
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

def SyscallAddressShape : Syscall → Prop
  | .wgSet a => DeviceAddressShape a
  | _ => True

private theorem state_safe (initial : FlatTable × FlatTable) :
    ∀ h w, GlobalCompletionState initial h w → CompletionSafe initial h := fun _ _ hi => hi.1

private theorem lift_kernel (initial : FlatTable × FlatTable) (a : M α) (ha : SameKernel a) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (liftPrefix a) :=
  global_completion_same initial a (routing_kernel a ha)

private theorem lift_wg (initial : FlatTable × FlatTable) (a : M α) (ha : SameWGKernel a) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (liftPrefix a) :=
  global_completion_same initial a (wgKernel_routing a ha)

def socketCallOnObserved (fd : Nat) (body : PrefixM RoutingCompletion Int) : PrefixM RoutingCompletion Int := do
  let f ← liftPrefix (fdget fd)
  if f.file.isNone then return -EBADF
  let ret ← body
  liftPrefix (fdput f)
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
  if fd ≥ (← liftPrefix getK).task.rlimitNofile then
    liftPrefix (unsupported "no descriptor below RLIMIT_NOFILE for the temporary rtnetlink socket (the guest fails)")
  let fid := (← liftPrefix getK).nextFile
  liftPrefix (setFile fid { fFlags := O_RDWR, fMode := FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED, fCount := 1, fOp := some (.fixture "rtnetlink"), fInode := some (.fixture "rtnetlink") })
  liftPrefix (modifyK fun k => { k with nextFile := fid + 1 })
  liftPrefix (setFdtSlot fd (some fid))
  liftPrefix (setFdtOpen fd true)
  liftPrefix (setFdtCloexec fd false)
  -- the request's, the acknowledgement's and the notifications' skbs are
  -- below the cut (allocation cut sites), as in `netlinkRequest`
  let ret ← socketCallOnObserved fd do
    liftPrefix (skipCut allocCuts)
    let ret ← handler
    liftPrefix (skipCut allocCuts)
    pure ret
  _ ← socketCallOnObserved fd (pure 0)
  -- close(fd) after the window
  liftPrefix (setFdtSlot fd none)
  liftPrefix (setFdtOpen fd false)
  liftPrefix (modifyFiles fun fs => { fs with nextFd := fd })
  liftPrefix (freeFile fid)
  return ret

abbrev netnsCloseObserved : PrefixM RoutingCompletion Int := liftPrefix netnsClose

macro "routing_wrapper_erasure" : tactic => `(tactic|
  repeat' first
    | assumption
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

macro "routing_wrapper_preservation" initial:term : tactic => `(tactic|
  repeat' first
    | assumption
    | with_reducible exact lift_wg $initial _ (FSFrames.fdget_sameWGKernel _)
    | with_reducible exact lift_wg $initial _ (FSFrames.fdput_sameWGKernel _)
    | with_reducible exact lift_wg $initial _ getFiles_sameWGKernel
    | with_reducible exact lift_wg $initial _ (modifyFiles_sameWGKernel _)
    | with_reducible exact lift_wg $initial _ (setFile_sameWGKernel _ _)
    | with_reducible exact lift_wg $initial _ (freeFile_sameWGKernel _)
    | with_reducible exact lift_wg $initial _ (setFdtSlot_sameWGKernel _ _)
    | with_reducible exact lift_wg $initial _ (setFdtOpen_sameWGKernel _ _)
    | with_reducible exact lift_wg $initial _ (setFdtCloexec_sameWGKernel _ _)
    | with_reducible exact lift_kernel $initial _ (skipCut_sameKernel _)
    | exact lift_wg $initial _ (by intro w x v hr; cases hr; rfl)
    | exact lift_wg $initial _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (state_safe $initial) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem socketCallOnObserved_erases (fd : Nat) (body : PrefixM RoutingCompletion Int) (original : M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (socketCallOnObserved fd body) (socketCallOn fd original) := by
  unfold socketCallOnObserved socketCallOn
  routing_wrapper_erasure

theorem socketCallOnObserved_global (initial : FlatTable × FlatTable) (fd : Nat)
    (body : PrefixM RoutingCompletion Int)
    (hb : PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) body) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (socketCallOnObserved fd body) := by
  unfold socketCallOnObserved
  routing_wrapper_preservation initial

theorem netlinkRequestObserved_erases (body : PrefixM RoutingCompletion Int) (original : M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (netlinkRequestObserved body) (netlinkRequest original) := by
  unfold netlinkRequestObserved netlinkRequest socketCallObserved socketCall
  repeat' first | with_reducible apply socketCallOnObserved_erases | routing_wrapper_erasure

theorem netlinkRequestObserved_global (initial : FlatTable × FlatTable) (body : PrefixM RoutingCompletion Int)
    (hb : PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) body) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (netlinkRequestObserved body) := by
  unfold netlinkRequestObserved socketCallObserved
  repeat' first | with_reducible apply socketCallOnObserved_global initial | routing_wrapper_preservation initial

theorem rtnetlinkRequestObserved_erases (body : PrefixM RoutingCompletion Int) (original : M Int)
    (hb : ErasesPrefix body original) :
    ErasesPrefix (rtnetlinkRequestObserved body) (rtnetlinkRequest original) := by
  unfold rtnetlinkRequestObserved rtnetlinkRequest
  repeat' first | with_reducible apply socketCallOnObserved_erases | routing_wrapper_erasure

theorem rtnetlinkRequestObserved_global (initial : FlatTable × FlatTable) (body : PrefixM RoutingCompletion Int)
    (hb : PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) body) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (rtnetlinkRequestObserved body) := by
  unfold rtnetlinkRequestObserved
  repeat' first | with_reducible apply socketCallOnObserved_global initial | routing_wrapper_preservation initial

def dispatchObserved : Syscall → PrefixM RoutingCompletion Int
  | .eventfd2 count flags => liftPrefix (sysEventfd2 count flags)
  | .dup fildes => liftPrefix (sysDup fildes)
  | .dup3 oldfd newfd flags => liftPrefix (ksysDup3 oldfd newfd flags)
  | .close fd => liftPrefix (sysClose fd)
  | .read fd count => liftPrefix (ksysRead fd count)
  | .write fd count buf => liftPrefix (ksysWrite fd buf count)
  | .pipe2 flags => liftPrefix (sysPipe2 flags)
  | .fcntl fd cmd arg => liftPrefix (sysFcntl fd cmd arg)
  | .epollCreate1 flags => liftPrefix (sysEpollCreate1 flags)
  | .epollCtl epfd op fd events data => liftPrefix (sysEpollCtl epfd op fd events data)
  | .epollWait epfd maxevents timeout => liftPrefix (sysEpollWait epfd maxevents timeout)
  | .wgSet attrs => netlinkRequestObserved (wgSetDeviceObserved attrs)
  | .wgGet device => netlinkRequestObserved do
    match ← liftPrefix (wgGetDevice device) with
    | .error e => return e
    | .ok device =>
      liftPrefix (modify fun w => { w with extraOut := [("device", device)] })
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
    let sock ← liftPrefix (WG.getNlSock DUMP_FD)
    if !sock.bound then
      liftPrefix (skipCutExactly .netlinkAutobindPort 1 allocCuts)
      liftPrefix (WG.setNlSock DUMP_FD { sock with bound := true })
    liftPrefix (netlinkDumpStart DUMP_FD device)
    liftPrefix (skipCut allocCuts)
    return 0
  | .wgGetRecv => socketCallOnObserved DUMP_FD do
    liftPrefix (skipCut allocCuts)
    let some messages ← liftPrefix (netlinkRecvmsg DUMP_FD)
      | liftPrefix (unsupported "wg_get_recv with nothing queued (-EAGAIN): no WireGuard code runs")
    liftPrefix (skipCut allocCuts)
    -- the chunk carrying the DONE and a start error's acknowledgement run no
    -- WireGuard code but carry the dump's data or the lookup's error code; a
    -- lone NLMSG_DONE (one that did not fit its chunk) carries nothing and
    -- stays outside the domain, as does the `-EBUSY` acknowledgement
    -- (netlinkDumpStart stops at the start)
    if messages.all (· matches .done ..) then
      liftPrefix (unsupported "wg_get_recv popping a lone NLMSG_DONE: no WireGuard code runs")
    liftPrefix (modify fun w => { w with extraOut := [("messages", Lean.Json.arr (messages.map (·.toJson)).toArray)] })
    return 0
  | .wgUp => socketCallOnObserved SENDER_FD (liftPrefix Env.wgUp)
  | .wgXmit family addr payload opts => socketCallOnObserved SENDER_FD do
    -- W9: the sender's `sendto` routes on the fixture's tables
    -- (`World.route4/6`): into wg0 by the default route the guest adds after
    -- a successful wg_up (and removes with a down, a deletion or
    -- `wg_delroute`), else `-ENETUNREACH`; a local destination never
    -- reaches wg0
    match ← liftPrefix (routeLookup family 0 addr) with
    | .error err => return err
    | .ok r => if r.dev != WG0_IFINDEX then liftPrefix (unsupported "a transmit to a local address (not into wg0)")
    -- W4: an MTU change below the family's floor took its routes down with
    -- its IP device, and the fixture re-adds them only at the next wg_up
    if let some d := (← liftPrefix getK).wg then
      if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
        liftPrefix (unsupported "a transmit after an MTU change took the family's routes into wg0 down")
    -- udp_sendmsg returns the datagram's length once the device took it
    liftPrefix Env.fixtureSend
    match ← liftPrefix (Env.xmitPackets family addr payload opts) with
    | .error e => return e   -- refused by the sender's IP layer before any output
    | .ok (pkts, mtu) =>
      liftPrefix (Env.xmitMulticastLoop family addr)
      let ret ← liftPrefix (wgXmit family addr pkts mtu)
      return if ret == 0 then payload.length else ret
  | .wgSetMtu mtu => socketCallOnObserved SENDER_FD (liftPrefix (Env.setMtu mtu))
  | .wgInject family port message tos ll dest => socketCallOnObserved SENDER_FD (liftPrefix (Env.inject family port message tos ll dest))
  | .wgDeladdr family => rtnetlinkRequestObserved (liftPrefix (Env.wgDeladdr family))
  | .wgDelroute family => rtnetlinkRequestObserved (liftPrefix (Env.wgDelroute family))
  | .wgFlood count port family messages => liftPrefix (Env.flood count port family messages)
  -- W7: the io_uring submission's descriptor plumbing (the ring's fdget, each
  -- send's fget of the sender) is the fixture's, as the flood's is: not modeled
  | .wgBatch items _ => liftPrefix (Env.batch items)
  | .wgObserve => do
    -- the fixture's observation happens whether or not the listener is still
    -- open (W8: after wg_netns_close the `recvfrom(4)` is -EBADF and the
    -- datagrams null, the sender's inbox and the stats are read as always)
    let (ret, observed) ← liftPrefix Env.observe
    liftPrefix (modify fun w => { w with extraOut := ["datagrams", "replies", "stats"].map fun k => (k, observed.getObjValD k) })
    socketCallOnObserved LISTEN4_FD (pure ret)
  | .wgAdvance ticks => do
    -- `ioctl(3, KCOV_LEANUX_TIME_ADVANCE, &ticks)`: `CLASS(fd, f)(fd)`
    -- (fs/ioctl.c), then the LEANUX case of `kcov_ioctl` (a cut point but
    -- for its kind-304 record)
    let f ← liftPrefix (fdget KCOV_FD)
    if f.file.isNone then liftPrefix (unsupported "wg_advance after the trace closed the KCOV descriptor")
    let ret ← liftPrefix (Env.advance ticks)
    liftPrefix (fdput f)
    return ret
  | .wgCreate => rtnetlinkRequestObserved (liftPrefix wgCreate)
  | .wgDown => socketCallOnObserved SENDER_FD (liftPrefix Env.wgDown)
  | .wgDelete => rtnetlinkRequestObserved envWgDeleteObserved
  | .wgNetnsClose => netnsCloseObserved
  | .seccompInstall via flags filter len bad mode => liftPrefix (Seccomp.sysSeccompInstall via flags filter len bad mode)
  | .seccompProbe nr args .self _ => liftPrefix (Seccomp.sysSeccompProbeSelf nr args)
  | .seccompProbe nr args .child strict => liftPrefix (Seccomp.sysSeccompProbeChild nr args strict)
  | .seccompPrctl cmd args => liftPrefix (Seccomp.sysSeccompPrctl cmd args)
  | .seccompCapdrop => liftPrefix (Seccomp.sysSeccompCapdrop)
  | .seccompQuery cmd action flags => liftPrefix (Seccomp.sysSeccompQuery cmd action flags)

def syscallObserved (call : Syscall) : PrefixM RoutingCompletion Int := do
  liftPrefix (modify fun w => { w with steps := #[], userOut := none, userFds := none, extraOut := [], queuedThisCall := [], fired := #[], netRxSections := 0, netRxSection := 0, emitted := {}, translatedLen := none })
  -- seccomp: the entry path of the operation's own call once a mode is set
  -- (a harness call by design 6.2 rule 1: a cache hit); a probe enters itself
  match syscallNr call with
  | some nr => liftPrefix (Seccomp.enterHarnessCall nr)
  | none =>
    if call.isNet && (← liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  let ret ← dispatchObserved call
  -- harness calls whose entry falls inside the window after the operation's (fixture knowledge)
  for c in Env.windowTailCalls do liftPrefix (Seccomp.enterHarnessCall c)
  liftPrefix taskWorkRun
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
  return ret


macro "routing_syscall_erasure" : tactic => `(tactic|
  repeat' first
    | contradiction
    | with_reducible exact wgSetDeviceObserved_erases _
    | with_reducible exact envWgDeleteObserved_erases
    | with_reducible apply netlinkRequestObserved_erases
    | with_reducible apply rtnetlinkRequestObserved_erases
    | with_reducible apply socketCallOnObserved_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem dispatchObserved_erases (call : Syscall) : ErasesPrefix (dispatchObserved call) (dispatch call) := by
  cases call <;> unfold dispatchObserved dispatch
  all_goals routing_syscall_erasure

macro "routing_dispatch_preservation" initial:ident shape:ident : tactic => `(tactic|
  repeat' first
    | contradiction
    | with_reducible apply netlinkRequestObserved_global $initial
    | with_reducible apply rtnetlinkRequestObserved_global $initial
    | with_reducible apply socketCallOnObserved_global $initial
    | with_reducible exact wgSetDeviceObserved_global $initial _ (by simpa only [SyscallAddressShape] using $shape)
    | with_reducible exact envWgDeleteObserved_global $initial
    | with_reducible exact wgCreate_global_completion $initial
    | with_reducible exact global_completion_lift $initial _ (wgGetDevice_routing _)
    | with_reducible exact global_completion_lift $initial _ (netlinkDumpStart_routing _ _)
    | with_reducible exact global_completion_lift $initial _ (netlinkRecvmsg_routing _)
    | with_reducible exact global_completion_lift $initial _ (wgXmit_routing _ _ _ _)
    | with_reducible exact global_completion_lift $initial _ (envWgUp_routing)
    | with_reducible exact global_completion_lift $initial _ (envWgDown_routing)
    | with_reducible exact global_completion_lift $initial _ (inject_routing _ _ _ _ _ _)
    | with_reducible exact global_completion_lift $initial _ (flood_routing _ _ _ _)
    | with_reducible exact global_completion_lift $initial _ (batch_routing _)
    | with_reducible exact global_completion_lift $initial _ (observe_routing)
    | with_reducible exact global_completion_lift $initial _ (runSendWorkers_routing)
    | with_reducible exact global_completion_lift $initial _ (idleTimers_routing)
    | with_reducible exact global_completion_lift $initial _ (afterXmit_routing)
    | with_reducible exact global_completion_lift $initial _ (afterAdvance_routing)
    | with_reducible exact global_completion_lift $initial _ (netnsCleanup_routing)
    | with_reducible exact global_completion_same $initial _ (envSetMtu_routing _)
    | with_reducible exact global_completion_same $initial _ (wgDeladdr_routing _)
    | with_reducible exact global_completion_same $initial _ (wgDelroute_routing _)
    | with_reducible exact global_completion_same $initial _ (advance_routing _)
    | with_reducible exact global_completion_same $initial _ (xmitMulticastLoop_routing _ _)
    | with_reducible exact global_completion_same $initial _ (routeIntoWg0_routing)
    | with_reducible exact lift_wg $initial _ (FSFrames.sysEventfd2_sameWGKernel _ _)
    | with_reducible exact lift_wg $initial _ (FSFrames.sysDup_sameWGKernel _)
    | with_reducible exact lift_wg $initial _ (FSFrames.ksysDup3_sameWGKernel _ _ _)
    | with_reducible exact lift_wg $initial _ (FSFrames.sysClose_sameWGKernel _)
    | with_reducible exact lift_wg $initial _ (FSFrames.ksysRead_sameWGKernel _ _)
    | with_reducible exact lift_wg $initial _ (FSFrames.ksysWrite_sameWGKernel _ _ _)
    | with_reducible exact lift_wg $initial _ (FSFrames.sysPipe2_sameWGKernel _)
    | with_reducible exact lift_wg $initial _ (FSFrames.sysFcntl_sameWGKernel _ _ _)
    | with_reducible exact lift_wg $initial _ (FSFrames.fdget_sameWGKernel _)
    | with_reducible exact lift_wg $initial _ (FSFrames.fdput_sameWGKernel _)
    | with_reducible exact lift_wg $initial _ (EventpollFrames.sysEpollCreate1_sameWGKernel _)
    | with_reducible exact lift_wg $initial _ (EventpollFrames.sysEpollCtl_sameWGKernel _ _ _ _ _)
    | with_reducible exact lift_wg $initial _ (EventpollFrames.sysEpollWait_sameWGKernel _ _ _)
    | with_reducible exact lift_wg $initial _ (SeccompFrames.sysSeccompInstall_sameWGKernel _ _ _ _ _ _)
    | with_reducible exact lift_wg $initial _ (SeccompFrames.sysSeccompProbeSelf_sameWGKernel _ _)
    | with_reducible exact lift_wg $initial _ (SeccompFrames.sysSeccompProbeChild_sameWGKernel _ _ _)
    | with_reducible exact lift_wg $initial _ (SeccompFrames.sysSeccompPrctl_sameWGKernel _ _)
    | with_reducible exact lift_wg $initial _ (SeccompFrames.sysSeccompCapdrop_sameWGKernel)
    | with_reducible exact lift_wg $initial _ (SeccompFrames.sysSeccompQuery_sameWGKernel _ _ _)
    | with_reducible exact lift_kernel $initial _ (getNlSock_sameKernel _)
    | with_reducible exact lift_wg $initial _ (skipCutExactly_sameWGKernel _ _ _)
    | with_reducible exact lift_kernel $initial _ (skipCut_sameKernel _)
    | with_reducible exact lift_kernel $initial _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact lift_kernel $initial _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact lift_kernel $initial _ fixtureSend_sameKernel
    | with_reducible exact lift_wg $initial _ SyscallFrames.netnsClose_sameWGKernel
    | with_reducible exact global_completion_same $initial _ (dumpKernel_routing _ (setNlSock_sameDumpKernel _ _))
    | exact lift_kernel $initial _ (by intro w x v hr; cases hr; rfl)
    | exact lift_kernel $initial _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (state_safe $initial) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem dispatchObserved_global (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : SyscallAddressShape call) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (dispatchObserved call) := by
  cases call <;> unfold dispatchObserved
  all_goals routing_dispatch_preservation initial shape

theorem syscallObserved_erases (call : Syscall) : ErasesPrefix (syscallObserved call) (syscall call) := by
  unfold syscallObserved syscall
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact dispatchObserved_erases _
    | routing_syscall_erasure

theorem syscallObserved_global (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : SyscallAddressShape call) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (syscallObserved call) := by
  unfold syscallObserved
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact dispatchObserved_global initial _ shape
    | with_reducible exact lift_wg initial _ (SeccompFrames.enterHarnessCall_sameWGKernel _)
    | with_reducible exact lift_wg initial _ SignalFrames.getCurrent_sameWGKernel
    | with_reducible exact lift_wg initial _ FSFrames.taskWorkRun_sameWGKernel
    | with_reducible apply PrefixPreserves.forIn _ _ _ (state_safe initial)
    | routing_dispatch_preservation initial shape

end Leanux.Proofs.WG.Configuration
