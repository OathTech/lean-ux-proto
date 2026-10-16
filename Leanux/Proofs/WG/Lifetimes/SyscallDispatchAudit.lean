import Leanux.Proofs.WG.Lifetimes.SyscallWrappersAudit
import Leanux.Proofs.WG.Lifetimes.ConfigurationDevice
import Leanux.Proofs.WG.Lifetimes.DumpAccess

/-! Every original syscall dispatch arm. Access-free FS/seccomp leaves are
lifted using independently proved full WG frames; configuration, dump, packet,
lifecycle and environment calls use their concrete source observers. Scalar
socket cursor records are covered by the dump mask, not a full WG frame. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.Framing.KernelFrames
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

/-- Socket cursor records do not alter allocation identity or saved probe facts. -/
theorem auditLift_dump (a : M α) (ha : SameDumpKernel a) :
    PrefixPreserves AuditInv AuditSafe (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  exact ⟨allocationDumpStable _ _ _ (ha w x v hr) hi.1, hi.2⟩

def dispatchAudit : Syscall → AuditM Int
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
  | .wgSet attrs => netlinkRequestAudit (auditFocus (wgSetDevicePrefix attrs))
  | .wgGet device => netlinkRequestAudit do
    match ← auditFocus (wgGetDevicePrefix device) with
    | .error e => return e
    | .ok device =>
      liftPrefix (modify fun w => { w with extraOut := [("device", device)] })
      return 0
  -- W2 (4.2): one system call each on the stepped socket, the netlink
  -- core's chunk allocations below the cut as in `netlinkRequestAudit`. The
  -- stepped operations that run no WireGuard code are outside the domain
  -- [AGENT, coordinator 2026-10-12: the WireGuard boundary, the af_netlink.c
  -- loop unanchored]: `-EAGAIN` (nothing queued), and a receive that pops
  -- only `NLMSG_DONE` or an acknowledgement (the dump call that produced
  -- it ran in the previous operation).
  | .wgGetStart device => socketCallOnAudit DUMP_FD do
    liftPrefix (skipCut allocCuts)
    -- netlink_autobind (af_netlink.c:803-830) on the socket's first sendmsg:
    -- its port id, the process's, is the fixture socket's, so the collision
    -- draws once (:820); the port id reaches no modeled path (a cut)
    let sock ← liftPrefix (WG.getNlSock DUMP_FD)
    if !sock.bound then
      liftPrefix (skipCutExactly .netlinkAutobindPort 1 allocCuts)
      liftPrefix (WG.setNlSock DUMP_FD { sock with bound := true })
    auditFocus (netlinkDumpStartPrefix DUMP_FD device)
    liftPrefix (skipCut allocCuts)
    return 0
  | .wgGetRecv => socketCallOnAudit DUMP_FD do
    liftPrefix (skipCut allocCuts)
    let some messages ← auditFocus (netlinkRecvmsgPrefix DUMP_FD)
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
  | .wgUp => socketCallOnAudit SENDER_FD envWgUpAudit
  | .wgXmit family addr payload opts => socketCallOnAudit SENDER_FD do
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
      xmitMulticastLoopAudit family addr
      let ret ← auditFocus (wgXmitPrefix family addr pkts mtu)
      return if ret == 0 then payload.length else ret
  | .wgSetMtu mtu => socketCallOnAudit SENDER_FD (setMtuAudit mtu)
  | .wgInject family port message tos ll dest => socketCallOnAudit SENDER_FD (injectAudit family port message tos ll dest)
  | .wgDeladdr family => rtnetlinkRequestAudit (wgDeladdrAudit family)
  | .wgDelroute family => rtnetlinkRequestAudit (wgDelrouteAudit family)
  | .wgFlood count port family messages => floodAudit count port family messages
  -- W7: the io_uring submission's descriptor plumbing (the ring's fdget, each
  -- send's fget of the sender) is the fixture's, as the flood's is: not modeled
  | .wgBatch items _ => batchAudit items
  | .wgObserve => do
    -- the fixture's observation happens whether or not the listener is still
    -- open (W8: after wg_netns_close the `recvfrom(4)` is -EBADF and the
    -- datagrams null, the sender's inbox and the stats are read as always)
    let (ret, observed) ← observeAudit
    liftPrefix (modify fun w => { w with extraOut := ["datagrams", "replies", "stats"].map fun k => (k, observed.getObjValD k) })
    socketCallOnAudit LISTEN4_FD (pure ret)
  | .wgAdvance ticks => do
    -- `ioctl(3, KCOV_LEANUX_TIME_ADVANCE, &ticks)`: `CLASS(fd, f)(fd)`
    -- (fs/ioctl.c), then the LEANUX case of `kcov_ioctl` (a cut point but
    -- for its kind-304 record)
    let f ← liftPrefix (fdget KCOV_FD)
    if f.file.isNone then liftPrefix (unsupported "wg_advance after the trace closed the KCOV descriptor")
    let ret ← advanceAudit ticks
    liftPrefix (fdput f)
    return ret
  | .wgCreate => rtnetlinkRequestAudit (auditFocus wgCreatePrefix)
  | .wgDown => socketCallOnAudit SENDER_FD envWgDownAudit
  | .wgDelete => rtnetlinkRequestAudit envWgDeleteAudit
  | .wgNetnsClose => netnsCloseAudit
  | .seccompInstall via flags filter len bad mode => liftPrefix (Seccomp.sysSeccompInstall via flags filter len bad mode)
  | .seccompProbe nr args .self _ => liftPrefix (Seccomp.sysSeccompProbeSelf nr args)
  | .seccompProbe nr args .child strict => liftPrefix (Seccomp.sysSeccompProbeChild nr args strict)
  | .seccompPrctl cmd args => liftPrefix (Seccomp.sysSeccompPrctl cmd args)
  | .seccompCapdrop => liftPrefix (Seccomp.sysSeccompCapdrop)
  | .seccompQuery cmd action flags => liftPrefix (Seccomp.sysSeccompQuery cmd action flags)

macro "syscall_dispatch_erasure" : tactic => `(tactic|
  repeat' first
    | contradiction
    | with_reducible apply netlinkRequestAudit_erases
    | with_reducible apply rtnetlinkRequestAudit_erases
    | with_reducible apply socketCallOnAudit_erases
    | with_reducible exact auditFocus_erases (wgSetDevicePrefix_erases _)
    | with_reducible exact auditFocus_erases (wgGetDevicePrefix_erases _)
    | with_reducible exact auditFocus_erases (netlinkDumpStartPrefix_erases _ _)
    | with_reducible exact auditFocus_erases (netlinkRecvmsgPrefix_erases _)
    | with_reducible exact auditFocus_erases (wgXmitPrefix_erases _ _ _ _)
    | with_reducible exact auditFocus_erases wgCreatePrefix_erases
    | with_reducible exact envWgUpAudit_erases
    | with_reducible exact setMtuAudit_erases _
    | with_reducible exact injectAudit_erases _ _ _ _ _ _
    | with_reducible exact wgDeladdrAudit_erases _
    | with_reducible exact wgDelrouteAudit_erases _
    | with_reducible exact floodAudit_erases _ _ _ _
    | with_reducible exact batchAudit_erases _
    | with_reducible exact observeAudit_erases
    | with_reducible exact advanceAudit_erases _
    | with_reducible exact xmitMulticastLoopAudit_erases _ _
    | with_reducible exact envWgDownAudit_erases
    | with_reducible exact envWgDeleteAudit_erases
    | with_reducible exact netnsCloseAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

macro "syscall_dispatch_preservation" : tactic => `(tactic|
  repeat' first
    | contradiction
    | with_reducible apply netlinkRequestAudit_preserves
    | with_reducible apply rtnetlinkRequestAudit_preserves
    | with_reducible apply socketCallOnAudit_preserves
    | exact auditFocus_preserves (ConfigurationCall.allocation (.device _))
    | exact auditFocus_preserves (NetlinkDumpCall.allocation (.device _))
    | exact auditFocus_preserves (NetlinkDumpCall.allocation (.start _ _))
    | exact auditFocus_preserves (NetlinkDumpCall.allocation (.receive _))
    | with_reducible exact auditFocus_preserves (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible exact auditFocus_preserves wgCreatePrefix_allocation
    | with_reducible exact envWgUpAudit_preserves
    | with_reducible exact setMtuAudit_preserves _
    | with_reducible exact injectAudit_preserves _ _ _ _ _ _
    | with_reducible exact wgDeladdrAudit_preserves _
    | with_reducible exact wgDelrouteAudit_preserves _
    | with_reducible exact floodAudit_preserves _ _ _ _
    | with_reducible exact batchAudit_preserves _
    | with_reducible exact observeAudit_preserves
    | with_reducible exact advanceAudit_preserves _
    | with_reducible exact xmitMulticastLoopAudit_preserves _ _
    | with_reducible exact envWgDownAudit_preserves
    | with_reducible exact envWgDeleteAudit_preserves
    | with_reducible exact netnsCloseAudit_preserves
    | with_reducible exact auditLift_wgKernel _ (FSFrames.sysEventfd2_sameWGKernel _ _)
    | with_reducible exact auditLift_wgKernel _ (FSFrames.sysDup_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ (FSFrames.ksysDup3_sameWGKernel _ _ _)
    | with_reducible exact auditLift_wgKernel _ (FSFrames.sysClose_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ (FSFrames.ksysRead_sameWGKernel _ _)
    | with_reducible exact auditLift_wgKernel _ (FSFrames.ksysWrite_sameWGKernel _ _ _)
    | with_reducible exact auditLift_wgKernel _ (FSFrames.sysPipe2_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ (FSFrames.sysFcntl_sameWGKernel _ _ _)
    | with_reducible exact auditLift_wgKernel _ (FSFrames.fdget_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ (FSFrames.fdput_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ (EventpollFrames.sysEpollCreate1_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ (EventpollFrames.sysEpollCtl_sameWGKernel _ _ _ _ _)
    | with_reducible exact auditLift_wgKernel _ (EventpollFrames.sysEpollWait_sameWGKernel _ _ _)
    | with_reducible exact auditLift_wgKernel _ (SeccompFrames.sysSeccompInstall_sameWGKernel _ _ _ _ _ _)
    | with_reducible exact auditLift_wgKernel _ (SeccompFrames.sysSeccompProbeSelf_sameWGKernel _ _)
    | with_reducible exact auditLift_wgKernel _ (SeccompFrames.sysSeccompProbeChild_sameWGKernel _ _ _)
    | with_reducible exact auditLift_wgKernel _ (SeccompFrames.sysSeccompPrctl_sameWGKernel _ _)
    | with_reducible exact auditLift_wgKernel _ (SeccompFrames.sysSeccompCapdrop_sameWGKernel)
    | with_reducible exact auditLift_wgKernel _ (SeccompFrames.sysSeccompQuery_sameWGKernel _ _ _)
    | with_reducible exact auditLift_dump _ (setNlSock_sameDumpKernel _ _)
    | with_reducible exact auditLift_kernel _ (getNlSock_sameKernel _)
    | with_reducible exact auditLift_wgKernel _ (skipCutExactly_sameWGKernel _ _ _)
    | with_reducible exact auditLift_kernel _ (skipCut_sameKernel _)
    | with_reducible exact auditLift_kernel _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ fixtureSend_sameKernel
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem dispatchAudit_erases (call : Syscall) : ErasesPrefix (dispatchAudit call) (dispatch call) := by
  cases call <;> unfold dispatchAudit dispatch
  all_goals syscall_dispatch_erasure

theorem dispatchAudit_preserves (call : Syscall) : PrefixPreserves AuditInv AuditSafe (dispatchAudit call) := by
  cases call <;> unfold dispatchAudit
  all_goals syscall_dispatch_preservation

end Leanux.Proofs.WG.Lifetimes
