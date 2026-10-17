import Leanux.Proofs.WG.Lifetimes.SyscallWrappersAudit
import Leanux.Proofs.WG.Lifetimes.ConfigurationDevice
import Leanux.Proofs.WG.Lifetimes.DumpAccess

/-! Every original syscall dispatch arm. Access-free FS/seccomp leaves are
lifted through the actual component adapters; configuration, dump, packet,
lifecycle and environment calls use their concrete source observers. Scalar
socket cursor records are covered by the dump mask, not a full WG frame. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

/-- Socket cursor records do not alter allocation identity or saved probe facts. -/
theorem auditLift_dump (a : Leanux.M α) (ha : SameView productDumpView a) :
    PrefixPreserves AuditInv AuditSafe (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  have he := (ProjectedAction.iff_run _ _ _).mp ha w x v hr
  exact ⟨allocationDumpStable _ _ _
    (congrArg (fun s : ProductStore43 => s.2.2.2) he) hi.1, hi.2⟩

def dispatchAudit : Syscall → AuditM Int
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
  | .wgSet attrs => netlinkRequestAudit (auditFocus (liftWGObserver (wgSetDevicePrefix attrs)))
  | .wgGet device => netlinkRequestAudit do
    match ← auditFocus (liftWGObserver (wgGetDevicePrefix device)) with
    | .error e => return e
    | .ok device =>
      liftPrefix (modifyAmbient fun w => { w with extraOut := [("device", device)] })
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
    let sock ← liftPrefix (liftWG (WG.getNlSock DUMP_FD))
    if !sock.bound then
      liftPrefix (skipCutExactly .netlinkAutobindPort 1 allocCuts)
      liftPrefix (liftWG (WG.setNlSock DUMP_FD { sock with bound := true }))
    auditFocus (liftWGObserver (netlinkDumpStartPrefix DUMP_FD device))
    liftPrefix (skipCut allocCuts)
    return 0
  | .wgGetRecv => socketCallOnAudit DUMP_FD do
    liftPrefix (skipCut allocCuts)
    let some messages ← auditFocus (liftWGObserver (netlinkRecvmsgPrefix DUMP_FD))
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
  | .wgUp => socketCallOnAudit SENDER_FD envWgUpAudit
  | .wgXmit family addr payload opts => socketCallOnAudit SENDER_FD do
    -- W9: the sender's `sendto` routes on the fixture's tables
    -- (`World.route4/6`): into wg0 by the default route the guest adds after
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
      xmitMulticastLoopAudit family addr
      if family == 4 then liftPrefix (Net.neighbourClassify WG0_IFINDEX)
      let ret ← auditFocus (liftWGObserver (wgXmitPrefix family addr pkts mtu))
      return if ret == 0 then payload.length else ret
  | .wgSetMtu mtu => socketCallOnAudit SENDER_FD (setMtuAudit mtu)
  | .wgInject family port message tos ll dest => socketCallOnAudit SENDER_FD (injectAudit family port message tos ll dest)
  | .wgDeladdr family => rtnetlinkRequestAudit (wgDeladdrAudit family)
  | .wgDelroute family named dst plen oif typeCode metric =>
    rtnetlinkRequestAudit (liftPrefix (Env.wgDelroute family named dst plen oif typeCode metric))
  | .wgAddroute dst plen oif typeCode metric mtu nlflags =>
    rtnetlinkRequestAudit (liftPrefix (Env.wgAddroute dst plen oif typeCode metric mtu nlflags))
  | .wgAddaddr addr plen => rtnetlinkRequestAudit (liftPrefix (Env.wgAddaddr addr plen))
  | .wgFlood count port family messages => floodAudit count port family messages
  -- W7: the io_uring submission's descriptor plumbing (the ring's fdget, each
  -- send's fget of the sender) is the fixture's, as the flood's is: not modeled
  | .wgBatch items _ => batchAudit items
  | .wgObserve => do
    -- the fixture's observation happens whether or not the listener is still
    -- open (W8: after wg_netns_close the `recvfrom(4)` is -EBADF and the
    -- datagrams null, the sender's inbox and the stats are read as always)
    let (ret, observed) ← observeAudit
    liftPrefix (modifyAmbient fun w => { w with extraOut := ["datagrams", "replies", "stats"].map fun k => (k, observed.getObjValD k) })
    socketCallOnAudit LISTEN4_FD (pure ret)
  | .wgAdvance ticks => do
    -- `ioctl(3, KCOV_LEANUX_TIME_ADVANCE, &ticks)`: `CLASS(fd, f)(fd)`
    -- (fs/ioctl.c), then the LEANUX case of `kcov_ioctl` (a cut point but
    -- for its kind-304 record)
    let f ← liftPrefix (liftFS (fdget KCOV_FD))
    if f.file.isNone then liftPrefix (unsupported "wg_advance after the trace closed the KCOV descriptor")
    let ret ← advanceAudit ticks
    liftPrefix (liftFS (fdput f))
    return ret
  | .wgCreate => rtnetlinkRequestAudit (auditFocus (liftWGObserver wgCreatePrefix))
  | .wgDown => socketCallOnAudit SENDER_FD envWgDownAudit
  | .wgDelete => rtnetlinkRequestAudit envWgDeleteAudit
  | .wgNetnsClose => netnsCloseAudit
  | .seccompInstall via flags filter len bad mode => liftPrefix (liftSeccomp (Seccomp.sysSeccompInstall via flags filter len bad mode))
  | .seccompProbe nr args .self _ => liftPrefix (liftSeccomp (Seccomp.sysSeccompProbeSelf nr args))
  | .seccompProbe nr args .child strict => liftPrefix (liftSeccomp (Seccomp.sysSeccompProbeChild nr args strict))
  | .seccompPrctl cmd args => liftPrefix (liftSeccomp (Seccomp.sysSeccompPrctl cmd args))
  | .seccompCapdrop => liftPrefix (liftSeccomp (Seccomp.sysSeccompCapdrop))
  | .seccompQuery cmd action flags => liftPrefix (liftSeccomp (Seccomp.sysSeccompQuery cmd action flags))

macro "syscall_dispatch_erasure" : tactic => `(tactic|
  repeat' first
    | (maintenance_head netlinkRequestAudit; apply netlinkRequestAudit_erases)
    | (maintenance_head rtnetlinkRequestAudit; apply rtnetlinkRequestAudit_erases)
    | (maintenance_head socketCallOnAudit; apply socketCallOnAudit_erases)
    | (maintenance_head envWgUpAudit; exact envWgUpAudit_erases)
    | (maintenance_head setMtuAudit; exact setMtuAudit_erases _)
    | (maintenance_head injectAudit; exact injectAudit_erases _ _ _ _ _ _)
    | (maintenance_head wgDeladdrAudit; exact wgDeladdrAudit_erases _)
    | (maintenance_head floodAudit; exact floodAudit_erases _ _ _ _)
    | (maintenance_head batchAudit; exact batchAudit_erases _)
    | (maintenance_head observeAudit; exact observeAudit_erases)
    | (maintenance_head advanceAudit; exact advanceAudit_erases _)
    | (maintenance_head xmitMulticastLoopAudit; exact xmitMulticastLoopAudit_erases _ _)
    | (maintenance_head envWgDownAudit; exact envWgDownAudit_erases)
    | (maintenance_head envWgDeleteAudit; exact envWgDeleteAudit_erases)
    | (maintenance_head netnsCloseAudit; exact netnsCloseAudit_erases)
    | (timer_audit_focus_head wgSetDevicePrefix; exact auditFocus_erases (liftWGObserver_erases (wgSetDevicePrefix_erases _)))
    | (timer_audit_focus_head wgGetDevicePrefix; exact auditFocus_erases (liftWGObserver_erases (wgGetDevicePrefix_erases _)))
    | (timer_audit_focus_head netlinkDumpStartPrefix; exact auditFocus_erases (liftWGObserver_erases (netlinkDumpStartPrefix_erases _ _)))
    | (timer_audit_focus_head netlinkRecvmsgPrefix; exact auditFocus_erases (liftWGObserver_erases (netlinkRecvmsgPrefix_erases _)))
    | (timer_audit_focus_head wgXmitPrefix; exact auditFocus_erases (liftWGObserver_erases (wgXmitPrefix_erases _ _ _ _)))
    | (timer_audit_focus_head wgCreatePrefix; exact auditFocus_erases (liftWGObserver_erases (wgCreatePrefix_erases)))
    | control_audit_erases)

/-- Only a genuine routing action is handed to the routing adapter. -/
elab "syscall_routing_head" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``SameView && !target.getAppArgs.isEmpty do
    Lean.throwError "not a view contract"
  let rec name (fuel : Nat) (e : Lean.Expr) : Lean.Name :=
    match fuel with
    | 0 => .anonymous
    | n+1 =>
      let e := e.consumeMData
      match e.getAppFn with
      | .const actual _ =>
        if actual == ``liftM || actual == ``MonadLift.monadLift || actual == ``MonadLiftT.monadLift then
          if e.getAppArgs.isEmpty then .anonymous else name n e.getAppArgs.back!
        else actual
      | _ => .anonymous
  let actual := name 4 target.getAppArgs.back!
  unless actual == ``getRouting || actual == ``modifyRouting ||
      actual.toString.startsWith "Leanux.Net." do Lean.throwError "not routing"

/-- Compose the actual product control bodies without a per-routing-leaf frame. -/
macro "syscall_routing_store" : tactic => `(tactic|
  repeat' first
    | (dump_kernel_head getWG; intro initial; exact productGetWG_spec (fun s => s.2.2.2 = initial))
    | (syscall_routing_head; intro initial; exact productRouting_spec _ (fun s => s.2.2.2 = initial))
    | (dump_kernel_head unsupported; intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | (dump_kernel_head invariant; intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | (dump_kernel_head Pure.pure; exact SameView.pure _ _)
    | (dump_kernel_head Bind.bind; apply SameView.bind)
    | (dump_kernel_head ForIn.forIn; apply DumpComposition.forIn_sameView)
    | dump_kernel_intro
    | dump_kernel_join_let
    | dump_kernel_join_use
    | dump_dump_kernel_head_reduce
    | dump_dump_kernel_head_match
    | (with_reducible split))

macro "syscall_dispatch_preservation" : tactic => `(tactic|
  repeat' first
    | (audit_contract_head netlinkRequestAudit; apply netlinkRequestAudit_preserves)
    | (audit_contract_head rtnetlinkRequestAudit; apply rtnetlinkRequestAudit_preserves)
    | (audit_contract_head socketCallOnAudit; apply socketCallOnAudit_preserves)
    | (audit_contract_head envWgUpAudit; exact envWgUpAudit_preserves)
    | (audit_contract_head setMtuAudit; exact setMtuAudit_preserves _)
    | (audit_contract_head injectAudit; exact injectAudit_preserves _ _ _ _ _ _)
    | (audit_contract_head wgDeladdrAudit; exact wgDeladdrAudit_preserves _)
    | (audit_contract_head floodAudit; exact floodAudit_preserves _ _ _ _)
    | (audit_contract_head batchAudit; exact batchAudit_preserves _)
    | (audit_contract_head observeAudit; exact observeAudit_preserves)
    | (audit_contract_head advanceAudit; exact advanceAudit_preserves _)
    | (audit_contract_head xmitMulticastLoopAudit; exact xmitMulticastLoopAudit_preserves _ _)
    | (audit_contract_head envWgDownAudit; exact envWgDownAudit_preserves)
    | (audit_contract_head envWgDeleteAudit; exact envWgDeleteAudit_preserves)
    | (audit_contract_head netnsCloseAudit; exact netnsCloseAudit_preserves)
    | (timer_audit_focus_head wgSetDevicePrefix; exact auditFocus_preserves ((ConfigurationCall.allocation (.device _)).liftWGObserver))
    | (timer_audit_focus_head wgGetDevicePrefix; exact auditFocus_preserves ((NetlinkDumpCall.allocation (.device _)).liftWGObserver))
    | (timer_audit_focus_head netlinkDumpStartPrefix; exact auditFocus_preserves ((NetlinkDumpCall.allocation (.start _ _)).liftWGObserver))
    | (timer_audit_focus_head netlinkRecvmsgPrefix; exact auditFocus_preserves ((NetlinkDumpCall.allocation (.receive _)).liftWGObserver))
    | (timer_audit_focus_head wgXmitPrefix; exact auditFocus_preserves ((wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _).liftWGObserver))
    | (timer_audit_focus_head wgCreatePrefix; exact auditFocus_preserves (wgCreatePrefix_allocation.liftWGObserver))
    | (audit_contract_head Env.wgDelroute; apply auditLift_store; unfold Env.wgDelroute; syscall_routing_store)
    | (audit_contract_head Env.wgAddroute; apply auditLift_store; unfold Env.wgAddroute; syscall_routing_store)
    | (audit_contract_head Env.wgAddaddr; apply auditLift_store; unfold Env.wgAddaddr; syscall_routing_store)
    | (audit_contract_head liftWG; first
        | exact auditLift_dump _ (sameView_liftWG productDumpView dumpView _ (setNlSock_sameDump _ _)
            (fun _ _ _ hi => by change (_, _, _, _) = (_, _, _, _); rw [hi]))
        | exact auditLift_store _ (sameView_liftWG (fun w => wgStoreView w.wg) id _ (getNlSock_sameWGWorld _)
            (fun _ _ _ hi => congrArg wgStoreView hi)))
    | (audit_contract_head Env.xmitPackets; exact auditLift_store _ ((xmitPackets_sameKernel _ _ _ _).of_factor
        (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl)))
    | (audit_contract_head Env.fixtureSend; unfold Env.fixtureSend)
    | (control_audit_routing; exact auditLift_store _ (by intro initial; exact productRouting_spec _ (fun s => s.2.2.2 = initial)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _)
    | syscall_audit_component
    | control_audit_preserves)

theorem dispatchAudit_erases (call : Syscall) : ErasesPrefix (dispatchAudit call) (dispatch call) := by
  cases call
  case seccompProbe nr args target strict =>
    cases target <;> exact erasesPrefix_lift _
  all_goals unfold dispatchAudit dispatch
  all_goals syscall_dispatch_erasure

theorem dispatchAudit_preserves (call : Syscall) : PrefixPreserves AuditInv AuditSafe (dispatchAudit call) := by
  apply PrefixEnsures.preserves
  cases call <;> unfold dispatchAudit
  all_goals syscall_dispatch_preservation
  all_goals exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _

end Leanux.Proofs.WG.Lifetimes
