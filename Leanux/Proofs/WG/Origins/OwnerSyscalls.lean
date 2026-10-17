import Leanux.Proofs.WG.Origins.OwnerRemaining

/-! The concrete original dispatcher and its return-to-user continuations.
Foreign subsystem actions use their typed adapters; native WG paths retain
the eventful observers, failed prefixes and ordinary errno returns. -/
namespace Leanux.Proofs.WG.OwnerSyscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration OwnerControlCalls

private theorem safe (h : List RxHistory.Event) (w : World) (hi : OwnerChecks.Inv h w) :
    OwnerChecks.Safe h := hi.safe

private theorem socket (fd : Nat) (body : AuditM Int) (hb : Audited body) :
    Audited (socketCallOnAudit fd body) := by
  refine ⟨?_,audit_socket fd body hb.1 hb.2⟩
  rw [socketCallOnAudit_factor]
  exact socketCallOnWith_appends fd hb.1

private theorem netlink (body : AuditM Int) (hb : Audited body) :
    Audited (netlinkRequestAudit body) := by
  refine ⟨?_,audit_netlink body hb⟩
  rw [netlinkRequestAudit_factor]
  exact netlinkRequestWith_appends hb.1

private theorem rtnetlink (body : AuditM Int) (hb : Audited body) :
    Audited (rtnetlinkRequestAudit body) := by
  refine ⟨?_,?_⟩
  · rw [rtnetlinkRequestAudit_factor]
    exact rtnetlinkRequestWith_appends hb.1
  · rw [rtnetlinkRequestAudit_factor]
    rw [← rtnetlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) body hb.1]
    exact OwnerControlCalls.rtnetlinkRequest _ hb.2

private theorem multicast (family addr : Nat) : Audited (xmitMulticastLoopAudit family addr) :=
  ⟨((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.multicast) family addr).1,
    OwnerRemaining.remaining (.multicast family addr)⟩

private theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Audited (auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  ⟨Appends.focus _ _ _,
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerTraffic.«0».Leanux.Proofs.WG.OwnerTraffic.transmit) family addr packets mtu⟩

private theorem dump (call : NetlinkDumpCall) : Audited (auditFocus (liftWGObserver call.observed)) :=
  ⟨Appends.focus _ _ _,dump_checked call⟩

macro "owner_dispatch_audit_steps" : tactic => `(tactic| first
  | (owner_control_audit_at socketCallOnAudit; apply socket)
  | (owner_control_audit_at netlinkRequestAudit; apply netlink)
  | (owner_control_audit_at rtnetlinkRequestAudit; apply rtnetlink)
  | (owner_control_audit_at wgGetDevicePrefix; exact dump (.device _))
  | (owner_control_audit_at netlinkDumpStartPrefix; exact dump (.start _ _))
  | (owner_control_audit_at netlinkRecvmsgPrefix; exact dump (.receive _))
  | (owner_control_audit_at wgXmitPrefix; exact transmit _ _ _ _)
  | (owner_control_audit_at xmitMulticastLoopAudit; exact multicast _ _)
  | (owner_control_audit_at setMtuAudit; exact ⟨Appends.lift _,OwnerControlCalls.mtu _⟩)
  | (owner_control_audit_at wgDeladdrAudit; exact ⟨Appends.lift _,OwnerRemaining.deladdr _⟩)
  | (owner_control_audit_at advanceAudit; exact ⟨Appends.lift _,OwnerDeferred.deferred (.advance _)⟩)
  | (owner_control_audit_at Env.wgDelroute; apply audit_lift; apply lift_wgStore
     unfold Env.wgDelroute; syscall_routing_store)
  | (owner_control_audit_at Env.wgAddroute; apply audit_lift; apply lift_wgStore
     unfold Env.wgAddroute; syscall_routing_store)
  | (owner_control_audit_at Env.wgAddaddr; apply audit_lift; apply lift_wgStore
     unfold Env.wgAddaddr; syscall_routing_store)
  | (owner_control_audit_at getNlSock
     exact audit_dump_lift _ ((getNlSock_sameWGWorld _).factor dumpView))
  | (owner_control_audit_at setNlSock; exact audit_dump_lift _ (setNlSock_sameDump _ _))
  | (owner_control_audit_at Env.xmitPackets
     exact audit_lift _ (lift_store _ (xmitPackets_sameKernel _ _ _ _)))
  | (owner_control_audit_at Env.fixtureSend; exact audit_lift _ (lift_ambient _))
  | (owner_control_audit_at liftFS; exact audit_lift _ (lift_fs _))
  | (owner_control_audit_at liftSeccomp; exact audit_lift _ (lift_seccomp _))
  | (owner_control_audit_at unsupported; exact audit_lift _ (lift_ambient _))
  | (owner_control_audit_at skipCut; exact audit_lift _ (lift_ambient _))
  | (owner_control_audit_at skipCutExactly; exact audit_lift _ (lift_ambient _))
  | (owner_control_audit_at modifyAmbient; exact audit_lift _ (lift_ambient _))
  | owner_control_audit_steps)

private theorem get (device : DeviceRef) : Audited (dispatchAudit (.wgGet device)) := by
  simp only [dispatchAudit]
  repeat' owner_dispatch_audit_steps

private theorem getStart (device : DeviceRef) : Audited (dispatchAudit (.wgGetStart device)) := by
  simp only [dispatchAudit]
  repeat' owner_dispatch_audit_steps

private theorem getRecv : Audited (dispatchAudit .wgGetRecv) := by
  simp only [dispatchAudit]
  repeat' owner_dispatch_audit_steps

private theorem xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Audited (dispatchAudit (.wgXmit family addr payload opts)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' owner_dispatch_audit_steps

private theorem delroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    Audited (dispatchAudit (.wgDelroute family named dst plen oif typeCode metric)) := by
  simp only [dispatchAudit]
  repeat' owner_dispatch_audit_steps

private theorem addroute (dst plen oif typeCode metric mtu nlflags : Nat) :
    Audited (dispatchAudit (.wgAddroute dst plen oif typeCode metric mtu nlflags)) := by
  simp only [dispatchAudit]
  repeat' owner_dispatch_audit_steps

private theorem addaddr (addr plen : Nat) : Audited (dispatchAudit (.wgAddaddr addr plen)) := by
  simp only [dispatchAudit]
  repeat' owner_dispatch_audit_steps

private theorem advance (ticks : Nat) : Audited (dispatchAudit (.wgAdvance ticks)) := by
  simp only [dispatchAudit]
  repeat' owner_dispatch_audit_steps

/-- All actual source arms, including both seccomp probe targets. -/
theorem dispatch (call : Syscall) : OwnerChecks.Preserves (RxHistory.syscallDispatch call) := by
  cases call with
  | eventfd2 count flags => exact (audit_lift _ (lift_fs _)).2
  | dup fd => exact (audit_lift _ (lift_fs _)).2
  | dup3 old new flags => exact (audit_lift _ (lift_fs _)).2
  | close fd => exact (audit_lift _ (lift_fs _)).2
  | read fd count => exact (audit_lift _ (lift_fs _)).2
  | write fd count buf => exact (audit_lift _ (lift_fs _)).2
  | pipe2 flags => exact (audit_lift _ (lift_fs _)).2
  | fcntl fd cmd arg => exact (audit_lift _ (lift_fs _)).2
  | epollCreate1 flags => exact (audit_lift _ (lift_fs _)).2
  | epollCtl epfd op fd events data => exact (audit_lift _ (lift_fs _)).2
  | epollWait epfd maxevents timeout => exact (audit_lift _ (lift_fs _)).2
  | wgSet attrs => exact dispatchSet attrs
  | wgGet device => exact (get device).2
  | wgGetStart device => exact (getStart device).2
  | wgGetRecv => exact getRecv.2
  | wgUp => exact dispatchUp
  | wgXmit family addr payload opts => exact (xmit family addr payload opts).2
  | wgSetMtu mtu => exact (socket _ _ ⟨Appends.lift _,OwnerControlCalls.mtu mtu⟩).2
  | wgInject family port message tos ll dest => exact OwnerControlCalls.socketCallOn _ _ (OwnerTraffic.inject family port message tos ll dest)
  | wgDeladdr family => exact (rtnetlink _ ⟨Appends.lift _,OwnerRemaining.deladdr family⟩).2
  | wgDelroute family named dst plen oif typeCode metric => exact (delroute family named dst plen oif typeCode metric).2
  | wgAddroute dst plen oif typeCode metric mtu nlflags => exact (addroute dst plen oif typeCode metric mtu nlflags).2
  | wgAddaddr addr plen => exact (addaddr addr plen).2
  | wgFlood count port family messages => exact OwnerTraffic.flood count port family messages
  | wgBatch items _ => exact OwnerTraffic.batch items
  | wgObserve =>
    change OwnerChecks.Preserves (do
      let (ret, observed) ← RxHistory.observe
      liftPrefix (modifyAmbient fun w => {w with extraOut := ["datagrams","replies","stats"].map fun k => (k,observed.getObjValD k)})
      RxHistory.socketCallOn LISTEN4_FD (pure ret))
    apply OwnerRemaining.observe.bind
    rintro ⟨ret,observed⟩
    dsimp only
    apply PrefixPreserves.bind
    · exact lift_modify _ (fun _ => rfl)
    intro _
    exact OwnerControlCalls.socketCallOn LISTEN4_FD (pure ret) (PrefixPreserves.pure safe ret)
  | wgAdvance ticks => exact (advance ticks).2
  | wgCreate => exact dispatchCreate
  | wgDown => exact dispatchDown
  | wgDelete => exact dispatchDelete
  | wgNetnsClose => exact dispatchNetnsClose
  | seccompInstall via flags filter len bad mode => exact (audit_lift _ (lift_seccomp _)).2
  | seccompProbe nr args target strict => cases target <;> exact (audit_lift _ (lift_seccomp _)).2
  | seccompPrctl cmd args => exact (audit_lift _ (lift_seccomp _)).2
  | seccompCapdrop => exact (audit_lift _ (lift_seccomp _)).2
  | seccompQuery cmd action flags => exact (audit_lift _ (lift_seccomp _)).2

/-- Source-designated suffixes run after every normal errno return; an actual
Stop retains only the reached prefix. No arbitrary callback premise remains. -/
theorem syscall (call : Syscall) : OwnerChecks.Preserves (RxHistory.syscall call) := by
  rw [syscallRx_factor]
  exact syscallWith_preserves call _ _ _ _ _ _ _ (dispatch call)
    OwnerDeferred.runSendWorkers OwnerDeferred.idleTimers OwnerRemaining.route
    OwnerDeferred.afterXmit OwnerDeferred.afterAdvance OwnerControlCalls.netnsCleanup

end Leanux.Proofs.WG.OwnerSyscalls
