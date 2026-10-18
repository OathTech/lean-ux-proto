import Leanux.Proofs.WG.Packets.PublicationRemaining
import Leanux.Proofs.WG.Packets.PublicationDump
import Leanux.Proofs.WG.Packets.PublicationDeviceConfiguration

/-! The concrete original dispatcher and its return-to-user continuations.
Foreign subsystem actions use their typed adapters; native WG paths retain
the eventful observers, failed prefixes and ordinary errno returns. -/
namespace Leanux.Proofs.WG.PublicationSyscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration PublicationOuter

private theorem safe (h : List RxHistory.Event) (w : World) (hi : PublicationJoint.Inv h w) :
    PublicationJoint.Safe h := hi.safe

private theorem socket (fd : Nat) (body : AuditM Int) (hb : Audited body) :
    Audited (socketCallOnAudit fd body) := socket_audited fd body hb

private theorem netlink (body : AuditM Int) (hb : Audited body) :
    Audited (netlinkRequestAudit body) := netlink_audited body hb

private theorem rtnetlink (body : AuditM Int) (hb : Audited body) :
    Audited (rtnetlinkRequestAudit body) := rtnetlink_audited body hb

private theorem audit_dump_lift (a : WG.M α) (frame : SameDump a) :
    Audited (liftPrefix (liftWG a)) := by
  refine ⟨Appends.lift _,PublicationJoint.combine _ (OwnerControlCalls.audit_dump_lift a frame).2 ?_⟩
  exact PublicationAudited.source _ _ (erasesPrefix_lift (liftWG a)) (fun history =>
    PublicationPoll.native_product _ _
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationDump.«0».Leanux.Proofs.WG.PublicationFrontier.dump_preserves) a frame history))

/-- The unchanged device observer runs inside both actual netlink transactions. -/
theorem dispatchSet (attrs : DeviceAttrs) :
    PublicationJoint.Preserves (RxHistory.syscallDispatch (.wgSet attrs)) := by
  change PublicationJoint.Preserves (RxHistory.audit (netlinkRequestAudit
    (auditFocus (liftWGObserver (wgSetDevicePrefix attrs)))))
  exact audit_netlink _ ⟨Appends.focus _ _ _,PublicationJoint.wgSetDevice attrs⟩

theorem dispatchCreate : PublicationJoint.Preserves (RxHistory.syscallDispatch .wgCreate) := by
  exact (rtnetlink_audited _ ⟨Appends.focus _ _ _,PublicationControls.create⟩).2

theorem dispatchUp : PublicationJoint.Preserves (RxHistory.syscallDispatch .wgUp) := by
  apply audit_socket SENDER_FD envWgUpAudit
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.up).1 PublicationControls.up

theorem dispatchDown : PublicationJoint.Preserves (RxHistory.syscallDispatch .wgDown) := by
  apply audit_socket SENDER_FD envWgDownAudit
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.down).1 PublicationControls.down

theorem dispatchDelete : PublicationJoint.Preserves (RxHistory.syscallDispatch .wgDelete) := by
  exact (rtnetlink_audited _
    ⟨(pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.delete).1,
      PublicationControls.delete⟩).2

theorem dispatchNetnsClose : PublicationJoint.Preserves (RxHistory.syscallDispatch .wgNetnsClose) := by
  exact (audit_lift _ (lift_wgStore _ SyscallFrames.netnsClose_sameWGStore)).2

private theorem multicast (family addr : Nat) : Audited (xmitMulticastLoopAudit family addr) :=
  ⟨((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.multicast) family addr).1,
    PublicationRemaining.remaining (.multicast family addr)⟩

private theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Audited (auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  ⟨Appends.focus _ _ _,
    (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.transmit) family addr packets mtu⟩

private theorem dump (call : NetlinkDumpCall) : Audited (auditFocus (liftWGObserver call.observed)) :=
  ⟨Appends.focus _ _ _,PublicationJoint.dump_checked call⟩

macro "publication_dispatch_audit_steps" : tactic => `(tactic|
  first
  | support_intro
  | (change FocusedInvariant PublicationJoint.Inv PublicationJoint.Safe RxHistory.Event.audit RxHistory.auditEvent _
     first
      | (owner_control_audit_at socketCallOnAudit; apply socket)
      | (owner_control_audit_at netlinkRequestAudit; apply netlink)
      | (owner_control_audit_at rtnetlinkRequestAudit; apply rtnetlink)
      | (owner_control_audit_at wgGetDevicePrefix; exact dump (.device _))
      | (owner_control_audit_at netlinkDumpStartPrefix; exact dump (.start _ _))
      | (owner_control_audit_at netlinkRecvmsgPrefix; exact dump (.receive _))
      | (owner_control_audit_at wgXmitPrefix; exact transmit _ _ _ _)
      | (owner_control_audit_at xmitMulticastLoopAudit; exact multicast _ _)
      | (owner_control_audit_at setMtuAudit; exact ⟨Appends.lift _,PublicationControls.mtu _⟩)
      | (owner_control_audit_at wgDeladdrAudit; exact ⟨Appends.lift _,PublicationRemaining.deladdr _⟩)
      | (owner_control_audit_at advanceAudit; exact ⟨Appends.lift _,PublicationDeferred.deferred (.advance _)⟩)
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
      | publication_outer_audit_steps))

private theorem get (device : DeviceRef) : Audited (dispatchAudit (.wgGet device)) := by
  simp only [dispatchAudit]
  repeat' publication_dispatch_audit_steps

private theorem getStart (device : DeviceRef) : Audited (dispatchAudit (.wgGetStart device)) := by
  simp only [dispatchAudit]
  repeat' publication_dispatch_audit_steps

private theorem getRecv : Audited (dispatchAudit .wgGetRecv) := by
  simp only [dispatchAudit]
  repeat' publication_dispatch_audit_steps

private theorem xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Audited (dispatchAudit (.wgXmit family addr payload opts)) := by
  simp (config := {zeta := false}) only [dispatchAudit]
  repeat' publication_dispatch_audit_steps

private theorem delroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    Audited (dispatchAudit (.wgDelroute family named dst plen oif typeCode metric)) := by
  simp only [dispatchAudit]
  repeat' publication_dispatch_audit_steps

private theorem addroute (dst plen oif typeCode metric mtu nlflags : Nat) :
    Audited (dispatchAudit (.wgAddroute dst plen oif typeCode metric mtu nlflags)) := by
  simp only [dispatchAudit]
  repeat' publication_dispatch_audit_steps

private theorem addaddr (addr plen : Nat) : Audited (dispatchAudit (.wgAddaddr addr plen)) := by
  simp only [dispatchAudit]
  repeat' publication_dispatch_audit_steps

private theorem advance (ticks : Nat) : Audited (dispatchAudit (.wgAdvance ticks)) := by
  simp only [dispatchAudit]
  repeat' publication_dispatch_audit_steps

/-- All actual source arms, including both seccomp probe targets. -/
theorem dispatch (call : Syscall) : PublicationJoint.Preserves (RxHistory.syscallDispatch call) := by
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
  | wgSetMtu mtu => exact (socket _ _ ⟨Appends.lift _,PublicationControls.mtu mtu⟩).2
  | wgInject family port message tos ll dest => exact PublicationOuter.socketCallOn _ _ (PublicationTraffic.inject family port message tos ll dest)
  | wgDeladdr family => exact (rtnetlink _ ⟨Appends.lift _,PublicationRemaining.deladdr family⟩).2
  | wgDelroute family named dst plen oif typeCode metric => exact (delroute family named dst plen oif typeCode metric).2
  | wgAddroute dst plen oif typeCode metric mtu nlflags => exact (addroute dst plen oif typeCode metric mtu nlflags).2
  | wgAddaddr addr plen => exact (addaddr addr plen).2
  | wgFlood count port family messages => exact PublicationTraffic.flood count port family messages
  | wgBatch items _ => exact PublicationTraffic.batch items
  | wgObserve =>
    change PublicationJoint.Preserves (do
      let (ret, observed) ← RxHistory.observe
      liftPrefix (modifyAmbient fun w => {w with extraOut := ["datagrams","replies","stats"].map fun k => (k,observed.getObjValD k)})
      RxHistory.socketCallOn LISTEN4_FD (pure ret))
    apply PublicationRemaining.observe.bind
    rintro ⟨ret,observed⟩
    dsimp only
    apply PrefixPreserves.bind
    · exact lift_modify _ (fun _ => rfl)
    intro _
    exact PublicationOuter.socketCallOn LISTEN4_FD (pure ret) (PrefixPreserves.pure safe ret)
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
theorem syscall (call : Syscall) : PublicationJoint.Preserves (RxHistory.syscall call) := by
  rw [syscallRx_factor]
  exact syscallWith_preserves call _ _ _ _ _ _ _ (dispatch call)
    PublicationDeferred.runSendWorkers PublicationDeferred.idleTimers PublicationRemaining.route
    PublicationDeferred.afterXmit PublicationDeferred.afterAdvance PublicationControls.netnsCleanup

end Leanux.Proofs.WG.PublicationSyscalls
