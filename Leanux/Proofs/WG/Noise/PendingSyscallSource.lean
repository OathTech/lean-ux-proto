import Leanux.Proofs.WG.Noise.PendingSyscallFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSyscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration PendingSession PendingOuter

abbrev Audited {α : Type} (g : AuditM α) :=
  FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent g

theorem audit_lift {α : Type} (a : Leanux.M α)
    (ha : PrefixPreserves StateInv HistorySafe (liftPrefix a)) : Audited (liftPrefix a) :=
  FocusedInvariant.lift _ _ a ha

theorem product_lift {α : Type} (a : Leanux.M α) (same : SameProductStore a) :
    Audited (liftPrefix a) :=
  audit_lift a (lift_store a (same.of_factor (fun s : ProductStore43 => s.2.2.2) _ (fun _ => rfl)))

theorem scalar_lift (mtu : Nat) : Audited (setMtuAudit mtu) := by
  apply audit_lift
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ PendingScheduler.safe
  intro h w x v hi run
  exact scalar_native w v _ ((ProjectedAction.iff_run _ _ _).mp
    (setMtu_sameEnvScalar mtu) w x v run) hi

theorem socket (fd : Nat) (body : AuditM Int) (hb : Audited body) :
    Audited (socketCallOnAudit fd body) := by
  refine ⟨?_,?_⟩
  · rw [socketCallOnAudit_factor]
    exact socketCallOnWith_appends fd hb.1
  · rw [socketCallOnAudit_factor]
    apply prefixPreserves_congr (socketCallOn_pending_variant fd _ hb.2)
    intro w h
    exact socketCallOnWith_focuses RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
      fd (FocusesUnder.focus body) hb.1 w h True.intro

theorem netlink (body : AuditM Int) (hb : Audited body) :
    Audited (netlinkRequestAudit body) := by
  refine ⟨?_,?_⟩
  · rw [netlinkRequestAudit_factor]
    exact netlinkRequestWith_appends hb.1
  · rw [netlinkRequestAudit_factor]
    rw [← netlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) body hb.1]
    exact netlinkRequest_pending_variant _ hb.2

theorem rtnetlink (body : AuditM Int) (hb : Audited body) :
    Audited (rtnetlinkRequestAudit body) := by
  refine ⟨?_,?_⟩
  · rw [rtnetlinkRequestAudit_factor]
    exact rtnetlinkRequestWith_appends hb.1
  · rw [rtnetlinkRequestAudit_factor]
    rw [← rtnetlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) body hb.1]
    exact rtnetlinkRequest_pending_variant _ hb.2

theorem dump_lift {α : Type} (a : WG.M α) (same : SameDump a) :
    Audited (liftPrefix (liftWG a)) := by
  apply audit_lift
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ PendingScheduler.safe
  intro h w x v hi run
  exact (hoare_iff_run _ _ _).mp
    (native_product a (fun seen => Config.DumpInvariant.frame (PendingDump.contracts seen) a same) _)
    w x v hi run

macro "pending_audit_step" : tactic => `(tactic| first
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at socketCallOnAudit; apply socket)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at netlinkRequestAudit; apply netlink)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at rtnetlinkRequestAudit; apply rtnetlink)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at wgGetDevicePrefix; exact ⟨Appends.focus _ _ _,PendingDump.observed (.device _)⟩)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at netlinkDumpStartPrefix; exact ⟨Appends.focus _ _ _,PendingDump.observed (.start _ _)⟩)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at netlinkRecvmsgPrefix; exact ⟨Appends.focus _ _ _,PendingDump.observed (.receive _)⟩)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at getNlSock; exact dump_lift _ ((getNlSock_sameWGWorld _).factor dumpView))
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at setNlSock; exact dump_lift _ (setNlSock_sameDump _ _))
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at Env.wgDelroute; apply audit_lift; apply lift_store
     unfold Env.wgDelroute; syscall_routing_store)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at Env.wgAddroute; apply audit_lift; apply lift_store
     unfold Env.wgAddroute; syscall_routing_store)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at Env.wgAddaddr; apply audit_lift; apply lift_store
     unfold Env.wgAddaddr; syscall_routing_store)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at advanceAudit; exact product_lift _ (advance_sameKernel _))
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at liftFS; exact audit_lift _ (lift_fs _))
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at liftSeccomp; exact audit_lift _ (lift_seccomp _))
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at modifyAmbient; apply audit_lift
     exact lift_modify _ (fun _ => rfl))
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at unsupported; apply audit_lift
     exact lift_ambient (AmbientM.unsupported _))
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at liftPrefix; apply audit_lift
     first | exact lift_ambient _ | exact lift_fs _ | exact lift_seccomp _)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at Pure.pure; exact FocusedInvariant.pure _ _ PendingScheduler.safe _)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at Bind.bind; apply FocusedInvariant.bind
      (encode := RxHistory.Event.audit) (decode := RxHistory.auditEvent) (fun _ => rfl))
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_at ite; apply FocusedInvariant.ite)
  | (change FocusedInvariant StateInv HistorySafe RxHistory.Event.audit RxHistory.auditEvent _; owner_control_audit_reduce)
  | support_intro)

theorem dump_dispatch (device : DeviceRef) : Audited (dispatchAudit (.wgGet device)) := by
  simp only [dispatchAudit]
  repeat' pending_audit_step

theorem dump_start (device : DeviceRef) : Audited (dispatchAudit (.wgGetStart device)) := by
  simp only [dispatchAudit]
  repeat' pending_audit_step

theorem dump_receive : Audited (dispatchAudit .wgGetRecv) := by
  simp only [dispatchAudit]
  repeat' pending_audit_step

theorem route_delete (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    Audited (dispatchAudit (.wgDelroute family named dst plen oif typeCode metric)) := by
  simp only [dispatchAudit]
  repeat' pending_audit_step

theorem route_add (dst plen oif typeCode metric mtu nlflags : Nat) :
    Audited (dispatchAudit (.wgAddroute dst plen oif typeCode metric mtu nlflags)) := by
  simp only [dispatchAudit]
  repeat' pending_audit_step

theorem addr_add (addr plen : Nat) : Audited (dispatchAudit (.wgAddaddr addr plen)) := by
  simp only [dispatchAudit]
  repeat' pending_audit_step

theorem advance (ticks : Nat) : Audited (dispatchAudit (.wgAdvance ticks)) := by
  simp only [dispatchAudit]
  repeat' pending_audit_step

theorem transmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves StateInv HistorySafe (RxHistory.audit
      (syscallXmitWith xmitMulticastLoopAudit
        (fun family addr packets mtu => auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu)))
        family addr payload opts)) := by
  unfold RxHistory.audit
  rw [← syscallXmitWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    xmitMulticastLoopAudit
    (fun family addr packets mtu => auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu)))
    xmitMulticastLoopAudit_appends (fun _ _ _ _ => Appends.focus _ _ _)]
  exact syscallXmitWith_preserves PendingScheduler.safe state_store _ _
    PendingTraffic.multicast PendingTraffic.transmit family addr payload opts

theorem retained (call : Syscall) (hc : DispatchRetained call) :
    PrefixPreserves StateInv HistorySafe (RxHistory.syscallDispatch call) := by
  cases call
  case wgGet device => exact (dump_dispatch device).2
  case wgGetStart device => exact (dump_start device).2
  case wgGetRecv => exact dump_receive.2
  case wgUp => exact (socket _ _ ⟨
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.up).1,
    PendingEnvironment.up_observed⟩).2
  case wgDown => exact (socket _ _ ⟨
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.down).1,
    PendingEnvironment.down_observed⟩).2
  case wgSetMtu mtu => exact (socket _ _ (scalar_lift mtu)).2
  case wgDeladdr family => exact (rtnetlink _ (product_lift _ (wgDeladdr_sameKernel family))).2
  case wgDelroute family named dst plen oif typeCode metric => exact (route_delete family named dst plen oif typeCode metric).2
  case wgAddroute dst plen oif typeCode metric mtu nlflags => exact (route_add dst plen oif typeCode metric mtu nlflags).2
  case wgAddaddr addr plen => exact (addr_add addr plen).2
  case wgAdvance ticks => exact (advance ticks).2
  case wgNetnsClose => exact (audit_lift _ (lift_store _ SyscallFrames.netnsClose_sameWGStore)).2
  case seccompProbe nr args target strict => cases target <;> exact (audit_lift _ (lift_seccomp _)).2
  case eventfd2 count flags => exact (audit_lift _ (lift_fs _)).2
  case dup fd => exact (audit_lift _ (lift_fs _)).2
  case dup3 old new flags => exact (audit_lift _ (lift_fs _)).2
  case close fd => exact (audit_lift _ (lift_fs _)).2
  case read fd count => exact (audit_lift _ (lift_fs _)).2
  case write fd count buf => exact (audit_lift _ (lift_fs _)).2
  case pipe2 flags => exact (audit_lift _ (lift_fs _)).2
  case fcntl fd cmd arg => exact (audit_lift _ (lift_fs _)).2
  case epollCreate1 flags => exact (audit_lift _ (lift_fs _)).2
  case epollCtl epfd op fd events data => exact (audit_lift _ (lift_fs _)).2
  case epollWait epfd maxevents timeout => exact (audit_lift _ (lift_fs _)).2
  case seccompInstall via flags filter len bad mode => exact (audit_lift _ (lift_seccomp _)).2
  case seccompPrctl cmd args => exact (audit_lift _ (lift_seccomp _)).2
  case seccompCapdrop => exact (audit_lift _ (lift_seccomp _)).2
  case seccompQuery cmd action flags => exact (audit_lift _ (lift_seccomp _)).2
  all_goals cases hc

theorem observe_dispatch : PrefixPreserves StateInv HistorySafe
    (RxHistory.syscallDispatch .wgObserve) := by
  change PrefixPreserves StateInv HistorySafe (do
    let (ret, observed) ← RxHistory.observe
    liftPrefix (modifyAmbient fun w => {w with extraOut := ["datagrams","replies","stats"].map fun k => (k,observed.getObjValD k)})
    RxHistory.socketCallOn LISTEN4_FD (pure ret))
  apply (PendingTraffic.observe PendingScheduler.actualWorkers PendingScheduler.actualLeaves).bind
  rintro ⟨ret,observed⟩
  dsimp only
  apply PrefixPreserves.bind
  · exact lift_modify _ (fun _ => rfl)
  intro _
  exact socketCallOn_pending_variant LISTEN4_FD (pure ret) (PrefixPreserves.pure PendingScheduler.safe ret)

theorem dispatch (call : Syscall) :
    PrefixPreserves StateInv HistorySafe (RxHistory.syscallDispatch call) := by
  rw [rxDispatch_source]
  apply dispatchWith_preserves
  · exact retained
  · intro attrs
    exact (netlink _ ⟨Appends.focus _ _ _,device_configuration_observed attrs⟩).2
  · exact (rtnetlink _ ⟨Appends.focus _ _ _,create_observed⟩).2
  · exact (rtnetlink _ ⟨
      (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.delete).1,
      PendingEnvironment.delete_observed⟩).2
  · exact transmit
  · intro family port msg tos ll dest
    exact socketCallOn_pending_variant _ _
      (PendingTraffic.inject PendingScheduler.actualWorkers family port msg tos ll dest)
  · exact PendingTraffic.flood PendingScheduler.actualWorkers PendingScheduler.actualLeaves
  · exact PendingTraffic.batch PendingScheduler.actualWorkers PendingScheduler.actualLeaves
  · exact observe_dispatch

theorem syscall (call : Syscall) :
    PrefixPreserves StateInv HistorySafe (RxHistory.syscall call) := by
  rw [syscallRx_factor]
  exact SyscallSource.preserves PendingScheduler.safe state_store call _ _ _ _ _ _ _
    (dispatch call)
    (PendingScheduler.send PendingScheduler.actualWorkers PendingScheduler.actualLeaves)
    (PendingScheduler.idle PendingScheduler.actualWorkers PendingScheduler.actualLeaves)
    (product_lift _ routeIntoWg0_sameKernel).2
    (PendingScheduler.afterXmit PendingScheduler.actualWorkers PendingScheduler.actualLeaves)
    (PendingScheduler.afterAdvance PendingScheduler.actualWorkers PendingScheduler.actualLeaves)
    PendingEnvironment.cleanup_observed

end Leanux.Proofs.WG.Noise.PendingSyscalls
