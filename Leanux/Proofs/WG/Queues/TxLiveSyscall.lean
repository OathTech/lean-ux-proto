import Leanux.Proofs.WG.Queues.TxLiveDispatchSupport
import Leanux.Proofs.WG.Queues.TxLiveControls
import Leanux.Proofs.WG.Queues.TxLiveDump
import Leanux.Proofs.WG.Queues.TxLiveDeviceConfiguration

/-! Every original syscall and its actual return-to-user suffix preserves the
live encryption frontier. Normal errno results retain the same suffix choices;
the existing observer preserves stopped journals without an endpoint claim. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveSyscall
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open LiveFrontier LiveDispatch

private theorem dump_get (ref : DeviceRef) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.dispatch (.wgGet ref)) := by
  unfold Leanux.dispatch
  apply netlink
  repeat' first
    | (allocation_release_lift_from WG.M; exact PublicationPoll.native_product Ready _ (dump_device _))
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | live_dispatch_step

private theorem dump_start :
    Preserves (fun w : World=>Ready w.wg) (Leanux.dispatch (.wgGetStart ref)) := by
  have finish : Preserves (fun w : World=>Ready w.wg) (do
      liftWG (netlinkDumpStart DUMP_FD ref)
      skipCut allocCuts
      pure (0 : Int)) :=
    preserves_bind (PublicationPoll.native_product Ready (netlinkDumpStart DUMP_FD ref)
      (LiveFrontier.dump_start DUMP_FD ref)) (fun _=>
      preserves_bind (ambient (AmbientM.skipCut allocCuts)) (fun _=>preserves_pure 0))
  unfold Leanux.dispatch
  apply socket
  apply preserves_bind (ambient (AmbientM.skipCut allocCuts))
  intro _
  apply preserves_bind (PublicationPoll.native_product Ready (getNlSock DUMP_FD)
    ((getNlSock_sameWGWorld DUMP_FD).wp Ready))
  intro sock
  split
  · apply preserves_bind (ambient (AmbientM.skipCutExactly .netlinkAutobindPort 1 allocCuts))
    intro _
    apply preserves_bind (PublicationPoll.native_product Ready
      (setNlSock DUMP_FD {sock with bound:=true})
      (dump_frame (setNlSock_sameDump DUMP_FD {sock with bound:=true})))
    intro _
    exact finish
  · exact finish

private theorem dump_recv :
    Preserves (fun w : World=>Ready w.wg) (Leanux.dispatch .wgGetRecv) := by
  unfold Leanux.dispatch
  apply socket
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (allocation_release_lift_from WG.M; exact PublicationPoll.native_product Ready _ (LiveFrontier.dump_recv _))
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | live_dispatch_step

private theorem observe_dispatch :
    Preserves (fun w : World=>Ready w.wg) (Leanux.dispatch .wgObserve) := by
  unfold Leanux.dispatch
  apply preserves_bind observe_native
  intro out
  apply preserves_bind
  · unfold modifyAmbient
    exact ambient _
  intro _
  exact socket _ _ (preserves_pure _)

private theorem advance_dispatch (ticks : Nat) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.dispatch (.wgAdvance ticks)) := by
  unfold Leanux.dispatch
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.advance; exact stored (advance_sameKernel _))
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | live_dispatch_step

theorem dispatch_native (call : Syscall) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.dispatch call) := by
  cases call with
  | eventfd2 count flags=>exact fs _
  | dup fd=>exact fs _
  | dup3 oldfd newfd flags=>exact fs _
  | close fd=>exact fs _
  | read fd count=>exact fs _
  | write fd count buf=>exact fs _
  | pipe2 flags=>exact fs _
  | fcntl fd cmd arg=>exact fs _
  | epollCreate1 flags=>exact fs _
  | epollCtl epfd op fd events data=>exact fs _
  | epollWait epfd maxevents timeout=>exact fs _
  | wgSet attrs=>exact netlink _ (PublicationPoll.native_product Ready _ (set_device attrs))
  | wgGet ref=>exact dump_get ref
  | wgGetStart ref=>exact dump_start
  | wgGetRecv=>exact dump_recv
  | wgUp=>exact socket _ _ env_up
  | wgXmit family addr payload opts=>exact xmit family addr payload opts
  | wgSetMtu n=>exact socket _ _ (env_mtu n)
  | wgInject family port msg tos ll dest=>exact socket _ _ (LiveTraffic.inject_native family port msg tos ll dest)
  | wgDeladdr family=>exact rtnetlink _ (stored (wgDeladdr_sameKernel family))
  | wgDelroute family named dst plen oif typeCode metric=>exact rtnetlink _ (delroute family named dst plen oif typeCode metric)
  | wgAddroute dst plen oif typeCode metric mtu flags=>exact rtnetlink _ (addroute dst plen oif typeCode metric mtu flags)
  | wgAddaddr addr plen=>exact rtnetlink _ (addaddr addr plen)
  | wgFlood count port family messages=>exact LiveTraffic.flood_native count port family messages
  | wgBatch items _=>exact LiveTraffic.batch_native items
  | wgObserve=>exact observe_dispatch
  | wgAdvance ticks=>exact advance_dispatch ticks
  | wgCreate=>exact rtnetlink _ (PublicationPoll.native_product Ready _ device_create)
  | wgDown=>exact socket _ _ env_down
  | wgDelete=>exact rtnetlink _ env_delete
  | wgNetnsClose=>exact SyscallFrames.netnsClose_sameWGStore.wp (fun s : WGStoreView=>Ready {dev:=s.dev})
  | seccompInstall via flags filter len bad mode=>exact seccomp _
  | seccompProbe nr args target strict=>cases target <;> exact seccomp _
  | seccompPrctl cmd args=>exact seccomp _
  | seccompCapdrop=>exact seccomp _
  | seccompQuery cmd action flags=>exact seccomp _

theorem dispatch (call : Syscall) :
    PrefixPreserves LiveScheduler.Inv (fun _=>True) (RxHistory.syscallDispatch call) :=
  LiveTraffic.observed _ _ (RxHistory.syscallDispatch_appends call)
    (RxHistory.syscallDispatch_erases call) (dispatch_native call)

theorem syscall (call : Syscall) :
    PrefixPreserves LiveScheduler.Inv (fun _=>True) (RxHistory.syscall call) := by
  rw [Configuration.syscallRx_factor]
  apply SyscallSource.preserves (I:=LiveScheduler.Inv) (S:=fun _=>True)
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>LiveTraffic.wg_store eq hi)
  · exact dispatch call
  · exact LiveDeferred.send
  · exact LiveDeferred.idle
  · exact LiveTraffic.observed _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases routeIntoWg0Audit_erases) (stored routeIntoWg0_sameKernel)
  · exact LiveDeferred.afterXmit
  · exact LiveDeferred.afterAdvance
  · exact LiveTraffic.observed _ _ (Appends.focus _ _ _)
      (RxHistory.audit_erases envNetnsCleanupAudit_erases) env_cleanup

/-- The initialized runner may use this actual native contract directly. -/
theorem syscall_native (call : Syscall) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.syscall call) :=
  LiveTraffic.native _ _ (RxHistory.syscall_erases call) (syscall call)

end Leanux.Proofs.WG.Queues.TxDisposition.LiveSyscall
