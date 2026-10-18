import Leanux.Proofs.WG.Roaming.RemoteDispatchFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDispatch
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open RemoteSilent

theorem dump_dispatch (entry : RemoteMap) (device : DeviceRef) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch (.wgGet device)) := by
  simp only [Leanux.dispatch]
  apply Index.DumpCore.netlinkRequest_preserves
  apply preserves_bind (PublicationPoll.native_product _ _ (RemoteLifecycle.dump entry (.device device)))
  intro result
  cases result with
  | error e => exact preserves_pure e
  | ok value =>
    exact preserves_bind (productAmbient_spec (modify fun a=>{a with extraOut:=[("device",value)]})
      _ (fun _ _ pre=>pre)) (fun _=>preserves_pure 0)

theorem dump_start (entry : RemoteMap) (device : DeviceRef) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch (.wgGetStart device)) := by
  simp only [Leanux.dispatch]
  apply Index.DumpCore.socketCallOn_preserves
  apply preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
  intro _
  apply preserves_bind (PublicationPoll.native_product _ _
    ((dump_frame _ ((getNlSock_sameWGWorld DUMP_FD).factor dumpView)).wp (RemoteRetained entry)))
  intro sock
  have tail : Preserves (fun w : World=>Retained entry w.wg) (do
      liftWG (netlinkDumpStart DUMP_FD device)
      skipCut allocCuts
      pure (0 : Int) : Leanux.M Int) :=
    preserves_bind (PublicationPoll.native_product _ _ (RemoteLifecycle.dump entry (.start DUMP_FD device))) (fun _=>
      preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
        (fun _=>preserves_pure 0))
  split
  · exact preserves_bind (productAmbient_spec (AmbientM.skipCutExactly .netlinkAutobindPort 1 allocCuts)
      _ (fun _ _ pre=>pre)) (fun _=>
      preserves_bind (PublicationPoll.native_product _ _
        ((dump_frame _ (setNlSock_sameDump DUMP_FD {sock with bound:=true})).wp (RemoteRetained entry)))
        (fun _=>tail))
  · exact tail

theorem dump_receive (entry : RemoteMap) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch .wgGetRecv) := by
  simp only [Leanux.dispatch]
  apply Index.DumpCore.socketCallOn_preserves
  apply preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
  intro _
  apply preserves_bind (PublicationPoll.native_product _ _ (RemoteLifecycle.dump entry (.receive DUMP_FD)))
  intro result
  cases result with
  | none => exact productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ pre=>pre)
  | some messages =>
    apply preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
    intro _
    split
    · exact preserves_bind (productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ pre=>pre))
        (fun _=>preserves_bind (productAmbient_spec
          (modify fun a=>{a with extraOut:=[("messages",Lean.Json.arr (messages.map (·.toJson)).toArray)]})
          _ (fun _ _ pre=>pre)) (fun _=>preserves_pure 0))
    · exact preserves_bind (productAmbient_spec
        (modify fun a=>{a with extraOut:=[("messages",Lean.Json.arr (messages.map (·.toJson)).toArray)]})
        _ (fun _ _ pre=>pre)) (fun _=>preserves_pure 0)

theorem rtnetlink_retained (entry : RemoteMap) (body : Leanux.M Int)
    (kept : Preserves (fun w : World=>Retained entry w.wg) body) :
    Preserves (fun w : World=>Retained entry w.wg) (rtnetlinkRequest body) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.rtnetlink_spec)
    _ (fun _ _ same pre=>by
      change RemoteRetained entry _ at pre ⊢
      have destinations := congrArg (fun s : WGStoreView=>fun pid : PeerId=>
        ((s.dev.bind fun d=>d.peers[pid]?).bind Peer.endpoint).map destination) same
      change destinationAt _ = destinationAt _ at destinations
      rwa [destinations]) body kept

theorem advance (entry : RemoteMap) (ticks : Nat) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch (.wgAdvance ticks)) := by
  unfold Leanux.dispatch
  simp (config := {zeta:=false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.advance
       exact RemoteWorkers.product_store entry _ (advance_sameKernel ticks))
    | (allocation_release_lift_from FS.M
       exact productFS_spec _ _ (fun _ _ _ _ pre=>pre))
    | (allocation_release_lift_from AmbientM
       exact productAmbient_spec _ _ (fun _ _ pre=>pre))
    | rx_retention_step

theorem ordinary (entry : RemoteMap) (call : Syscall)
    (selected : HolderEntryPollFree.Ordinary call) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch call) := by
  have files {α : Type} (a : FS.M α) :
      Preserves (fun w : World=>Retained entry w.wg) (liftFS a) :=
    productFS_spec a _ (fun _ _ _ _ pre=>pre)
  have seccomp {α : Type} (a : Seccomp.M α) :
      Preserves (fun w : World=>Retained entry w.wg) (liftSeccomp a) :=
    productSeccomp_spec a _ (fun _ _ _ _ pre=>pre)
  cases call with
  | eventfd2 count flags => exact files _
  | dup fd => exact files _
  | dup3 oldfd newfd flags => exact files _
  | close fd => exact files _
  | read fd count => exact files _
  | write fd count bytes => exact files _
  | pipe2 flags => exact files _
  | fcntl fd cmd arg => exact files _
  | epollCreate1 flags => exact files _
  | epollCtl epfd op fd events data => exact files _
  | epollWait epfd maxevents timeout => exact files _
  | seccompInstall via flags filter len bad mode => exact seccomp _
  | seccompProbe nr args target strict => cases target <;> exact seccomp _
  | seccompPrctl cmd args => exact seccomp _
  | seccompCapdrop => exact seccomp _
  | seccompQuery cmd action flags => exact seccomp _
  | _ => exact False.elim selected


theorem retained (entry : RemoteMap) (call : Syscall) (selected : DispatchRetained call) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch call) := by
  cases call
  case wgGet device => exact dump_dispatch entry device
  case wgGetStart device => exact dump_start entry device
  case wgGetRecv => exact dump_receive entry
  case wgUp => exact Index.DumpCore.socketCallOn_preserves _ _ _ (RemoteLifecycle.envUp_native entry)
  case wgDown => exact Index.DumpCore.socketCallOn_preserves _ _ _ (RemoteLifecycle.envDown_native entry)
  case wgSetMtu mtu => exact Index.DumpCore.socketCallOn_preserves _ _ _ ((mtu_frame mtu).wp (RemoteRetained entry))
  case wgDeladdr family =>
    exact rtnetlink_retained entry _ (RemoteWorkers.product_store entry _ (wgDeladdr_sameKernel family))
  case wgDelroute family named dst plen oif typeCode metric =>
    exact rtnetlink_retained entry _ (store_retained entry _
      (Index.ReachedControls.route_delete_store family named dst plen oif typeCode metric))
  case wgAddroute dst plen oif typeCode metric mtu flags =>
    exact rtnetlink_retained entry _ (store_retained entry _
      (Index.ReachedControls.route_add_store dst plen oif typeCode metric mtu flags))
  case wgAddaddr addr plen =>
    exact rtnetlink_retained entry _ (store_retained entry _ (Index.ReachedControls.address_add_store addr plen))
  case wgAdvance ticks => exact advance entry ticks
  case wgNetnsClose => exact store_retained entry _ SyscallFrames.netnsClose_sameWGStore
  all_goals try (solve | cases selected)
  all_goals exact ordinary entry _ True.intro

theorem retained_covered (entry : RemoteMap) (call : Syscall) (selected : DispatchRetained call) :
    PrefixPreserves (RemoteDriver.Inv entry) RemoteDriver.Safe
      (RemoteDriver.focus (RxHistory.syscallDispatch call)) :=
  RemoteDriver.focus_retained entry _ _ (RxHistory.syscallDispatch_appends call)
    (RxHistory.syscallDispatch_erases call) (fun before=>retained before call selected)

end Leanux.Proofs.WG.Roaming.RemoteDispatch
