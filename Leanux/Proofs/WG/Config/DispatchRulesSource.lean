import Leanux.Proofs.WG.Index.ReachedOrdinaryControlSource
import Leanux.Proofs.WG.Config.DumpInvariantSource
import Leanux.Proofs.WG.Packets.PublicationPoll

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.DispatchRules
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do

structure Contracts (P : WGWorld → Prop) where
  stable : ∀ w v, wgStoreView v = wgStoreView w → P w → P v
  dump : ∀ call : NetlinkDumpCall, Preserves P call.original
  dumpFrame : ∀ {α : Type} (action : WG.M α), SameDump action → Preserves P action
  up : Preserves (fun w : World=>P w.wg) Env.wgUp
  down : Preserves (fun w : World=>P w.wg) Env.wgDown
  mtu : ∀ n, Preserves (fun w : World=>P w.wg) (Env.setMtu n)

theorem store (P : WGWorld → Prop) (c : Contracts P) {α : Type}
    (action : Leanux.M α) (same : SameView (fun w : World=>wgStoreView w.wg) action) :
    Preserves (fun w : World=>P w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  exact c.stable w.wg v.wg ((ProjectedAction.iff_run _ _ _).mp same w result v run) pre

theorem product (P : WGWorld → Prop) (c : Contracts P) {α : Type}
    (action : Leanux.M α) (same : SameProductStore action) :
    Preserves (fun w : World=>P w.wg) action :=
  store P c action (same.of_factor (fun s : ProductStore43=>s.2.2.2) _ (fun _=>rfl))

theorem dump_dispatch (P : WGWorld → Prop) (c : Contracts P) (device : DeviceRef) :
    Preserves (fun w : World=>P w.wg) (Leanux.dispatch (.wgGet device)) := by
  simp only [Leanux.dispatch]
  apply Index.DumpCore.netlinkRequest_preserves
  apply preserves_bind (PublicationPoll.native_product _ _ (c.dump (.device device)))
  intro result
  cases result with
  | error e => exact preserves_pure e
  | ok value =>
    exact preserves_bind (productAmbient_spec (modify fun a=>{a with extraOut:=[("device",value)]})
      _ (fun _ _ pre=>pre)) (fun _=>preserves_pure 0)

theorem dump_start (P : WGWorld → Prop) (c : Contracts P) (device : DeviceRef) :
    Preserves (fun w : World=>P w.wg) (Leanux.dispatch (.wgGetStart device)) := by
  simp only [Leanux.dispatch]
  apply Index.DumpCore.socketCallOn_preserves
  apply preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
  intro _
  apply preserves_bind (PublicationPoll.native_product _ _
    (c.dumpFrame _ ((getNlSock_sameWGWorld DUMP_FD).factor dumpView)))
  intro sock
  have tail : Preserves (fun w : World=>P w.wg) (do
      liftWG (netlinkDumpStart DUMP_FD device)
      skipCut allocCuts
      pure (0 : Int) : Leanux.M Int) :=
    preserves_bind (PublicationPoll.native_product _ _ (c.dump (.start DUMP_FD device))) (fun _=>
      preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
        (fun _=>preserves_pure 0))
  split
  · exact preserves_bind (productAmbient_spec (AmbientM.skipCutExactly .netlinkAutobindPort 1 allocCuts)
      _ (fun _ _ pre=>pre)) (fun _=>
      preserves_bind (PublicationPoll.native_product _ _
        (c.dumpFrame _ (setNlSock_sameDump DUMP_FD {sock with bound:=true})))
        (fun _=>tail))
  · exact tail

theorem dump_receive (P : WGWorld → Prop) (c : Contracts P) :
    Preserves (fun w : World=>P w.wg) (Leanux.dispatch .wgGetRecv) := by
  simp only [Leanux.dispatch]
  apply Index.DumpCore.socketCallOn_preserves
  apply preserves_bind (productAmbient_spec (AmbientM.skipCut allocCuts) _ (fun _ _ pre=>pre))
  intro _
  apply preserves_bind (PublicationPoll.native_product _ _ (c.dump (.receive DUMP_FD)))
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

theorem rtnetlink_retained (P : WGWorld → Prop) (c : Contracts P) (body : Leanux.M Int)
    (kept : Preserves (fun w : World=>P w.wg) body) :
    Preserves (fun w : World=>P w.wg) (rtnetlinkRequest body) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.rtnetlink_spec)
    _ (fun w v same pre=>c.stable w.wg v.wg same pre) body kept

theorem advance (P : WGWorld → Prop) (c : Contracts P) (ticks : Nat) :
    Preserves (fun w : World=>P w.wg) (Leanux.dispatch (.wgAdvance ticks)) := by
  unfold Leanux.dispatch
  simp (config := {zeta:=false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.advance
       exact product P c _ (advance_sameKernel ticks))
    | (allocation_release_lift_from FS.M
       exact productFS_spec _ _ (fun _ _ _ _ pre=>pre))
    | (allocation_release_lift_from AmbientM
       exact productAmbient_spec _ _ (fun _ _ pre=>pre))
    | rx_retention_step

theorem ordinary (P : WGWorld → Prop) (call : Syscall)
    (selected : HolderEntryPollFree.Ordinary call) :
    Preserves (fun w : World=>P w.wg) (Leanux.dispatch call) := by
  have files {α : Type} (a : FS.M α) :
      Preserves (fun w : World=>P w.wg) (liftFS a) :=
    productFS_spec a _ (fun _ _ _ _ pre=>pre)
  have seccomp {α : Type} (a : Seccomp.M α) :
      Preserves (fun w : World=>P w.wg) (liftSeccomp a) :=
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


theorem retained (P : WGWorld → Prop) (c : Contracts P) (call : Syscall) (selected : DispatchRetained call) :
    Preserves (fun w : World=>P w.wg) (Leanux.dispatch call) := by
  cases call
  case wgGet device => exact dump_dispatch P c device
  case wgGetStart device => exact dump_start P c device
  case wgGetRecv => exact dump_receive P c
  case wgUp => exact Index.DumpCore.socketCallOn_preserves _ _ _ (c.up)
  case wgDown => exact Index.DumpCore.socketCallOn_preserves _ _ _ (c.down)
  case wgSetMtu mtu => exact Index.DumpCore.socketCallOn_preserves _ _ _ (c.mtu mtu)
  case wgDeladdr family =>
    exact rtnetlink_retained P c _ (product P c _ (wgDeladdr_sameKernel family))
  case wgDelroute family named dst plen oif typeCode metric =>
    exact rtnetlink_retained P c _ (store P c _
      (Index.ReachedControls.route_delete_store family named dst plen oif typeCode metric))
  case wgAddroute dst plen oif typeCode metric mtu flags =>
    exact rtnetlink_retained P c _ (store P c _
      (Index.ReachedControls.route_add_store dst plen oif typeCode metric mtu flags))
  case wgAddaddr addr plen =>
    exact rtnetlink_retained P c _ (store P c _ (Index.ReachedControls.address_add_store addr plen))
  case wgAdvance ticks => exact advance P c ticks
  case wgNetnsClose => exact store P c _ SyscallFrames.netnsClose_sameWGStore
  all_goals try (solve | cases selected)
  all_goals exact ordinary P _ True.intro


end Leanux.Proofs.WG.Config.DispatchRules
