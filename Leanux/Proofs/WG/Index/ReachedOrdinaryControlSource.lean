import Leanux.Proofs.WG.Index.ReachedLifecycleControlSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedControls
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem dump (ref : DeviceRef) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch (.wgGet ref)) :=
  configuration_pair _ _ (RxHistory.syscallDispatch_erases (.wgGet ref))
    (fun _=>HolderDumpEntry.dispatchGet ref) (fun cs=>DumpCore.dispatchGet_entry cs [] ref)

theorem dump_start (ref : DeviceRef) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch (.wgGetStart ref)) :=
  configuration_pair _ _ (RxHistory.syscallDispatch_erases (.wgGetStart ref))
    (fun _=>HolderDumpEntry.dispatchStart ref) (fun cs=>DumpCore.dispatchStart_entry cs [] ref)

theorem dump_receive :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch .wgGetRecv) :=
  configuration_pair _ _ (RxHistory.syscallDispatch_erases .wgGetRecv)
    (fun _=>HolderDumpEntry.dispatchRecv) (fun cs=>DumpCore.dispatchRecv_entry cs [])

theorem deladdr (family : Nat) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch (.wgDeladdr family)) := by
  apply configuration_pair _ _ (RxHistory.syscallDispatch_erases (.wgDeladdr family))
    (fun _=>HolderEntryPollFree.deladdr family)
  intro cs
  exact rtnetlink_configuration cs [] _
    (LifecycleEnvironment.product_entry cs [] _ (wgDeladdr_sameKernel family))

theorem delroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgDelroute family named dst plen oif typeCode metric)) := by
  apply configuration_pair _ _
    (RxHistory.syscallDispatch_erases (.wgDelroute family named dst plen oif typeCode metric))
    (fun _=>HolderEntryPollFree.delroute family named dst plen oif typeCode metric)
  intro cs
  exact rtnetlink_configuration cs [] _
    (configuration_wg_store cs [] _ (route_delete_store family named dst plen oif typeCode metric))

theorem addroute (dst plen oif typeCode metric mtu flags : Nat) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgAddroute dst plen oif typeCode metric mtu flags)) := by
  apply configuration_pair _ _
    (RxHistory.syscallDispatch_erases (.wgAddroute dst plen oif typeCode metric mtu flags))
    (fun _=>HolderEntryPollFree.addroute dst plen oif typeCode metric mtu flags)
  intro cs
  exact rtnetlink_configuration cs [] _
    (configuration_wg_store cs [] _ (route_add_store dst plen oif typeCode metric mtu flags))

theorem addaddr (addr plen : Nat) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch (.wgAddaddr addr plen)) := by
  apply configuration_pair _ _ (RxHistory.syscallDispatch_erases (.wgAddaddr addr plen))
    (fun _=>HolderEntryPollFree.addaddr addr plen)
  intro cs
  exact rtnetlink_configuration cs [] _
    (configuration_wg_store cs [] _ (address_add_store addr plen))

theorem namespaceClose :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch .wgNetnsClose) :=
  configuration_pair _ _ (RxHistory.syscallDispatch_erases .wgNetnsClose)
    (fun _=>HolderEntryPollFree.namespaceClose)
    (fun cs=>configuration_wg_store cs [] _ SyscallFrames.netnsClose_sameWGStore)

theorem advance_configuration (cs : Ledger) (loans : Reservations) (ticks : Nat) :
    Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg)
      (Leanux.dispatch (.wgAdvance ticks)) := by
  unfold Leanux.dispatch
  simp (config := {zeta:=false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.advance
       exact LifecycleEnvironment.product_entry cs loans _ (advance_sameKernel ticks))
    | (allocation_release_lift_from FS.M
       exact productFS_spec _ _ (fun _ _ _ _ pre=>pre))
    | (allocation_release_lift_from AmbientM
       exact productAmbient_spec _ _ (fun _ _ pre=>pre))
    | rx_retention_step

theorem advance (ticks : Nat) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch (.wgAdvance ticks)) :=
  configuration_pair _ _ (RxHistory.syscallDispatch_erases (.wgAdvance ticks))
    (fun _=>HolderEntryPollFree.advance ticks) (fun cs=>advance_configuration cs [] ticks)

theorem ordinary_configuration (cs : Ledger) (loans : Reservations)
    (call : Syscall) (selected : HolderEntryPollFree.Ordinary call) :
    Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg) (Leanux.dispatch call) := by
  have files {α : Type} (a : FS.M α) :
      Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg) (liftFS a) :=
    productFS_spec a _ (fun _ _ _ _ pre=>pre)
  have seccomp {α : Type} (a : Seccomp.M α) :
      Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg) (liftSeccomp a) :=
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

theorem ordinary (call : Syscall) (selected : HolderEntryPollFree.Ordinary call) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch call) :=
  configuration_pair _ _ (RxHistory.syscallDispatch_erases call)
    (fun _=>HolderEntryPollFree.ordinary call selected)
    (fun cs=>ordinary_configuration cs [] call selected)

theorem retained (call : Syscall) (selected : DispatchRetained call) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch call) := by
  cases call
  case wgGet ref => exact dump ref
  case wgGetStart ref => exact dump_start ref
  case wgGetRecv => exact dump_receive
  case wgUp => exact up
  case wgDown => exact down
  case wgSetMtu n => exact mtu n
  case wgDeladdr family => exact deladdr family
  case wgDelroute family named dst plen oif typeCode metric => exact delroute family named dst plen oif typeCode metric
  case wgAddroute dst plen oif typeCode metric mtu flags => exact addroute dst plen oif typeCode metric mtu flags
  case wgAddaddr addr plen => exact addaddr addr plen
  case wgAdvance ticks => exact advance ticks
  case wgNetnsClose => exact namespaceClose
  all_goals try (solve | cases selected)
  all_goals exact ordinary _ True.intro

end Leanux.Proofs.WG.Index.ReachedControls
