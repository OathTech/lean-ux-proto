import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterControls
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTransmit
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDeviceCreate
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpDispatch
import Leanux.Proofs.WG.Queues.HolderDumpEntry

/-! Concrete retained syscall observers keep the same outer entry on every
normal result, including errno returns. Dumps may exchange their real cursor
holder; transmission may add real durable holders. Neither is treated as a
quiet state operation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Dispatch
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits

theorem checked (call : Syscall)
    (old : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch call))
    (account : Preserves (fun w : World => ExactBoundary cs loans w.wg) (Leanux.dispatch call)) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch call) :=
  Frames.pair_native _ _ (RxHistory.syscallDispatch_erases call) old account

theorem create : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch .wgCreate) :=
  checked _ HolderEntryPollFree.create
    (Frames.rtnetlink _ (fun _ _ same hi => hi.store same) _ (ExactBoundary.lift _ DeviceCreate.create))

theorem up : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch .wgUp) :=
  checked _ HolderEntryPollFree.up
    (Frames.socket _ (fun _ _ same hi => hi.store same) _ _ RetiredPeer.Controls.env_up)

theorem mtu (n : Nat) : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch (.wgSetMtu n)) :=
  checked _ (HolderEntryPollFree.mtu n)
    (Frames.socket _ (fun _ _ same hi => hi.store same) _ _ (ControlFrames.mtu n))

theorem configuration (attrs : DeviceAttrs) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch (.wgSet attrs)) :=
  Outer.Controls.configuration attrs

theorem get (ref : DeviceRef) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch (.wgGet ref)) :=
  checked _ (HolderDumpEntry.dispatchGet ref) (Dump.boundary_dispatch_get ref)

theorem getStart (ref : DeviceRef) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch (.wgGetStart ref)) :=
  checked _ (HolderDumpEntry.dispatchStart ref) (Dump.boundary_dispatch_start ref)

theorem getRecv : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch .wgGetRecv) :=
  checked _ HolderDumpEntry.dispatchRecv Dump.boundary_dispatch_receive

theorem xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgXmit family addr payload opts)) :=
  checked _ (HolderEntryDispatch.xmit family addr payload opts) (Transmit.dispatch family addr payload opts)

theorem namespaceClose : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch .wgNetnsClose) := by
  apply checked _ HolderEntryPollFree.namespaceClose
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  exact hi.store ((ProjectedAction.iff_run _ _ _).mp SyscallFrames.netnsClose_sameWGStore w result v run)

private theorem fs (action : FS.M α) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (liftFS action) :=
  productFS_spec action _ (fun _ _ _ _ hi => hi)

private theorem seccomp (action : Seccomp.M α) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (liftSeccomp action) :=
  productSeccomp_spec action _ (fun _ _ _ _ hi => hi)

/-- Only the explicitly classified FS/seccomp constructors use this frame. -/
theorem ordinary (call : Syscall) (selected : HolderEntryPollFree.Ordinary call) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch call) := by
  apply checked _ (HolderEntryPollFree.ordinary call selected)
  cases call with
  | eventfd2 count flags => exact fs _
  | dup fd => exact fs _
  | dup3 oldfd newfd flags => exact fs _
  | close fd => exact fs _
  | read fd count => exact fs _
  | write fd count buf => exact fs _
  | pipe2 flags => exact fs _
  | fcntl fd cmd arg => exact fs _
  | epollCreate1 flags => exact fs _
  | epollCtl epfd op fd events data => exact fs _
  | epollWait epfd maxevents timeout => exact fs _
  | seccompInstall via flags filter len bad mode => exact seccomp _
  | seccompProbe nr args target strict => cases target <;> exact seccomp _
  | seccompPrctl cmd args => exact seccomp _
  | seccompCapdrop => exact seccomp _
  | seccompQuery cmd action flags => exact seccomp _
  | _ => exact False.elim selected

/-- Hiding the history occurs only after the concrete original dispatcher
has supplied its actual paired endpoint. -/
theorem boundary (call : Syscall)
    (keeps : ∀ cs, PrefixPreserves (Inv cs []) OwnerChecks.Safe (RxHistory.syscallDispatch call)) :
    Preserves Boundary (Leanux.dispatch call) :=
  Frames.boundary _ _ (RxHistory.syscallDispatch_erases call) keeps

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Dispatch
