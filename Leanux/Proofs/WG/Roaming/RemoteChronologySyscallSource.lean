import Leanux.Proofs.WG.Roaming.RemoteChronologyOuterSource
import Leanux.Proofs.WG.Roaming.RemoteDriverSyscallSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

namespace Dispatch
theorem retained_preserves (entry : RemoteMap) (call : Syscall) (selected : DispatchRetained call) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.focus (RxHistory.syscallDispatch call)) := by
  apply focus_retained entry _ _ (RxHistory.syscallDispatch_appends call)
    (RxHistory.syscallDispatch_erases call) ?_ (fun before => RemoteDispatch.retained before call selected)
  cases call <;> first
    | exact Poll.audit_inert _
    | cases selected

theorem call_preserves (entry : RemoteMap) (call : Syscall) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Dispatch.call call) :=
  dispatchWith_preserves _ _ _ _ _ _ _ _ _
    (retained_preserves entry) (Outer.set_preserves entry) (Outer.create_preserves entry)
    (Outer.delete_preserves entry) (Outer.xmit_preserves entry) (Outer.inject_preserves entry)
    (Traffic.flood_preserves entry) (Traffic.batch_preserves entry) (Outer.observe_preserves entry) call
end Dispatch

namespace Syscalls
theorem route_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Syscalls.route :=
  audit_store entry _ _ routeIntoWg0Audit_erases routeIntoWg0_sameKernel

theorem cleanup_preserves (entry : RemoteMap) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe RemoteDriver.Syscalls.cleanup :=
  focus_audit entry _ _ envNetnsCleanupAudit_erases RemoteLifecycle.cleanup_native

theorem call_preserves (entry : RemoteMap) (call : Syscall) :
    PrefixPreserves (Inv entry) RemoteDriver.Safe (RemoteDriver.Syscalls.call call) :=
  SyscallSource.preserves (safe entry) (wg_store_inv entry) call (RemoteDriver.Dispatch.call call)
    _ _ _ _ _ RemoteDriver.Syscalls.cleanup
    (Dispatch.call_preserves entry call)
    (Deferred.send_preserves entry) (Deferred.idle_preserves entry) (route_preserves entry)
    (Deferred.afterXmit_preserves entry) (Deferred.afterAdvance_preserves entry) (cleanup_preserves entry)
end Syscalls

end Leanux.Proofs.WG.Roaming.RemoteChronology.Driver
