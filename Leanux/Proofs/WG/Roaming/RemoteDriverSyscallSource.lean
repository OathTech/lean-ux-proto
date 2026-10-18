import Leanux.Proofs.WG.Roaming.RemoteDriverDispatchSource
import Leanux.Proofs.WG.Roaming.RemoteDriverTrafficFrames
import Leanux.Proofs.WG.Roaming.RemoteLifecycleSource
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Syscalls
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing

def route : PrefixM Event Unit := focus (RxHistory.audit routeIntoWg0Audit)
def cleanup : PrefixM Event Unit := focus (RxHistory.audit envNetnsCleanupAudit)

theorem route_preserves (entry : RemoteMap) : PrefixPreserves (Inv entry) Safe route :=
  focus_store entry _ _ (Appends.focus _ _ _) (RxHistory.audit_erases routeIntoWg0Audit_erases)
    routeIntoWg0_sameKernel

theorem route_projects : ProjectsPrefix rxEvent id route (RxHistory.audit routeIntoWg0Audit) :=
  Scheduler.focus_projects _ (Appends.focus _ _ _)

theorem route_appends : Appends route := Appends.focus _ _ _

theorem cleanup_preserves (entry : RemoteMap) : PrefixPreserves (Inv entry) Safe cleanup :=
  focus_retained entry _ _ (Appends.focus _ _ _)
    (RxHistory.audit_erases envNetnsCleanupAudit_erases) RemoteLifecycle.cleanup_native

theorem cleanup_projects : ProjectsPrefix rxEvent id cleanup (RxHistory.audit envNetnsCleanupAudit) :=
  Scheduler.focus_projects _ (Appends.focus _ _ _)

theorem cleanup_appends : Appends cleanup := Appends.focus _ _ _

def call (c : Syscall) : PrefixM Event Int :=
  Configuration.syscallWith (fun {_} a=>liftPrefix a) (Dispatch.call c) Deferred.send Deferred.idle
    route Deferred.afterXmit Deferred.afterAdvance cleanup c

theorem call_projects (c : Syscall) :
    ProjectsPrefix rxEvent id (call c) (RxHistory.syscall c) := by
  rw [Configuration.syscallRx_factor]
  exact Configuration.syscallWith_projects rxEvent (Dispatch.call_projects c)
    Deferred.send_projects Deferred.idle_projects route_projects Deferred.afterXmit_projects
    Deferred.afterAdvance_projects cleanup_projects c

theorem call_appends (c : Syscall) : Appends (call c) :=
  SyscallSource.appends c (Dispatch.call c) _ _ _ _ _ cleanup (Dispatch.call_appends c)
    Deferred.send_appends Deferred.idle_appends route_appends Deferred.afterXmit_appends
    Deferred.afterAdvance_appends cleanup_appends

theorem call_preserves (entry : RemoteMap) (c : Syscall) :
    PrefixPreserves (Inv entry) Safe (call c) :=
  SyscallSource.preserves (safe entry) (wg_store_inv entry) c (Dispatch.call c) _ _ _ _ _ cleanup
    (Dispatch.call_preserves entry c)
    (Deferred.send_preserves entry) (Deferred.idle_preserves entry) (route_preserves entry)
    (Deferred.afterXmit_preserves entry) (Deferred.afterAdvance_preserves entry) (cleanup_preserves entry)

theorem call_erases (c : Syscall) : ErasesPrefix (call c) (Leanux.syscall c) :=
  projection_erases (call_projects c) (RxHistory.syscall_erases c)

end Leanux.Proofs.WG.Roaming.RemoteDriver.Syscalls
