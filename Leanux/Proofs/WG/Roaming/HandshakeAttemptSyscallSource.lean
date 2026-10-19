import Leanux.Proofs.WG.Roaming.HandshakeAttemptOuterSource
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport
open Leanux Leanux.WG Leanux.Proofs.Logged Queues Lifetimes Configuration
variable {Attempt : Type} {valid : List Attempt → Prop}

namespace Syscalls

def call (r : Receive Attempt valid) (c : Syscall) : PrefixM (Event Attempt) Int :=
  Configuration.syscallWith (fun {_} a=>liftPrefix a) (Dispatch.call r c)
    (Deferred.send r) (Deferred.idle r) (old (RxHistory.audit routeIntoWg0Audit))
    (Deferred.afterXmit r) (Deferred.afterAdvance r) (old (RxHistory.audit envNetnsCleanupAudit)) c

theorem call_projects (r : Receive Attempt valid) (c : Syscall) :
    ProjectsPrefix rxEvent id (call r c) (RxHistory.syscall c) := by
  rw [Configuration.syscallRx_factor]
  exact Configuration.syscallWith_projects rxEvent (Dispatch.call_projects r c)
    (Deferred.send_projects r) (Deferred.idle_projects r)
    (old_projects _ (Appends.focus _ _ _))
    (Deferred.afterXmit_projects r) (Deferred.afterAdvance_projects r)
    (old_projects _ (Appends.focus _ _ _)) c

theorem call_appends (r : Receive Attempt valid) (c : Syscall) : Appends (call r c) :=
  SyscallSource.appends c (Dispatch.call r c) _ _ _ _ _ _ (Dispatch.call_appends r c)
    (Deferred.send_appends r) (Deferred.idle_appends r) (old_appends _)
    (Deferred.afterXmit_appends r) (Deferred.afterAdvance_appends r) (old_appends _)

theorem call_preserves (r : Receive Attempt valid) (c : Syscall) :
    PrefixPreserves (fun h _=>Safe valid h) (Safe valid) (call r c) :=
  SyscallSource.preserves (I:=fun h _=>Safe valid h) (S:=Safe valid)
    (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) c (Dispatch.call r c) _ _ _ _ _ _
    (Dispatch.call_preserves r c) (Deferred.send_preserves r) (Deferred.idle_preserves r)
    (old_preserves valid _) (Deferred.afterXmit_preserves r)
    (Deferred.afterAdvance_preserves r) (old_preserves valid _)

theorem call_erases (r : Receive Attempt valid) (c : Syscall) :
    ErasesPrefix (call r c) (Leanux.syscall c) :=
  projects_erases (call_projects r c) (RxHistory.syscall_erases c)

end Syscalls


end Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport
