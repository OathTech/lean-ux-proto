import Leanux.Proofs.WG.Packets.DispatchTransmit
import Leanux.Proofs.WG.Packets.DeferredTransmit
import Leanux.Proofs.WG.Queues.NapiTransmit
import Leanux.Proofs.WG.Queues.SchedulerTransmit
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

/-! Every actual committed traffic, scheduler and return-to-user callback is
wired to the transmit observer. Configuration still uses its original routing
completion events; copied scheduler trials remain behind the original probe. -/
namespace Leanux.Proofs.WG.TransmitJoint.Actual
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps Configuration

def schedule (stack : Option Worker) : PrefixM Event Unit :=
  Scheduler.schedule Napi.encryptIteration Napi.decryptIteration Napi.softirq stack

def afterBatch : PrefixM Event Unit :=
  Traffic.afterBatch (Deferred.crypt schedule) (Deferred.send schedule) schedule

def dispatch (call : Syscall) : PrefixM Event Int :=
  Calls.dispatch (Deferred.crypt schedule) Napi.inline afterBatch (Deferred.idle schedule) call

def syscall (call : Syscall) : PrefixM Event Int :=
  syscallWith (fun {_} a => liftPrefix a) (dispatch call)
    (Deferred.send schedule) (Deferred.idle schedule)
    (oldRx (RxHistory.audit routeIntoWg0Audit)) (Deferred.afterXmit schedule)
    (Deferred.afterAdvance schedule) (oldRx (RxHistory.audit envNetnsCleanupAudit)) call

theorem schedule_preserves (initial : FlatTable × FlatTable) (stack : Option Worker) :
    PrefixPreserves (Inv initial) (Safe initial) (schedule stack) :=
  Scheduler.schedule_preserves initial _ _ _ (Napi.encryptIteration_checked initial)
    (Napi.decryptIteration_checked initial) (Napi.softirq_checked initial) stack

theorem schedule_projects (stack : Option Worker) :
    ProjectsPrefix RxTransmit.globalRx id (schedule stack) (RxHistory.schedule stack) :=
  Scheduler.schedule_projects _ _ _ Napi.encryptIteration_rx Napi.decryptIteration_rx Napi.softirq_rx stack

theorem schedule_appends (stack : Option Worker) : Appends (schedule stack) :=
  Scheduler.schedule_appends _ _ _ Napi.encryptIteration_append Napi.decryptIteration_append Napi.softirq_append stack

theorem afterBatch_preserves (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) afterBatch :=
  Traffic.afterBatch_preserves initial _ _ _
    (Deferred.crypt_preserves initial schedule (schedule_preserves initial none))
    (Deferred.send_preserves initial schedule (schedule_preserves initial none)) (schedule_preserves initial)

theorem afterBatch_projects : ProjectsPrefix RxTransmit.globalRx id afterBatch RxHistory.afterBatch :=
  Traffic.afterBatch_projects _ _ _ (Deferred.crypt_projects schedule (schedule_projects none))
    (Deferred.send_projects schedule (schedule_projects none)) schedule_projects

theorem afterBatch_appends : Appends afterBatch :=
  Traffic.afterBatch_appends _ _ _ (Deferred.crypt_appends schedule (schedule_appends none))
    (Deferred.send_appends schedule (schedule_appends none)) schedule_appends

theorem dispatch_preserves (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : SyscallAddressShape call) : PrefixPreserves (Inv initial) (Safe initial) (dispatch call) :=
  Calls.dispatch_preserves initial _ _ _ _
    (Deferred.crypt_preserves initial schedule (schedule_preserves initial none))
    (Napi.inline_checked initial) (afterBatch_preserves initial)
    (Deferred.idle_preserves initial schedule (schedule_preserves initial none)) call shape

theorem dispatch_projects (call : Syscall) :
    ProjectsPrefix RxTransmit.globalRx id (dispatch call) (RxHistory.syscallDispatch call) :=
  Calls.dispatch_projects _ _ _ _ (Deferred.crypt_projects schedule (schedule_projects none))
    Napi.inline_rx afterBatch_projects (Deferred.idle_projects schedule (schedule_projects none)) call

theorem dispatch_appends (call : Syscall) : Appends (dispatch call) :=
  Calls.dispatch_appends _ _ _ _ (Deferred.crypt_appends schedule (schedule_appends none))
    Napi.inline_append afterBatch_appends (Deferred.idle_appends schedule (schedule_appends none)) call

theorem syscall_preserves (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : SyscallAddressShape call) : PrefixPreserves (Inv initial) (Safe initial) (syscall call) :=
  SyscallSource.preserves (fun _ _ hi => hi.safe) Inv.store call _ _ _ _ _ _ _
    (dispatch_preserves initial call shape)
    (Deferred.send_preserves initial schedule (schedule_preserves initial none))
    (Deferred.idle_preserves initial schedule (schedule_preserves initial none))
    (oldRx_preserves initial _ _ (RxHistory.audit_erases routeIntoWg0Audit_erases)
      (ProjectedRetainsRoutingCall.of_same routeIntoWg0_routing))
    (Deferred.afterXmit_preserves initial schedule (schedule_preserves initial none))
    (Deferred.afterAdvance_preserves initial schedule (schedule_preserves initial none))
    (oldRx_preserves initial _ _ (RxHistory.audit_erases envNetnsCleanupAudit_erases) netnsCleanup_routing)

theorem syscall_projects (call : Syscall) :
    ProjectsPrefix RxTransmit.globalRx id (syscall call) (RxHistory.syscall call) :=
  syscallWith_projects _ (dispatch_projects call)
    (Deferred.send_projects schedule (schedule_projects none))
    (Deferred.idle_projects schedule (schedule_projects none))
    (oldRx_projects _ (Appends.focus _ _ _))
    (Deferred.afterXmit_projects schedule (schedule_projects none))
    (Deferred.afterAdvance_projects schedule (schedule_projects none))
    (oldRx_projects _ (Appends.focus _ _ _)) call

theorem syscall_appends (call : Syscall) : Appends (syscall call) :=
  SyscallSource.appends call _ _ _ _ _ _ _ (dispatch_appends call)
    (Deferred.send_appends schedule (schedule_appends none))
    (Deferred.idle_appends schedule (schedule_appends none)) (oldRx_appends _)
    (Deferred.afterXmit_appends schedule (schedule_appends none))
    (Deferred.afterAdvance_appends schedule (schedule_appends none)) (oldRx_appends _)

theorem syscall_erases (call : Syscall) : ErasesPrefix (syscall call) (Leanux.syscall call) := by
  intro w h
  have same := (congrArg Prod.fst (syscall_projects call w h)).symm.trans
    (RxHistory.syscall_erases call w (h.filterMap RxTransmit.globalRx))
  cases result : (runPrefix (syscall call) w h).1 <;>
    simpa only [result,Except.map,id_eq] using same

end Leanux.Proofs.WG.TransmitJoint.Actual
