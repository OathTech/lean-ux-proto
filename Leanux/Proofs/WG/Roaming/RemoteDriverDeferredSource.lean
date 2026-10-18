import Leanux.Proofs.WG.Roaming.RemoteDriverSchedulerSource
import Leanux.Proofs.WG.Roaming.RemoteDriverDeferredNativeSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Deferred
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open RxHistory.DeferredSource

def sendOne : PrefixM Event Unit := focus (RxHistory.audit runOneSendWorkerAudit)
def crypt : PrefixM Event Unit := cryptWith (Scheduler.schedule none)
def send : PrefixM Event Unit := sendWith (fun {_} g=>focus g) (Scheduler.schedule none)
def afterXmit : PrefixM Event Unit := afterXmitWith (fun {_} g=>focus g) crypt send
def timers (j : UInt64) : PrefixM Event Bool := timersWith (fun {_} g=>focus g) crypt j
def placeholder (j : UInt64) : PrefixM Event Unit := placeholderWith (fun {_} g=>focus g) crypt send j
def idle : PrefixM Event Unit := idleWith (fun {_} g=>focus g) timers placeholder
def afterAdvance : PrefixM Event Unit := afterAdvanceWith (fun {_} g=>focus g) timers placeholder
def deferred (call : EnvDeferredCall) : PrefixM Event call.Result :=
  deferredWith (fun {_} g=>focus g) crypt send afterXmit timers placeholder idle afterAdvance call

theorem sendOne_preserves (entry : RemoteMap) : PrefixPreserves (Inv entry) Safe sendOne :=
  (atoms entry).sendOne

theorem sendOne_projects : ProjectsPrefix rxEvent id sendOne (RxHistory.audit runOneSendWorkerAudit) :=
  Scheduler.focus_projects _ (Appends.focus _ _ _)

theorem sendOne_appends : Appends sendOne := Appends.focus _ _ _

theorem crypt_projects : ProjectsPrefix rxEvent id crypt RxHistory.runCryptWorkers :=
  RxHistory.DeferredSource.crypt_projects rxEvent _ _ (Scheduler.schedule_projects none)

theorem send_projects : ProjectsPrefix rxEvent id send RxHistory.runSendWorkers :=
  RxHistory.DeferredSource.send_projects rxEvent _ (fun {_} g=>g) (fun g ha=>Scheduler.focus_projects g ha)
    _ _ (Scheduler.schedule_projects none)

theorem afterXmit_projects : ProjectsPrefix rxEvent id afterXmit RxHistory.afterXmit :=
  RxHistory.DeferredSource.afterXmit_projects rxEvent _ (fun {_} g=>g) (fun g ha=>Scheduler.focus_projects g ha)
    _ _ _ _ crypt_projects send_projects

theorem timers_projects (j : UInt64) : ProjectsPrefix rxEvent id (timers j) (RxHistory.runTimers j) :=
  RxHistory.DeferredSource.timers_projects rxEvent _ (fun {_} g=>g) (fun g ha=>Scheduler.focus_projects g ha)
    _ _ crypt_projects j

theorem placeholder_projects (j : UInt64) :
    ProjectsPrefix rxEvent id (placeholder j) (RxHistory.runTimersPlaceholder j) :=
  RxHistory.DeferredSource.placeholder_projects rxEvent _ (fun {_} g=>g) (fun g ha=>Scheduler.focus_projects g ha)
    _ _ _ _ crypt_projects send_projects j

theorem idle_projects : ProjectsPrefix rxEvent id idle RxHistory.idleTimers :=
  RxHistory.DeferredSource.idle_projects rxEvent _ (fun {_} g=>g) (fun g ha=>Scheduler.focus_projects g ha)
    _ _ _ _ timers_projects placeholder_projects

theorem afterAdvance_projects : ProjectsPrefix rxEvent id afterAdvance RxHistory.afterAdvance :=
  RxHistory.DeferredSource.afterAdvance_projects rxEvent _ (fun {_} g=>g) (fun g ha=>Scheduler.focus_projects g ha)
    _ _ _ _ timers_projects placeholder_projects

theorem deferred_projects (call : EnvDeferredCall) :
    ProjectsPrefix rxEvent id (deferred call) (RxHistory.deferred call) :=
  RxHistory.DeferredSource.deferred_projects rxEvent _ (fun {_} g=>g) (fun g ha=>Scheduler.focus_projects g ha)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ crypt_projects send_projects afterXmit_projects
    timers_projects placeholder_projects idle_projects afterAdvance_projects call

theorem crypt_appends : Appends crypt :=
  RxHistory.DeferredSource.crypt_appends _ (Scheduler.schedule_appends none)

theorem send_appends : Appends send :=
  RxHistory.DeferredSource.send_appends _ (fun g _=>Appends.focus _ _ g) _ (Scheduler.schedule_appends none)

theorem afterXmit_appends : Appends afterXmit :=
  RxHistory.DeferredSource.afterXmit_appends _ (fun g _=>Appends.focus _ _ g)
    _ crypt_appends _ send_appends

theorem timers_appends (j : UInt64) : Appends (timers j) :=
  RxHistory.DeferredSource.timers_appends _ (fun g _=>Appends.focus _ _ g) _ crypt_appends j

theorem placeholder_appends (j : UInt64) : Appends (placeholder j) :=
  RxHistory.DeferredSource.placeholder_appends _ (fun g _=>Appends.focus _ _ g)
    _ crypt_appends _ send_appends j

theorem idle_appends : Appends idle :=
  RxHistory.DeferredSource.idle_appends _ (fun g _=>Appends.focus _ _ g)
    _ timers_appends _ placeholder_appends

theorem afterAdvance_appends : Appends afterAdvance :=
  RxHistory.DeferredSource.afterAdvance_appends _ (fun g _=>Appends.focus _ _ g)
    _ timers_appends _ placeholder_appends

theorem deferred_appends (call : EnvDeferredCall) : Appends (deferred call) :=
  RxHistory.DeferredSource.deferred_appends _ (fun g _=>Appends.focus _ _ g)
    _ crypt_appends _ send_appends _ afterXmit_appends _ timers_appends _ placeholder_appends
    _ idle_appends _ afterAdvance_appends call

theorem deferred_erases (call : EnvDeferredCall) :
    ErasesPrefix (deferred call) call.original :=
  projection_erases (deferred_projects call) (RxHistory.deferred_erases call)

section
variable (entry : RemoteMap)

theorem crypt_preserves : PrefixPreserves (Inv entry) Safe crypt :=
  RxHistory.DeferredSource.crypt_preserves (safe entry) (store_inv entry) _ (Scheduler.schedule_preserves entry none)

theorem send_preserves : PrefixPreserves (Inv entry) Safe send :=
  RxHistory.DeferredSource.send_preserves (safe entry) (store_inv entry) _ (atoms entry) _ (Scheduler.schedule_preserves entry none)

theorem afterXmit_preserves : PrefixPreserves (Inv entry) Safe afterXmit :=
  RxHistory.DeferredSource.afterXmit_preserves (safe entry) (store_inv entry) _ (atoms entry)
    _ (crypt_preserves entry) _ (send_preserves entry)

theorem timers_preserves (j : UInt64) : PrefixPreserves (Inv entry) Safe (timers j) :=
  RxHistory.DeferredSource.timers_preserves (safe entry) (store_inv entry) _ (atoms entry)
    _ (crypt_preserves entry) j

theorem placeholder_preserves (j : UInt64) : PrefixPreserves (Inv entry) Safe (placeholder j) :=
  RxHistory.DeferredSource.placeholder_preserves (safe entry) (store_inv entry) _ (atoms entry)
    _ (crypt_preserves entry) _ (send_preserves entry) j

theorem idle_preserves : PrefixPreserves (Inv entry) Safe idle :=
  RxHistory.DeferredSource.idle_preserves (safe entry) (store_inv entry) _ (atoms entry)
    _ (timers_preserves entry) _ (placeholder_preserves entry)

theorem afterAdvance_preserves : PrefixPreserves (Inv entry) Safe afterAdvance :=
  RxHistory.DeferredSource.afterAdvance_preserves (safe entry) (store_inv entry) _ (atoms entry)
    _ (timers_preserves entry) _ (placeholder_preserves entry)

theorem deferred_preserves (call : EnvDeferredCall) : PrefixPreserves (Inv entry) Safe (deferred call) :=
  RxHistory.DeferredSource.deferred_preserves _ (atoms entry) _ _ _ _ _ _ _
    (crypt_preserves entry) (send_preserves entry) (afterXmit_preserves entry)
    (timers_preserves entry) (placeholder_preserves entry)
    (idle_preserves entry) (afterAdvance_preserves entry) call
end
end Leanux.Proofs.WG.Roaming.RemoteDriver.Deferred
