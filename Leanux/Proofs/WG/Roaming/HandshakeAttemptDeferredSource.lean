import Leanux.Proofs.WG.Roaming.HandshakeAttemptTransportSource
import Leanux.Proofs.WG.Queues.DeferredPreservation
/-! The existing deferred source factories carry an attempted-handshake
journal through the supplied receive-step observer. All other callbacks retain
their exact old RX observations. Validity is state-independent, so no physical
frame layer is needed. This is conditional on the supplied Receive contract;
it does not by itself identify that callback or establish initialization. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport.Deferred
open Leanux Leanux.WG Queues Lifetimes Leanux.Proofs.Logged
open RxHistory.DeferredSource
variable {Attempt : Type} {valid : List Attempt → Prop}

theorem atoms (valid : List Attempt → Prop) :
    RxHistory.DeferredSource.AtomContracts (fun h _ => Safe valid h) (Safe valid)
      (fun {_} g => old g) where
  sendOne := old_preserves valid _
  clearOne := old_preserves valid _
  drained := fun _ _ => old_preserves valid _
  saved := old_preserves valid _
  wheel := fun _ _ => old_preserves valid _
  stepComplete := fun _ => old_preserves valid _
  nothingDue := fun _ => old_preserves valid _
  timer := fun _ _ _ _ _ => old_preserves valid _
  placeholder := fun _ => old_preserves valid _
  idleDevice := old_preserves valid _
  noCrypt := old_preserves valid _
  timerWorker := fun _ => old_preserves valid _
  advance := fun _ => old_preserves valid _

def sendOne : PrefixM (Event Attempt) Unit := old (RxHistory.audit runOneSendWorkerAudit)
def crypt (r : Receive Attempt valid) : PrefixM (Event Attempt) Unit :=
  cryptWith (schedule r none)
def send (r : Receive Attempt valid) : PrefixM (Event Attempt) Unit :=
  sendWith (fun {_} g => old g) (schedule r none)
def afterXmit (r : Receive Attempt valid) : PrefixM (Event Attempt) Unit :=
  afterXmitWith (fun {_} g => old g) (crypt r) (send r)
def timers (r : Receive Attempt valid) (j : UInt64) : PrefixM (Event Attempt) Bool :=
  timersWith (fun {_} g => old g) (crypt r) j
def placeholder (r : Receive Attempt valid) (j : UInt64) : PrefixM (Event Attempt) Unit :=
  placeholderWith (fun {_} g => old g) (crypt r) (send r) j
def idle (r : Receive Attempt valid) : PrefixM (Event Attempt) Unit :=
  idleWith (fun {_} g => old g) (timers r) (placeholder r)
def afterAdvance (r : Receive Attempt valid) : PrefixM (Event Attempt) Unit :=
  afterAdvanceWith (fun {_} g => old g) (timers r) (placeholder r)
def deferred (r : Receive Attempt valid) (call : EnvDeferredCall) :
    PrefixM (Event Attempt) call.Result :=
  deferredWith (fun {_} g => old g) (crypt r) (send r) (afterXmit r) (timers r)
    (placeholder r) (idle r) (afterAdvance r) call

theorem sendOne_preserves (valid : List Attempt → Prop) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) sendOne := old_preserves valid _
theorem sendOne_projects :
    ProjectsPrefix rxEvent id (sendOne (Attempt := Attempt)) (RxHistory.audit runOneSendWorkerAudit) :=
  old_projects _ (Appends.focus _ _ _)
theorem sendOne_appends : Appends (sendOne (Attempt := Attempt)) := old_appends _

variable (r : Receive Attempt valid)

theorem crypt_projects : ProjectsPrefix rxEvent id (crypt r) RxHistory.runCryptWorkers :=
  RxHistory.DeferredSource.crypt_projects rxEvent _ _ (schedule_projects r none)
theorem send_projects : ProjectsPrefix rxEvent id (send r) RxHistory.runSendWorkers :=
  RxHistory.DeferredSource.send_projects rxEvent _ (fun {_} g => g) (fun g ha => old_projects g ha)
    _ _ (schedule_projects r none)
theorem afterXmit_projects : ProjectsPrefix rxEvent id (afterXmit r) RxHistory.afterXmit :=
  RxHistory.DeferredSource.afterXmit_projects rxEvent _ (fun {_} g => g) (fun g ha => old_projects g ha)
    _ _ _ _ (crypt_projects r) (send_projects r)
theorem timers_projects (j : UInt64) :
    ProjectsPrefix rxEvent id (timers r j) (RxHistory.runTimers j) :=
  RxHistory.DeferredSource.timers_projects rxEvent _ (fun {_} g => g) (fun g ha => old_projects g ha)
    _ _ (crypt_projects r) j
theorem placeholder_projects (j : UInt64) :
    ProjectsPrefix rxEvent id (placeholder r j) (RxHistory.runTimersPlaceholder j) :=
  RxHistory.DeferredSource.placeholder_projects rxEvent _ (fun {_} g => g) (fun g ha => old_projects g ha)
    _ _ _ _ (crypt_projects r) (send_projects r) j
theorem idle_projects : ProjectsPrefix rxEvent id (idle r) RxHistory.idleTimers :=
  RxHistory.DeferredSource.idle_projects rxEvent _ (fun {_} g => g) (fun g ha => old_projects g ha)
    _ _ _ _ (timers_projects r) (placeholder_projects r)
theorem afterAdvance_projects : ProjectsPrefix rxEvent id (afterAdvance r) RxHistory.afterAdvance :=
  RxHistory.DeferredSource.afterAdvance_projects rxEvent _ (fun {_} g => g) (fun g ha => old_projects g ha)
    _ _ _ _ (timers_projects r) (placeholder_projects r)
theorem deferred_projects (call : EnvDeferredCall) :
    ProjectsPrefix rxEvent id (deferred r call) (RxHistory.deferred call) :=
  RxHistory.DeferredSource.deferred_projects rxEvent _ (fun {_} g => g) (fun g ha => old_projects g ha)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ (crypt_projects r) (send_projects r) (afterXmit_projects r)
    (timers_projects r) (placeholder_projects r) (idle_projects r) (afterAdvance_projects r) call

theorem crypt_appends : Appends (crypt r) :=
  RxHistory.DeferredSource.crypt_appends _ (schedule_appends r none)
theorem send_appends : Appends (send r) :=
  RxHistory.DeferredSource.send_appends _ (fun g _ => old_appends g) _ (schedule_appends r none)
theorem afterXmit_appends : Appends (afterXmit r) :=
  RxHistory.DeferredSource.afterXmit_appends _ (fun g _ => old_appends g)
    _ (crypt_appends r) _ (send_appends r)
theorem timers_appends (j : UInt64) : Appends (timers r j) :=
  RxHistory.DeferredSource.timers_appends _ (fun g _ => old_appends g) _ (crypt_appends r) j
theorem placeholder_appends (j : UInt64) : Appends (placeholder r j) :=
  RxHistory.DeferredSource.placeholder_appends _ (fun g _ => old_appends g)
    _ (crypt_appends r) _ (send_appends r) j
theorem idle_appends : Appends (idle r) :=
  RxHistory.DeferredSource.idle_appends _ (fun g _ => old_appends g)
    _ (timers_appends r) _ (placeholder_appends r)
theorem afterAdvance_appends : Appends (afterAdvance r) :=
  RxHistory.DeferredSource.afterAdvance_appends _ (fun g _ => old_appends g)
    _ (timers_appends r) _ (placeholder_appends r)
theorem deferred_appends (call : EnvDeferredCall) : Appends (deferred r call) :=
  RxHistory.DeferredSource.deferred_appends _ (fun g _ => old_appends g)
    _ (crypt_appends r) _ (send_appends r) _ (afterXmit_appends r)
    _ (timers_appends r) _ (placeholder_appends r)
    _ (idle_appends r) _ (afterAdvance_appends r) call

theorem crypt_preserves : PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (crypt r) :=
  RxHistory.DeferredSource.crypt_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ (schedule_preserves r none)
theorem send_preserves : PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (send r) :=
  RxHistory.DeferredSource.send_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ (atoms valid) _ (schedule_preserves r none)
theorem afterXmit_preserves : PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (afterXmit r) :=
  RxHistory.DeferredSource.afterXmit_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ (atoms valid)
    _ (crypt_preserves r) _ (send_preserves r)
theorem timers_preserves (j : UInt64) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (timers r j) :=
  RxHistory.DeferredSource.timers_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ (atoms valid) _ (crypt_preserves r) j
theorem placeholder_preserves (j : UInt64) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (placeholder r j) :=
  RxHistory.DeferredSource.placeholder_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ (atoms valid)
    _ (crypt_preserves r) _ (send_preserves r) j
theorem idle_preserves : PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (idle r) :=
  RxHistory.DeferredSource.idle_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ (atoms valid)
    _ (timers_preserves r) _ (placeholder_preserves r)
theorem afterAdvance_preserves : PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (afterAdvance r) :=
  RxHistory.DeferredSource.afterAdvance_preserves (I := fun h _ => Safe valid h) (S := Safe valid)
    (fun _ _ pre => pre) (fun _ _ _ _ pre => pre) _ (atoms valid)
    _ (timers_preserves r) _ (placeholder_preserves r)
theorem deferred_preserves (call : EnvDeferredCall) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (deferred r call) :=
  RxHistory.DeferredSource.deferred_preserves _ (atoms valid) _ _ _ _ _ _ _
    (crypt_preserves r) (send_preserves r) (afterXmit_preserves r)
    (timers_preserves r) (placeholder_preserves r) (idle_preserves r) (afterAdvance_preserves r) call

theorem deferred_erases (call : EnvDeferredCall) : ErasesPrefix (deferred r call) call.original :=
  projects_erases (deferred_projects r call) (RxHistory.deferred_erases call)

/-- Source erasures include original Stop outcomes and do not assume a normal return. -/
theorem sendOne_erases :
    ErasesPrefix (sendOne (Attempt := Attempt)) Env.runOneSendWorker :=
  projects_erases sendOne_projects (RxHistory.audit_erases runOneSendWorkerAudit_erases)
theorem crypt_erases : ErasesPrefix (crypt r) Env.runCryptWorkers :=
  projects_erases (crypt_projects r) RxHistory.runCryptWorkers_erases
theorem send_erases : ErasesPrefix (send r) Env.runSendWorkers :=
  projects_erases (send_projects r) RxHistory.runSendWorkers_erases
theorem afterXmit_erases : ErasesPrefix (afterXmit r) Env.afterXmit :=
  projects_erases (afterXmit_projects r) RxHistory.afterXmit_erases
theorem timers_erases (j : UInt64) : ErasesPrefix (timers r j) (Env.runTimers j) :=
  projects_erases (timers_projects r j) (RxHistory.runTimers_erases j)
theorem placeholder_erases (j : UInt64) :
    ErasesPrefix (placeholder r j) (Env.runTimersPlaceholder j) :=
  projects_erases (placeholder_projects r j) (RxHistory.runTimersPlaceholder_erases j)
theorem idle_erases : ErasesPrefix (idle r) Env.idleTimers :=
  projects_erases (idle_projects r) RxHistory.idleTimers_erases
theorem afterAdvance_erases : ErasesPrefix (afterAdvance r) Env.afterAdvance :=
  projects_erases (afterAdvance_projects r) RxHistory.afterAdvance_erases

end Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport.Deferred
