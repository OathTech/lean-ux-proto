import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCryptSources
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductWork
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeferred
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTraffic
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteIngressAllocated

/-! The concrete scheduler, deferred workers and traffic wrappers have all
packet-source callbacks discharged. These are source contracts; initialized
administrative reset remains a separate obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver

theorem scheduled (stack : Option Worker) : Checked (scheduleObserved hooks stack) :=
  schedule encrypt_iteration decrypt_iteration receive_iteration
    (fun pid => tx_iter pid (tx_worker pid)) softirq stack

theorem received (msg : Key) (src : SkbSource) : Checked (receiveEntryObserved hooks msg src) :=
  pair_product (CompleteIngress.checked Safe account_safe msg src)
    (CompleteIngress.erases msg src) (CompleteIngress.allocated_product msg src)

theorem crypt : Checked (cryptObserved hooks) := Deferred.crypt scheduled

theorem sends : Checked (sendWorkersObserved hooks) := Deferred.sendWorkers scheduled scheduled_send

theorem after_xmit : Checked (afterXmitObserved hooks) := Deferred.afterXmit scheduled scheduled_send

theorem idle : Checked (idleTimersObserved hooks) := Deferred.idleTimers scheduled scheduled_send scheduled_clear

theorem advance : Checked (afterAdvanceObserved hooks) := Deferred.afterAdvance scheduled scheduled_send scheduled_clear

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Checked (injectObserved hooks family port msg tos ll dest) :=
  Traffic.inject scheduled received family port msg tos ll dest

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    Checked (floodObserved hooks count port family messages) :=
  Traffic.flood scheduled scheduled_send received count port family messages

theorem batch (items : List Env.BatchItem) : Checked (batchObserved hooks items) :=
  Traffic.batch scheduled scheduled_send received items

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Execution
