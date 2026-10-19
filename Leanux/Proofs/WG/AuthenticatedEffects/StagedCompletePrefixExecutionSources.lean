import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProductActive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProductWork
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDeferred
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixTraffic

/-! Concrete scheduling, deferred work and traffic retain every logical
journal prefix. Every worker and packet-source callback is discharged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver

theorem scheduled (stack : Option Worker) : Checked (scheduleObserved hooks stack) :=
  schedule encrypt_iteration decrypt_iteration receive_iteration
    (fun pid => tx_iter pid (Completion.tx_worker pid)) softirq stack

theorem crypt : Checked (cryptObserved hooks) := Deferred.crypt scheduled

theorem sends : Checked (sendWorkersObserved hooks) := Deferred.sendWorkers scheduled scheduled_send

theorem after_xmit : Checked (afterXmitObserved hooks) := Deferred.afterXmit scheduled scheduled_send

theorem idle : Checked (idleTimersObserved hooks) := Deferred.idleTimers timer scheduled scheduled_send scheduled_clear

theorem advance : Checked (afterAdvanceObserved hooks) := Deferred.afterAdvance timer scheduled scheduled_send scheduled_clear

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Checked (injectObserved hooks family port msg tos ll dest) :=
  Traffic.inject scheduled received family port msg tos ll dest

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    Checked (floodObserved hooks count port family messages) :=
  Traffic.flood scheduled scheduled_send received inline_poll count port family messages

theorem batch (items : List Env.BatchItem) : Checked (batchObserved hooks items) :=
  Traffic.batch scheduled scheduled_send received inline_poll transmit items

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product.Execution
