import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxActivationEntry
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkerCompletionAccounted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductTx

/-! Failure alternatives of the actual TX activation. A transmit failure
retains both the original worker frontier and its matched fixed-prefix
classification. A later reschedule failure keeps the actual completed worker
and its ledger transition, rather than reusing the pre-transmit account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxActivation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations CompleteCarrier AllocatedObligation CompletionBatch

inductive Stopped (pid : PeerId) (w : World) (history : List CausalJournal.Event)
    (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | ahead (performed : runPrefix (entryPrefix pid) w history = (.error reason,last))
      (safe : CompleteProduct.Safe last)
  | transmit (ledger : Ledger) (u : World) (middle : List CausalJournal.Event)
      (path : EntryPath pid w history ledger u middle)
      (performed : runPrefix (CausalJournal.transmit pid) u middle = (.error reason,last))
      (original : Converse.Worker.TransmitStop ledger [] pid u middle reason last)
      (matched : WorkerCompletion.WorkerStop ledger [] pid u middle reason last)
  | reschedule (ledger : Ledger) (u : World) (middle : List CausalJournal.Event)
      (path : EntryPath pid w history ledger u middle)
      (v : World) (after : List CausalJournal.Event)
      (transmitted : runPrefix (CausalJournal.transmit pid) u middle = (.ok (true,v),after))
      (returned : Converse.Worker.Returned ledger [] after v)
      (carrier : CompleteProduct.Carrier after v)
      (performed : runPrefix (continuation true) v after = (.error reason,last))

theorem Stopped.source_failed (stopped : Stopped pid w history reason last)
    (activation : Activation) (worker : activation.worker = .txWorker)
    (peer : activation.pid = some pid) :
    runPrefix (Driver.iterationObserved CausalJournal.hooks activation) w history = (.error reason,last) := by
  cases stopped with
  | ahead performed _ => exact entry_failed activation pid worker peer performed
  | transmit _ _ _ path performed _ _ =>
    rw [path.iteration_run activation worker peer,tail,runPrefix_bind,performed]
  | reschedule _ _ _ path _ _ transmitted _ _ performed =>
    rw [path.iteration_run activation worker peer,tail,runPrefix_bind,transmitted]
    exact performed

/-- The prefix and both callback outcomes are obtained from their actual
runs. There is no incoming worker or crypt-ahead preservation contract. -/
theorem iteration_failed (activation : Activation) (pid : PeerId)
    (worker : activation.worker = .txWorker) (peer : activation.pid = some pid)
    (before : CompleteProduct.Carrier history w)
    (failed : runPrefix (Driver.iterationObserved CausalJournal.hooks activation) w history = (.error reason,last)) :
    Stopped pid w history reason last := by
  rcases entry_cases activation pid worker peer before with early | entered
  · obtain ⟨stop,after,performed,native,safe⟩ := early
    rw [failed] at native
    cases native
    exact .ahead performed safe
  · obtain ⟨ledger,u,middle,path,native⟩ := entered
    rw [native,tail,runPrefix_bind] at failed
    cases transmitted : runPrefix (CausalJournal.transmit pid) u middle with
    | mk outcome after =>
      rw [transmitted] at failed
      cases outcome with
      | error stop =>
        cases failed
        obtain ⟨original,matched⟩ := WorkerCompletion.worker_failed pid path.accounted transmitted
        exact .transmit ledger u middle path transmitted original matched
      | ok out =>
        obtain ⟨more,v⟩ := out
        have returned := Converse.Worker.transmit_cases pid path.accounted
        rw [transmitted] at returned
        obtain ⟨_,_,_,carrier⟩ := CompleteProduct.tx_worker pid u middle path.carrier
        simp only [CausalJournal.hooks,transmitted] at carrier
        cases more with
        | false => simp only [continuation,Bool.not_false,↓reduceIte,runPrefix_pure] at failed; cases failed
        | true => exact .reschedule ledger u middle path v after transmitted returned carrier failed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxActivation
