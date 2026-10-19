import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionSequence
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteWorker

/-! The exact scoped completion and disposal caller retains logical prefixes
beside its original source frontier. Context assembly uses the same selected
entry, pending allocation tickets and canonical ledger as the worker result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {Safe : List CausalJournal.Event → Prop}

theorem completed_and_disposed (key : KeypairId) (accountSafe : AccountSafe Safe)
    (before : Owned context (.sending context.items) history ledger [] w)
    (complete : Complete history ledger) (earlier : All Safe history) :
    All Safe (runPrefix (completedAndDisposed context key) w history).2 ∧
      match (runPrefix (completedAndDisposed context key) w history).1 with
      | .error reason => Converse.BatchStopped context ledger key w history reason
          (runPrefix (completedAndDisposed context key) w history).2
      | .ok (value,v) => Converse.BatchReturned context ledger key w history
          (runPrefix (completedAndDisposed context key) w history).2 value v := by
  have checked := Converse.completedAndDisposed_cases key before complete
  refine ⟨?_,checked⟩
  have start := Converse.Sending.start before (LocalDebts.empty context context.items) complete
  obtain ⟨_,_,result⟩ := complete_scoped context ledger [] accountSafe w history ⟨start,earlier⟩
  unfold completedAndDisposed
  rw [runPrefix_bind]
  cases completed : runPrefix
      (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
        CausalJournal.completionOps context.pid context.items) w history with
  | mk outcome cutHistory =>
    rw [completed] at result
    cases outcome with
    | error reason => exact result.2
    | ok out =>
      obtain ⟨ignored,cutWorld⟩ := out
      cases ignored
      obtain ⟨after,debts,_,owned,localDebts,completeCut⟩ := result.1
      obtain ⟨_,_,disposed⟩ := dispose context key after debts accountSafe cutWorld cutHistory
        ⟨⟨owned.ready_to_free,localDebts,completeCut⟩,result.2⟩
      cases run : (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) cutWorld cutHistory).1 with
      | error reason => rw [run] at disposed; exact disposed.2
      | ok value => rw [run] at disposed; exact disposed.2

theorem crypted (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (items : List SkbId) (head : DataPacket) (w : World) (history : List CausalJournal.Event)
    (accountSafe : AccountSafe Safe)
    (before : CompleteCarrier.Accounted history ledger [] (⟨.selected,pid,items⟩ :: locals) w.wg)
    (pending : CreateDisposal.PendingBatch history ledger items) (earlier : All Safe history) :
    All Safe (runPrefix (TxWorker.crypted pid items head) w history).2 ∧
      match (runPrefix (TxWorker.crypted pid items head) w history).1 with
      | .error reason => Converse.WorkerFailure ledger locals pid items head w history reason
          (runPrefix (TxWorker.crypted pid items head) w history).2
      | .ok (value,v) => Converse.WorkerReturned ledger locals pid items head w history
          (runPrefix (TxWorker.crypted pid items head) w history).2 value v := by
  obtain ⟨context,peer,localEq,itemsEq,initial,domain,owned⟩ := TxSelection.selected_context before.entry pending
  obtain ⟨prefixSafe,checked⟩ := completed_and_disposed head.keypair accountSafe owned before.complete earlier
  have source : completedAndDisposed context head.keypair = TxWorker.crypted pid items head := by
    simp only [completedAndDisposed,TxWorker.crypted,peer,itemsEq]
  rw [source] at prefixSafe checked
  refine ⟨prefixSafe,?_⟩
  cases performed : runPrefix (TxWorker.crypted pid items head) w history with
  | mk result last =>
    rw [performed] at checked
    cases result with
    | error reason => exact ⟨context,peer,localEq,itemsEq,initial,domain,owned,before.complete,checked⟩
    | ok out => exact ⟨context,peer,localEq,itemsEq,initial,domain,owned,before.complete,checked⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
