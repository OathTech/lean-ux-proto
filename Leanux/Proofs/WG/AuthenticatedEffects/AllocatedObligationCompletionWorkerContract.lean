import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedWhole
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxWorkerContract

/-! Discharge the actual worker's crypted callback at its selected pending
batch. Context, ledger, debts and physical locals come from that same entry;
the stopped contract retains the indexed completion or disposal frontier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations

def WorkerFailure : TxWorker.CryptFailure := fun ledger locals pid items head w history reason last =>
  ∃ context : Context, context.pid = pid ∧ context.locals = locals ∧ context.items = items ∧
    context.initialLedger = ledger ∧ context.births = births history ∧
    Owned context (.sending context.items) history ledger [] w ∧
    IndexedBatchStopped context ledger head.keypair w history reason last

theorem crypted_contract : TxWorker.CryptContract WorkerFailure := by
  intro ledger locals pid items head w history before pending _
  obtain ⟨context,peer,localEq,itemsEq,initial,domain,owned⟩ := TxSelection.selected_context before pending
  have checked := indexed_completedAndDisposed_cases head.keypair owned
  have source : completedAndDisposed context head.keypair = TxWorker.crypted pid items head := by
    simp only [completedAndDisposed,TxWorker.crypted,peer,itemsEq]
  rw [source] at checked
  cases performed : runPrefix (TxWorker.crypted pid items head) w history with
  | mk result last =>
    rw [performed] at checked
    cases result with
    | error reason => exact ⟨context,peer,localEq,itemsEq,initial,domain,owned,checked⟩
    | ok out =>
      obtain ⟨after,step,entry⟩ := IndexedBatchReturned.entry checked
      exact ⟨after,step,by simpa only [localEq] using entry⟩

/-- The complete actual TX worker now has no crypted-callback premise.
Its normal result returns the same caller locals and empty cleanup debts. -/
theorem transmit_checked (pid : PeerId)
    (before : StagedEntry.Inv history ledger [] locals w.wg) :
    match (runPrefix (CausalJournal.transmit pid) w history).1 with
    | .error stop => TxWorker.TransmitStop WorkerFailure ledger locals pid w history stop
        (runPrefix (CausalJournal.transmit pid) w history).2
    | .ok (_,v) => TxWorker.Returned ledger locals (runPrefix (CausalJournal.transmit pid) w history).2 v :=
  TxWorker.transmit_cases WorkerFailure crypted_contract pid before

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
