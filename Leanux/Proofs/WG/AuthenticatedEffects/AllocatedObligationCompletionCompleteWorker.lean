import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteWhole

/-! The actual crypted worker callback preserves both directions of terminal
accounting on one ledger. The result retains its exact context and source
settlement chain, with a projection to the paired idle entry for callers. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete

def WorkerFailure : TxWorker.CryptFailure := fun ledger locals pid items head w history reason last =>
  ∃ context : Context, context.pid = pid ∧ context.locals = locals ∧ context.items = items ∧
    context.initialLedger = ledger ∧ context.births = births history ∧
    Owned context (.sending context.items) history ledger [] w ∧ Complete history ledger ∧
    BatchStopped context ledger head.keypair w history reason last

def WorkerReturned (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId) (items : List SkbId)
    (head : DataPacket) (w : World) (history last : List CausalJournal.Event) (value : Bool) (v : World) : Prop :=
  ∃ context : Context, context.pid = pid ∧ context.locals = locals ∧ context.items = items ∧
    context.initialLedger = ledger ∧ context.births = births history ∧
    Owned context (.sending context.items) history ledger [] w ∧ Complete history ledger ∧
    BatchReturned context ledger head.keypair w history last value v

def CryptContract (failure : TxWorker.CryptFailure) : Prop :=
  ∀ ledger locals pid items head w history,
    StagedEntry.Inv history ledger [] (⟨.selected,pid,items⟩ :: locals) w.wg →
    Complete history ledger → CreateDisposal.PendingBatch history ledger items → head.state = .crypted →
    match (runPrefix (TxWorker.crypted pid items head) w history).1 with
    | .error reason => failure ledger locals pid items head w history reason
        (runPrefix (TxWorker.crypted pid items head) w history).2
    | .ok (value,v) => WorkerReturned ledger locals pid items head w history
        (runPrefix (TxWorker.crypted pid items head) w history).2 value v

theorem crypted_contract : CryptContract WorkerFailure := by
  intro ledger locals pid items head w history before complete pending _
  obtain ⟨context,peer,localEq,itemsEq,initial,domain,owned⟩ := TxSelection.selected_context before pending
  have checked := completedAndDisposed_cases head.keypair owned complete
  have source : completedAndDisposed context head.keypair = TxWorker.crypted pid items head := by
    simp only [completedAndDisposed,TxWorker.crypted,peer,itemsEq]
  rw [source] at checked
  cases performed : runPrefix (TxWorker.crypted pid items head) w history with
  | mk result last =>
    rw [performed] at checked
    cases result with
    | error reason => exact ⟨context,peer,localEq,itemsEq,initial,domain,owned,complete,checked⟩
    | ok out => exact ⟨context,peer,localEq,itemsEq,initial,domain,owned,complete,checked⟩

theorem WorkerReturned.entry
    (returned : WorkerReturned ledger locals pid items head w history last value v) :
    ∃ after, Staged.Obligations.Step ledger after ∧
      StagedEntry.Inv last after [] locals v.wg ∧ Complete last after := by
  obtain ⟨context,_,localEq,_,_,_,_,_,result⟩ := returned
  obtain ⟨after,step,entry,complete⟩ := BatchReturned.entry result
  exact ⟨after,step,(by simpa only [localEq] using entry),complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
