import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispose

/-! The concrete crypted callback retains the successful scoped completion
that starts disposal and its full cleanup/repayment interval. A Stop inside
sending still carries the existing frontier; its deeper entry-to-cut anchor
is not claimed here. The global caller-entry anchor also remains open. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch
open AllocatedObligation.CompletionBatch.Converse

abbrev scopedCompletion (context : Context) :=
  CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
    CausalJournal.completionOps context.pid context.items

inductive CryptedInterval (context : Context) (initial : Ledger) (key : KeypairId)
    (w : World) (history : List CausalJournal.Event) :
    Except Stop (Bool × World) → List CausalJournal.Event → Prop where
  | sendingStopped (reason : Stop) (last : List CausalJournal.Event)
      (failed : runPrefix (scopedCompletion context) w history = (.error reason,last))
      (frontier : Converse.SendingStopped context initial [] reason last) :
      CryptedInterval context initial key w history (.error reason) last
  | disposing (ledger : Ledger) (debts : List CleanupDebt) (cutWorld : World)
      (cutHistory : List CausalJournal.Event)
      (completed : runPrefix (scopedCompletion context) w history = (.ok ((),cutWorld),cutHistory))
      (trace : SendSettlements context initial [] ledger debts)
      (owned : Owned context (.freeing context.items) cutHistory ledger debts cutWorld)
      (localDebts : LocalDebts context context.items debts) (complete : Complete cutHistory ledger)
      (interval : DisposalInterval context ledger debts key cutWorld cutHistory result last) :
      CryptedInterval context initial key w history result last

/-- The actual crypted source chooses its branch. After successful sending,
the cleanup path begins at precisely that source output and survives a later
repayment Stop with the same ledger and active-local indices. -/
theorem crypted_interval (key : KeypairId)
    (before : Owned context (.sending context.items) history ledger [] w)
    (complete : Complete history ledger) :
    CryptedInterval context ledger key w history
      (runPrefix (completedAndDisposed context key) w history).1
      (runPrefix (completedAndDisposed context key) w history).2 := by
  have start := Sending.start before (LocalDebts.empty context context.items) complete
  obtain ⟨_,_,checked⟩ := completeScoped_checked context ledger [] w history start
  unfold completedAndDisposed
  rw [runPrefix_bind]
  cases completed : runPrefix
      (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
        CausalJournal.completionOps context.pid context.items) w history with
  | mk outcome cutHistory =>
    rw [completed] at checked
    cases outcome with
    | error reason => exact .sendingStopped reason cutHistory completed checked
    | ok out =>
      obtain ⟨ignored,cutWorld⟩ := out
      cases ignored
      obtain ⟨after,debts,trace,owned,localDebts,completeCut⟩ := checked
      exact .disposing after debts cutWorld cutHistory completed trace owned.ready_to_free localDebts
        completeCut (disposal_interval key owned.ready_to_free localDebts completeCut)

theorem CryptedInterval.run
    (interval : CryptedInterval context ledger key w history result last) :
    runPrefix (completedAndDisposed context key) w history = (result,last) := by
  cases interval with
  | sendingStopped reason last failed =>
    change runPrefix (scopedCompletion context >>= fun _ => _) w history = _
    rw [runPrefix_bind,failed]
  | disposing _ _ _ _ completed _ _ _ _ interval =>
    change runPrefix (scopedCompletion context >>= fun _ => _) w history = _
    rw [runPrefix_bind,completed]
    exact interval.run

def WorkerInterval (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (items : List SkbId) (head : DataPacket) (w : World) (history : List CausalJournal.Event)
    (result : Except Stop (Bool × World)) (last : List CausalJournal.Event) : Prop :=
  ∃ context : Context, context.pid = pid ∧ context.locals = locals ∧ context.items = items ∧
    context.initialLedger = ledger ∧ context.births = births history ∧
    Owned context (.sending context.items) history ledger [] w ∧ Complete history ledger ∧
    CryptedInterval context ledger head.keypair w history result last

/-- The selected caller supplies the actual entry state. The concrete source
chooses all later states; no endpoint state or completed-call premise is added. -/
theorem worker_interval (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (before : StagedEntry.Inv history ledger [] (⟨.selected,pid,items⟩ :: locals) w.wg)
    (complete : Complete history ledger) (pending : CreateDisposal.PendingBatch history ledger items) :
    WorkerInterval ledger locals pid items head w history
      (runPrefix (TxWorker.crypted pid items head) w history).1
      (runPrefix (TxWorker.crypted pid items head) w history).2 := by
  obtain ⟨context,peer,localEq,itemsEq,initial,domain,owned⟩ := TxSelection.selected_context before pending
  have interval := crypted_interval head.keypair owned complete
  have source : completedAndDisposed context head.keypair = TxWorker.crypted pid items head := by
    simp only [completedAndDisposed,TxWorker.crypted,peer,itemsEq]
  rw [source] at interval
  exact ⟨context,peer,localEq,itemsEq,initial,domain,owned,complete,interval⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
