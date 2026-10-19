import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxDispatch

/-! Actual TX worker source transport with Entry and terminal completeness
on the same ledger. Normal paths retain their branch witness; stopped paths
retain the reached native cut and source run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Worker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open StagedEntry.CompleteCarrier StagedTerminalComplete TxWorker
open Staged.Obligations CreateDisposal
set_option pp.structureInstances false

inductive AfterReadStop (ledger : Ledger) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (w : World)
    (history : List CausalJournal.Event) (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | drop
      (entry : Accounted history ledger [] locals w.wg)
      (cached : ∀ p, peerAt w.wg pid = some p → p.txQueue.peeked = some items)
      (performed : runPrefix (CausalJournal.completionOps.drop pid items) w history = (.error stop,last))
  | dispatch (u : World) (middle : List CausalJournal.Event)
      (removed : runPrefix (CausalJournal.completionOps.drop pid items) w history = (.ok ((),u),middle))
      (entry : Accounted middle ledger [] (⟨.selected,pid,items⟩ :: locals) u.wg)
      (pending : PendingBatch middle ledger items)
      (frontier : DispatchStop ledger locals pid items head u middle stop last)

theorem afterRead_cases
    (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (before : Accounted history ledger [] locals w.wg)
    (cached : ∀ p, peerAt w.wg pid = some p → p.txQueue.peeked = some items) :
    match (runPrefix (TxWorker.afterRead pid items head) w history).1 with
    | .error stop => AfterReadStop ledger locals pid items head w history stop
        (runPrefix (TxWorker.afterRead pid items head) w history).2
    | .ok (_,v) => Returned ledger locals (runPrefix (TxWorker.afterRead pid items head) w history).2 v := by
  have paired := drop_complete pid items before.complete w
  rw [afterRead_factor,runPrefix_bind]
  cases removed : runPrefix (CausalJournal.completionOps.drop pid items) w history with
  | mk outcome middle =>
    rw [removed] at paired
    cases outcome with
    | error stop => exact .drop before cached removed
    | ok out =>
      obtain ⟨ignored,u⟩ := out
      cases ignored
      simp only []
      obtain ⟨entry,pending⟩ := TxSelection.drop_entry pid items before.entry cached removed
      have entry : Accounted middle ledger [] (⟨.selected,pid,items⟩ :: locals) u.wg := ⟨entry,paired⟩
      have result := dispatch_cases pid items head entry pending
      cases performed : runPrefix (TxWorker.dispatch pid items head) u middle with
      | mk final last =>
        rw [performed] at result
        cases final with
        | error stop => exact .dispatch u middle removed entry pending result
        | ok out => exact result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Worker
