import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxDispatchContract

/-! The original queue removal transfers the cached batch into selected
ownership before dispatch. Stops retain either the actual removal cut or
the reached dispatch cut with its full indexed entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal
set_option pp.structureInstances false

inductive AfterReadStop (failed : CryptFailure) (ledger : Ledger) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (w : World)
    (history : List CausalJournal.Event) (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | drop
      (entry : StagedEntry.Inv history ledger [] locals w.wg)
      (cached : ∀ p, peerAt w.wg pid = some p → p.txQueue.peeked = some items)
      (performed : runPrefix (CausalJournal.completionOps.drop pid items) w history = (.error stop,last))
  | dispatch (u : World) (middle : List CausalJournal.Event)
      (removed : runPrefix (CausalJournal.completionOps.drop pid items) w history = (.ok ((),u),middle))
      (entry : StagedEntry.Inv middle ledger [] (⟨.selected,pid,items⟩ :: locals) u.wg)
      (pending : PendingBatch middle ledger items)
      (frontier : DispatchStop failed ledger locals pid items head u middle stop last)

theorem afterRead_cases (failed : CryptFailure) (completed : CryptContract failed)
    (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (before : StagedEntry.Inv history ledger [] locals w.wg)
    (cached : ∀ p, peerAt w.wg pid = some p → p.txQueue.peeked = some items) :
    match (runPrefix (afterRead pid items head) w history).1 with
    | .error stop => AfterReadStop failed ledger locals pid items head w history stop
        (runPrefix (afterRead pid items head) w history).2
    | .ok (_,v) => Returned ledger locals (runPrefix (afterRead pid items head) w history).2 v := by
  rw [afterRead_factor,runPrefix_bind]
  cases removed : runPrefix (CausalJournal.completionOps.drop pid items) w history with
  | mk outcome middle =>
    cases outcome with
    | error stop => exact .drop before cached removed
    | ok out =>
      obtain ⟨ignored,u⟩ := out
      cases ignored
      simp only []
      obtain ⟨entry,pending⟩ := TxSelection.drop_entry pid items before cached removed
      have result := dispatch_cases failed completed pid items head entry pending
      cases performed : runPrefix (dispatch pid items head) u middle with
      | mk final last =>
        rw [performed] at result
        cases final with
        | error stop => exact .dispatch u middle removed entry pending result
        | ok out => exact result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
