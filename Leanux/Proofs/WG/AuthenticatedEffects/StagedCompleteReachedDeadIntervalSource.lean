import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeadWorker

/-! Ordered labelled-free intervals retain each actual cleanup run and its
single fixed-ticket settlement. The iteration boundary is after the original
terminal receipt, with the exact remaining selected list and original debts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeadIntervals
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedConservation

inductive Iteration (reason : Terminal.Reason) (pid : PeerId) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (id : SkbId) (remaining : List SkbId)
    (w : World) (history : List CausalJournal.Event) (ledger : Ledger)
    (v : World) (last : List CausalJournal.Event) (after : Ledger) : Prop where
  | receipt (ticket : Staged.Origins.Ticket) (position ordinal generation : Nat) (value : DataPacket)
      (accesses : List CausalJournal.Event)
      (initial : Accounted history ledger debts (⟨.selected,pid,id :: remaining⟩ :: locals) w.wg)
      (batch : PendingBatch history ledger (id :: remaining))
      (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
      (origin : Origin history position ordinal generation id value)
      (cleanup : runPrefix (FirstTerminal.cleanupFree id) w history = (.ok ((),v),history ++ accesses))
      (performed : runPrefix (free reason id) w history = (.ok ((),v),last))
      (recorded : last = history ++ accesses ++ [.terminalDrop ⟨reason,id,⟨(),w,v⟩⟩])
      (assigned : after = settle [ticket] (.disposed (history ++ accesses).length reason) ledger)
      (step : Staged.Obligations.Step ledger after)
      (accounted : Accounted last after debts (⟨.selected,pid,remaining⟩ :: locals) v.wg)
      (rest : PendingBatch last after remaining)
      (dropped : Dropped last after reason id)

inductive Path (reason : Terminal.Reason) (pid : PeerId) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) : Nat → List SkbId → World → List CausalJournal.Event → Ledger →
      World → List CausalJournal.Event → Ledger → Prop where
  | nil (before : Accounted history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg)
      (pending : PendingBatch history ledger items) :
      Path reason pid debts locals 0 items w history ledger w history ledger
  | cons {id : SkbId} (first : Iteration reason pid debts locals id items w history ledger u middle next)
      (rest : Path reason pid debts locals n items u middle next v last after) :
      Path reason pid debts locals (n + 1) (id :: items) w history ledger v last after

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeadIntervals
