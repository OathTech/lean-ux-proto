import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorker

/-! A trace of the actual ordinary completion frees. Each node records the
original named callback, its exact input and output states and histories, and
the same ledger's shrinking selected local and cleanup debts. The initial
caller's global anchor is deliberately not inferred by this local trace. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch
open AllocatedObligation.CompletionBatch.Converse HandshakeSecurity.StagedDisposal

abbrev cleanupOps := TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
  CausalJournal.Event.stagedDisposal

inductive CleanupPath (context : Context) (ledger : Ledger) : List SkbId →
    List CleanupDebt → World → List CausalJournal.Event → World → List CausalJournal.Event → Prop where
  | done (owned : Owned context (.freeing []) history ledger [] w)
      (complete : Complete history ledger) : CleanupPath context ledger [] [] w history w history
  | next (owned : Owned context (.freeing (skb :: rest)) history ledger debts w)
      (complete : Complete history ledger) (generation : Nat)
      (epoch : Packets.epoch w.wg = some generation)
      (performed : runPrefix (FirstTerminal.cleanupFree skb) w history = (.ok ((),u),history ++ suffix))
      (tail : CleanupPath context ledger rest (forgetFreedCell history generation skb debts)
        u (history ++ suffix) v last) :
      CleanupPath context ledger (skb :: rest) debts w history v last

theorem CleanupPath.initial (path : CleanupPath context ledger remaining debts w history v last) :
    Owned context (.freeing remaining) history ledger debts w ∧ Complete history ledger := by
  cases path with
  | done owned complete => exact ⟨owned,complete⟩
  | next owned complete => exact ⟨owned,complete⟩

theorem CleanupPath.returned (path : CleanupPath context ledger remaining debts w history v last) :
    Owned context (.freeing []) last ledger [] v ∧ Complete last ledger := by
  induction path with
  | done owned complete => exact ⟨owned,complete⟩
  | next _ _ _ _ _ _ ih => exact ih

/-- The trace executes the original fixed-list free loop, including the
exact lifetime-event suffix. It never substitutes a terminal-labelled free. -/
theorem CleanupPath.run (path : CleanupPath context ledger remaining debts w history v last) :
    runPrefix (freeLoop cleanupOps remaining) w history = (.ok ((),v),last) := by
  induction path with
  | done => rfl
  | @next skb rest history debts w generation u suffix v last _ _ _ performed tail ih =>
    change runPrefix (FirstTerminal.cleanupFree skb >>= fun _ => freeLoop cleanupOps rest) w history = _
    rw [runPrefix_bind,performed]
    exact ih

/-- Each cleanup is derived as total from the actual selected ownership;
the same canonical ledger persists and the debt list is restored to empty. -/
theorem cleanup_path (remaining : List SkbId)
    (before : Owned context (.freeing remaining) history ledger debts w)
    (localDebts : LocalDebts context remaining debts) (complete : Complete history ledger) :
    ∃ v last, CleanupPath context ledger remaining debts w history v last := by
  induction remaining generalizing debts w history with
  | nil =>
    have empty := localDebts.finished
    subst debts
    exact ⟨w,history,.done before complete⟩
  | cons skb rest ih =>
    obtain ⟨u,suffix,generation,epoch,performed,after⟩ := indexed_free_total_epoch before
    have nextComplete := cleanup_complete complete skb w
    rw [performed] at nextComplete
    obtain ⟨v,last,path⟩ := ih after (localDebts.free before epoch) nextComplete
    exact ⟨v,last,.next before complete generation epoch performed path⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
