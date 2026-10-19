import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRelease

/-! Constructor-preserving projections of stopped disposal and completion.
Each output cut is selected by the same source branch as its original failure.
These projections preserve existing evidence; operational reach from the outer
entry additionally requires `Reached.At` and is not inferred from histories. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch
open AllocatedObligation.CompletionBatch.Converse HandshakeSecurity.StagedDisposal

inductive DisposeProjection (context : Context) (key : KeypairId) (ledger : Ledger)
    (reason : Stop) (last : List CausalJournal.Event) : Cut context → Prop where
  | keyStopped (cutWorld : World) (cutHistory : List CausalJournal.Event)
      (owned : Owned context (.freeing []) cutHistory ledger [] cutWorld)
      (failed : runPrefix ((TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal).access (keypairPutPrefix (some key) false))
        cutWorld cutHistory = (.error reason,last))
      (frontier : IndexedFrontier context ledger [] reason last)
      (complete : Complete last ledger) :
      DisposeProjection context key ledger reason last (Cut.indexed frontier)
  | peerStopped (cutWorld : World) (cutHistory : List CausalJournal.Event)
      (owned : Owned context (.freeing []) cutHistory ledger [] cutWorld)
      (projection : ReleaseProjection context (.freeing []) ledger [] (some context.pid)
        cutWorld cutHistory reason last saved) :
      DisposeProjection context key ledger reason last saved

theorem dispose_project (stopped : Converse.DisposeStopped context key ledger reason last) :
    ∃ saved, DisposeProjection context key ledger reason last saved := by
  cases stopped with
  | keyStopped cutWorld cutHistory owned failed frontier complete =>
    obtain ⟨frontier⟩ := frontier
    exact ⟨_,.keyStopped cutWorld cutHistory owned failed frontier complete⟩
  | peerStopped cutWorld cutHistory owned frontier =>
    obtain ⟨saved,projection⟩ := release_project frontier
    exact ⟨saved,.peerStopped cutWorld cutHistory owned projection⟩

theorem DisposeProjection.original
    (projection : DisposeProjection context key ledger reason last saved) :
    Converse.DisposeStopped context key ledger reason last := by
  cases projection with
  | keyStopped cutWorld cutHistory owned failed frontier complete =>
    exact .keyStopped cutWorld cutHistory owned failed ⟨frontier⟩ complete
  | peerStopped cutWorld cutHistory owned projection =>
    exact .peerStopped cutWorld cutHistory owned projection.original

theorem DisposeProjection.valid
    (projection : DisposeProjection context key ledger reason last saved) :
    saved.Valid reason last := by
  cases projection with
  | keyStopped _ _ _ _ frontier complete => exact Cut.indexed_valid frontier complete
  | peerStopped _ _ _ projection => exact projection.valid

theorem DisposeProjection.step
    (projection : DisposeProjection context key ledger reason last saved) :
    Staged.Obligations.Step ledger saved.ledger := by
  cases projection with
  | keyStopped => exact .refl _
  | peerStopped _ _ _ projection => exact projection.step

theorem DisposeProjection.empty_debts
    (projection : DisposeProjection context key ledger reason last saved) :
    saved.debts = [] := by
  cases projection with
  | keyStopped => rfl
  | peerStopped _ _ _ projection => exact projection.debts_eq

inductive BatchProjection (context : Context) (initial : Ledger) (key : KeypairId)
    (w : World) (history : List CausalJournal.Event) (reason : Stop)
    (last : List CausalJournal.Event) : Cut context → Prop where
  | sending
      (failed : runPrefix
        (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
          CausalJournal.completionOps context.pid context.items) w history = (.error reason,last))
      (ledger : Ledger) (debts : List CleanupDebt)
      (trace : SendSettlements context initial [] ledger debts)
      (frontier : IndexedFrontier context ledger debts reason last)
      (complete : Complete last ledger) :
      BatchProjection context initial key w history reason last (Cut.indexed frontier)
  | disposing (ledger : Ledger) (debts : List CleanupDebt) (cutWorld : World)
      (cutHistory : List CausalJournal.Event)
      (completed : runPrefix
        (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
          CausalJournal.completionOps context.pid context.items) w history = (.ok ((),cutWorld),cutHistory))
      (trace : SendSettlements context initial [] ledger debts)
      (owned : Owned context (.freeing context.items) cutHistory ledger debts cutWorld)
      (localDebts : LocalDebts context context.items debts)
      (complete : Complete cutHistory ledger)
      (failed : runPrefix (CausalJournal.completionOps.dispose context.pid context.items key)
        cutWorld cutHistory = (.error reason,last))
      (projection : DisposeProjection context key ledger reason last saved) :
      BatchProjection context initial key w history reason last saved

theorem batch_project
    (stopped : BatchStopped context ledger key w history reason last) :
    ∃ saved, BatchProjection context ledger key w history reason last saved := by
  cases stopped with
  | sending failed frontier =>
    obtain ⟨after,debts,trace,⟨frontier⟩,complete⟩ := frontier
    exact ⟨_,.sending failed after debts trace frontier complete⟩
  | disposing after debts cutWorld cutHistory completed trace owned localDebts complete failed frontier =>
    obtain ⟨saved,projection⟩ := dispose_project frontier
    exact ⟨saved,.disposing after debts cutWorld cutHistory completed trace owned localDebts complete failed projection⟩

theorem BatchProjection.original
    (projection : BatchProjection context ledger key w history reason last saved) :
    BatchStopped context ledger key w history reason last := by
  cases projection with
  | sending failed after debts trace frontier complete =>
    exact .sending failed ⟨after,debts,trace,⟨frontier⟩,complete⟩
  | disposing after debts cutWorld cutHistory completed trace owned localDebts complete failed projection =>
    exact .disposing after debts cutWorld cutHistory completed trace owned localDebts complete failed projection.original

theorem BatchProjection.valid
    (projection : BatchProjection context ledger key w history reason last saved) :
    saved.Valid reason last := by
  cases projection with
  | sending _ _ _ _ frontier complete => exact Cut.indexed_valid frontier complete
  | disposing _ _ _ _ _ _ _ _ _ _ projection => exact projection.valid

theorem BatchProjection.step
    (projection : BatchProjection context ledger key w history reason last saved) :
    Staged.Obligations.Step ledger saved.ledger := by
  cases projection with
  | sending _ _ _ trace => exact trace.step
  | disposing _ _ _ _ _ trace _ _ _ _ projection => exact trace.step.trans projection.step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
