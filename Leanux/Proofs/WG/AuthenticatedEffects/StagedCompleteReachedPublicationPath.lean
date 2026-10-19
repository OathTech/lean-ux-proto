import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPublicationHistoryFrames

/-! A concrete published-head cut reached from the original publication
entry. The borrow's owner comes from the native key lookup, not a caller
peer argument. The later scheduling and repayment interval is separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation HandshakeSecurity.StagedDisposal

inductive PublishedPath (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (items : List SkbId) (state : PacketState) (w : World) (history : List CausalJournal.Event)
    (first : SkbId) (pid : PeerId) (v : World) (last : List CausalJournal.Event) : Prop where
  | marked (borrowWorld : World) (borrowHistory : List CausalJournal.Event)
      (initial : Accounted history ledger debts locals w.wg)
      (borrowed : runPrefix (Publication.borrow items) w history =
        (.ok ((first,pid),borrowWorld),borrowHistory))
      (beforeMark : Accounted borrowHistory ledger debts locals borrowWorld.wg)
      (marked : runPrefix (publicationMark pid first state) borrowWorld borrowHistory = (.ok ((),v),last))
      (afterMark : Accounted last ledger debts locals v.wg)

theorem PublishedPath.run
    (path : PublishedPath ledger debts locals items state w history first pid v last) :
    runPrefix (publishedPrefix items state) w history = (.ok ((first,pid),v),last) := by
  cases path with
  | marked _ _ _ borrowed _ marked =>
    simp only [publishedPrefix,runPrefix_bind,borrowed,marked,runPrefix_pure]

theorem PublishedPath.accounted
    (path : PublishedPath ledger debts locals items state w history first pid v last) :
    Accounted last ledger debts locals v.wg := by
  cases path with
  | marked _ _ _ _ _ _ afterMark => exact afterMark

theorem published_path
    (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (publishedPrefix items state) w history = (.ok ((first,pid),v),last)) :
    PublishedPath ledger debts locals items state w history first pid v last := by
  unfold publishedPrefix at performed
  rw [runPrefix_bind] at performed
  cases borrowed : runPrefix (Publication.borrow items) w history with
  | mk outcome borrowHistory =>
    rw [borrowed] at performed
    cases outcome with
    | error reason => cases performed
    | ok out =>
      obtain ⟨⟨chosen,owner⟩,u⟩ := out
      have atBorrow := publication_borrow_accounted items before borrowed
      dsimp only at performed
      rw [runPrefix_bind] at performed
      cases marked : runPrefix (publicationMark owner chosen state) u borrowHistory with
      | mk result markedHistory =>
        rw [marked] at performed
        cases result with
        | error reason => cases performed
        | ok out =>
          obtain ⟨ignored,s⟩ := out
          cases ignored
          simp only [runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at performed
          obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩ := performed
          exact .marked u borrowHistory before borrowed atBorrow marked
            (publication_mark_accounted _ _ state atBorrow marked)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
