import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPublicationRecord

/-! Every stopped native head publication retains the exact failed source
interval. After a completed middle, the actual borrow funds a total nonfinal
repayment, so that source branch cannot contribute another Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation HandshakeSecurity.StagedDisposal

inductive PublicationStop (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (items : List SkbId) (state : PacketState) (w : World) (history : List CausalJournal.Event)
    (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | borrowing (initial : Accounted history ledger debts locals w.wg)
      (failed : runPrefix (Publication.borrow items) w history = (.error reason,last))
  | marking (first : SkbId) (pid : PeerId) (u : World) (middle : List CausalJournal.Event)
      (initial : Accounted history ledger debts locals w.wg)
      (borrowed : runPrefix (Publication.borrow items) w history = (.ok ((first,pid),u),middle))
      (entry : Accounted middle ledger debts locals u.wg)
      (failed : runPrefix (publicationMark pid first state) u middle = (.error reason,last))
  | scheduling (first : SkbId) (pid : PeerId) (u : World) (middle : List CausalJournal.Event)
      (path : PublishedPath ledger debts locals items state w history first pid u middle)
      (failed : runPrefix (publicationSchedule pid) u middle = (.error reason,last))

/-- An original publication Stop is before its mark or after a source-linked
published cut. Successful scheduling cannot be followed by failed repayment:
the same native borrow discharges that possibility without an input premise. -/
theorem publication_stopped_cut
    (before : Accounted history ledger debts locals w.wg)
    (failed : runPrefix (TxSource.publish Admission.actualOps items state) w history = (.error reason,last)) :
    PublicationStop ledger debts locals items state w history reason last := by
  rw [Publication.factor,runPrefix_bind] at failed
  cases borrowed : runPrefix (Publication.borrow items) w history with
  | mk outcome borrowHistory =>
    rw [borrowed] at failed
    cases outcome with
    | error why => cases failed; exact .borrowing before borrowed
    | ok out =>
      obtain ⟨⟨first,pid⟩,u⟩ := out
      have atBorrow := publication_borrow_accounted items before borrowed
      dsimp only at failed
      rw [publication_middle_factor,runPrefix_bind,runPrefix_bind] at failed
      cases marked : runPrefix (publicationMark pid first state) u borrowHistory with
      | mk result markedHistory =>
        rw [marked] at failed
        cases result with
        | error why => cases failed; exact .marking first pid u borrowHistory before borrowed atBorrow marked
        | ok out =>
          obtain ⟨ignored,v⟩ := out
          cases ignored
          have path : PublishedPath ledger debts locals items state w history first pid v markedHistory :=
            .marked u borrowHistory before borrowed atBorrow marked
              (publication_mark_accounted pid first state atBorrow marked)
          dsimp only at failed
          cases scheduled : runPrefix (publicationSchedule pid) v markedHistory with
          | mk result scheduledHistory =>
            rw [scheduled] at failed
            cases result with
            | error why => cases failed; exact .scheduling first pid v markedHistory path scheduled
            | ok out =>
              obtain ⟨ignored,t⟩ := out
              cases ignored
              have middle : runPrefix (Publication.middle pid first state) u borrowHistory =
                  (.ok ((),t),scheduledHistory) := by
                rw [publication_middle_factor,runPrefix_bind,marked]
                exact scheduled
              obtain ⟨g,ambient,cutHistory,repaid,_⟩ := Publication.source_repayment_nonfinal items state borrowed middle
              dsimp only at failed
              rw [repaid] at failed
              cases failed

theorem PublicationStop.run
    (stopped : PublicationStop ledger debts locals items state w history reason last) :
    runPrefix (TxSource.publish Admission.actualOps items state) w history = (.error reason,last) := by
  cases stopped with
  | borrowing _ failed => rw [Publication.factor,runPrefix_bind,failed]
  | marking first pid u middle initial borrowed entry failed =>
    rw [Publication.factor,runPrefix_bind,borrowed]
    dsimp only
    rw [publication_middle_factor,runPrefix_bind,runPrefix_bind,failed]
  | scheduling first pid u middle path failed =>
    rw [published_prefix_factor,runPrefix_bind,path.run]
    dsimp only
    rw [runPrefix_bind,failed]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
