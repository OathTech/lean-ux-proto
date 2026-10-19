import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeadRepayment

/-! A DEAD batch's actual labelled free loop discharges the selected local
before repayment. Its exact run, same successor ledger and named terminal
outcomes stay attached to the original callback entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch

inductive DeadCleanupPath (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (w : World) (history : List CausalJournal.Event) (v : World)
    (last : List CausalJournal.Event) (after : Ledger) : Prop where
  | freed (suffix : List CausalJournal.Event)
      (initial : Accounted history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg)
      (performed : runPrefix (CreateDisposal.loop (.deadBatch pid head) items) w history =
        (.ok ((),v),last))
      (extended : last = history ++ suffix)
      (step : Staged.Obligations.Step ledger after)
      (accounted : Accounted last after debts locals v.wg)
      (dropped : CreateDisposal.AllDropped last after (.deadBatch pid head) items)

theorem DeadCleanupPath.run
    (path : DeadCleanupPath ledger debts locals pid items head w history v last after) :
    runPrefix (CreateDisposal.loop (.deadBatch pid head) items) w history = (.ok ((),v),last) := by
  cases path with
  | freed _ _ performed => exact performed

theorem DeadCleanupPath.accounted
    (path : DeadCleanupPath ledger debts locals pid items head w history v last after) :
    Staged.Obligations.Step ledger after ∧ Accounted last after debts locals v.wg ∧
      CreateDisposal.AllDropped last after (.deadBatch pid head) items := by
  cases path with
  | freed _ _ _ _ step accounted dropped => exact ⟨step,accounted,dropped⟩

theorem dead_stopped_path
    (before : Accounted history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg)
    (frontier : Converse.Dead.Stopped ledger debts locals pid items head w history reason last) :
    ∃ u middle after,
      DeadCleanupPath ledger debts locals pid items head w history u middle after ∧
      runPrefix (DeadEntry.repay pid head.keypair) u middle = (.error reason,last) ∧
      Converse.Dead.RepayStopped after debts locals pid head.keypair u middle reason last := by
  cases frontier with
  | atRepay u suffix after freed step accounted dropped failed stopped =>
    exact ⟨u,history ++ suffix,after,.freed suffix before freed rfl step accounted dropped,failed,stopped⟩

/-- A DEAD callback Stop follows its actual total labelled free loop. The
saved repayment cut is reached by a fixed original prefix, with the same
settled ledger and physical local ownership, including a final peer release. -/
theorem dead_stopped_cut
    (before : Accounted history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg)
    (frontier : Converse.Dead.Stopped ledger debts locals pid items head w history reason last) :
    ∃ u middle after,
      DeadCleanupPath ledger debts locals pid items head w history u middle after ∧
      ∃ stage, ∃ cut : DeadCut,
        runPrefix (deadPrefix pid items head stage) w history = (.ok ((),cut.world),cut.before) ∧
        Staged.Obligations.Step ledger cut.ledger ∧ cut.debts = debts ∧ cut.locals = locals ∧
        cut.Valid reason last := by
  obtain ⟨u,middle,after,path,_,stopped⟩ := dead_stopped_path before frontier
  obtain ⟨stage,cut,performed,step,debtEq,localEq,valid⟩ :=
    dead_repayment_reached path.accounted.2.1 stopped
  refine ⟨u,middle,after,path,stage,cut,?_,path.accounted.1.trans step,debtEq,localEq,valid⟩
  rw [deadPrefix,runPrefix_bind,path.run]
  exact performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
