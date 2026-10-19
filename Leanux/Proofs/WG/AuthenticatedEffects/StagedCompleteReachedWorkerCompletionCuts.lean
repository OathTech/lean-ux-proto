import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkerCompletionSource

/-! The original selected crypted callback supplies its own indexed entry.
Sending failures use the new unconditional classifier; cleanup and repayment
failures keep the existing exact native disposal path. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkerCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CompletionBatch

inductive Point where
  | sending (point : Completion.Point)
  | disposal (stage : RepaymentStage)

def sourcePrefix (pid : PeerId) : Point → PrefixM CausalJournal.Event Unit
  | .sending point => workerPrefix pid point
  | .disposal stage => workerDisposalPrefix pid stage

def Matched (context : Context) (ledger : Ledger) (w : World) (history : List CausalJournal.Event)
    (reason : Stop) (last : List CausalJournal.Event) : Point → Cut context → Prop
  | .sending point,saved => Completion.ScopedStop context ledger [] w history reason last ∧
      point.InSource context ∧ SendSettlements context ledger [] saved.ledger saved.debts
  | .disposal _,saved => Staged.Obligations.Step ledger saved.ledger

theorem matched_step (matched : Matched context ledger w history reason last point saved) :
    Staged.Obligations.Step ledger saved.ledger := by
  cases point with
  | sending point => exact matched.2.2.step
  | disposal stage => exact matched

/-- The callback interval and native prefix use the same selected world and
context. The original failed source continuation accompanies the reached cut. -/
theorem selected_cut
    (path : SelectionPath ledger locals pid w history ⟨items,head,true⟩ u middle)
    (interval : WorkerInterval ledger locals pid items head u middle (.error reason) last) :
    ∃ context : Context, context.pid = pid ∧ context.locals = locals ∧ context.items = items ∧
      context.initialLedger = ledger ∧ context.births = births middle ∧
      Owned context (.sending context.items) middle ledger [] u ∧ Complete middle ledger ∧
      runPrefix (TxWorker.crypted pid items head) u middle = (.error reason,last) ∧
      runPrefix (CausalJournal.transmit pid) w history = (.error reason,last) ∧
      ∃ point, ∃ saved : Cut context,
        Matched context ledger u middle reason last point saved ∧
        runPrefix (sourcePrefix pid point) w history = (.ok ((),saved.world),saved.before) ∧
        saved.Valid reason last := by
  obtain ⟨context,peer,localEq,batch,initial,domain,owned,complete,interval⟩ := interval
  have callback : runPrefix (TxWorker.crypted pid items head) u middle = (.error reason,last) := by
    simpa only [completedAndDisposed,TxWorker.crypted,peer,batch] using interval.run
  have native : runPrefix (CausalJournal.transmit pid) w history = (.error reason,last) := by
    rw [path.callback_run]
    simpa only [selectedCallback,↓reduceIte,completedAndDisposed,TxWorker.crypted,peer,batch] using interval.run
  refine ⟨context,peer,localEq,batch,initial,domain,owned,complete,callback,native,?_⟩
  rcases interval.stopped_cut with failed | disposal
  · have before := Converse.Sending.start owned (LocalDebts.empty context context.items) complete
    obtain ⟨stopped,point,saved,inSource,trace,prefixRun,valid⟩ := Completion.completeScoped_stopped_cut before failed.1
    exact ⟨.sending point,saved,⟨stopped,inSource,trace⟩,selected_run path peer batch prefixRun,valid⟩
  · obtain ⟨stage,saved,prefixRun,step,valid⟩ := disposal
    exact ⟨.disposal stage,saved,step,path.disposal_run peer batch prefixRun,valid⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkerCompletion
