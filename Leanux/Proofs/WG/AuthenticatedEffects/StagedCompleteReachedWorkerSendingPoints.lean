import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingScopedPoints
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkerCompletionAccounted

/-! The selected TX worker reaches every completed send-list prefix,
including prefixes of successful completion. Its actual prelude, original
list split and native packet capture retain the same settlement chain. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkerCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CompletionBatch
variable {initial : Ledger}

theorem selected_sending_entry
    (path : SelectionPath initial locals pid w history ⟨items,head,true⟩ u middle)
    (shape : items=done++(skb::rest))
    (prepared : runPrefix (prelude pid items) u (middle++[entered pid items middle])=
      (.ok ((),loopWorld),loopHistory))
    (iterations : runPrefix (sendLoop CausalJournal.completionOps pid done false) loopWorld loopHistory=
      (.ok (next,v),after)) :
    ∃ context : Context, context.pid=pid ∧ context.locals=locals ∧ context.items=items ∧
      context.initialLedger=initial ∧
      ∃ ledger debts packet z last,
        SendSettlements context initial [] ledger debts ∧
        Staged.Obligations.Step initial ledger ∧
        runPrefix (workerPrefix pid (.packet done skb)) w history=(.ok ((),z),last) ∧
        Owned context (.sending (skb::rest)) last ledger debts z ∧
        Complete last ledger ∧ PacketAt skb packet z := by
  obtain ⟨account,pending⟩ := path.accounted_entry
  obtain ⟨context,peer,localEq,batch,origin,_,owned⟩ :=
    TxSelection.selected_context account.entry pending
  have before := Converse.Sending.start owned (LocalDebts.empty context context.items) account.complete
  let point : Sending.ScopedLoopPoint context u middle (skb::rest) next v after := {
    loopWorld := loopWorld
    loopHistory := loopHistory
    prepared := by
      simpa only [Sending.prelude,Sending.entered,prelude,entered,peer,batch] using prepared
    loop := {
      done := done
      shape := batch.trans shape
      performed := by simpa only [peer] using iterations } }
  obtain ⟨ledger,debts,packet,z,last,trace,reached,kept,paired,resident⟩ := point.send_entry before
  refine ⟨context,peer,localEq,batch,origin,ledger,debts,packet,z,last,trace,trace.step,?_,kept,paired,resident⟩
  exact selected_run path peer batch reached

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkerCompletion
