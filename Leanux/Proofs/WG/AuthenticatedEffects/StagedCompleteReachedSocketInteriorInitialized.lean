import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorCoverage
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkerSendingPoints
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionInitialized

/-! The initialized worker derives the packet entry and settlement chain
used by the actual socket result interval. Every earlier send is an original
completed list prefix; later success or failure is not a premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Lifetimes Queues
open TransmitSecurity CausalJournal AllocatedObligation CompletionBatch Staged.Obligations
open StagedTerminalComplete CompletionFirstTerminal

theorem TxEntry.socket_intervals
    (entry : TxEntry trace placeholders operationIndex pid world history)
    (selected : runPrefix (workerSelection pid) world history=(.ok (some ⟨items,head,true⟩,u),middle))
    (shape : items=done++(skb::rest))
    (prepared : runPrefix (WorkerCompletion.prelude pid items) u
      (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),loopWorld),loopHistory))
    (iterations : runPrefix (sendLoop completionOps pid done false) loopWorld loopHistory=
      (.ok (next,v),after)) :
    ∃ initial, ∃ context : CompletionBatch.Context,
      context.pid=pid ∧ context.locals=[] ∧ context.items=items ∧ context.initialLedger=initial ∧
      ∃ ledger debts packet z last,
        SendSettlements context initial [] ledger debts ∧ Staged.Obligations.Step initial ledger ∧
        runPrefix (WorkerCompletion.workerPrefix pid (.packet done skb)) world history=(.ok ((),z),last) ∧
        Owned context (.sending (skb::rest)) last ledger debts z ∧ Complete last ledger ∧ PacketAt skb packet z ∧
        ∀ peer q readEvents ipv4 result frontWorld events,
          runPrefix (captureObserved (Completion.access (getPeerMixed context.pid))) z
            (last.filterMap CausalJournal.completion?)=
            (.ok (peer,q),last.filterMap CausalJournal.completion?++readEvents) →
          SelectedFamily ipv4 peer →
          runPrefix (SocketInterior.socketFront context.pid packet peer ipv4) (familyWorld ipv4 q)
            ((last++readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?)=
            (.ok (result,frontWorld),
              (last++readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?++events) →
          Nonempty (SocketInterior.Awaiting context skb rest packet peer ipv4
            (last++readEvents.map FirstTerminal.encode) ledger debts (familyWorld ipv4 q) result frontWorld events) := by
  obtain ⟨initial,path⟩ := entry.selected selected
  obtain ⟨context,peer,locals,batch,origin,ledger,debts,packet,z,last,settlements,step,reached,owned,complete,resident⟩ :=
    WorkerCompletion.selected_sending_entry path shape prepared iterations
  refine ⟨initial,context,peer,locals,batch,origin,ledger,debts,packet,z,last,
    settlements,step,reached,owned,complete,resident,?_⟩
  intro peer q readEvents ipv4 result frontWorld events read family front
  exact SocketInterior.from_send_entry owned complete resident read family front

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
