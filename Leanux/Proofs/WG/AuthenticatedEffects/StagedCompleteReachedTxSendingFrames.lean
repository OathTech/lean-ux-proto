import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSendingSource

/-! Original selection supplies the completion context. Each actual ordered
send prefix retains that context and its one settlement chain. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompleteCarrier Staged.Obligations
variable {initial : Ledger}

theorem loop_sending (before : Accounted h initial [] locals w.wg)
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (prepared : runPrefix (WorkerCompletion.prelude pid items) u
      (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),v),last))
    (shape : items=done++rest)
    (iterations : runPrefix (sendLoop CausalJournal.completionOps pid done false) v last=(.ok (next,q),after)) :
    ∃context : Context,context.pid=pid ∧ context.locals=locals ∧ context.items=items ∧
      context.initialLedger=initial ∧ Converse.Sending context initial [] rest after q := by
  have selection:=selection_returned before selected
  obtain ⟨account,pending⟩:=selection.accounted_entry
  obtain ⟨context,peer,localEq,batch,origin,_,owned⟩:=TxSelection.selected_context account.entry pending
  have atEntry:=Converse.Sending.start owned (LocalDebts.empty context context.items) account.complete
  let point : Sending.ScopedLoopPoint context u middle rest next q after := {
    loopWorld:=v
    loopHistory:=last
    prepared:=by
      simpa only [Sending.prelude,Sending.entered,WorkerCompletion.prelude,WorkerCompletion.entered,peer,batch] using prepared
    loop:={done:=done,shape:=batch.trans shape,performed:=by simpa only [peer] using iterations} }
  exact ⟨context,peer,localEq,batch,origin,point.carrier atEntry⟩

theorem packet_sending (before : Converse.Sending context initial [] (skb::rest) h w)
    (read : runPrefix (Sending.iterationPrefix skb) w h=(.ok (packet,u),middle)) :
    Converse.Sending context initial [] (skb::rest) middle u ∧ PacketAt skb packet u := by
  obtain ⟨ledger,debts,settlements,owned,localDebts,complete⟩:=before
  obtain ⟨chosen,v,last,performed,atRead,paired,resident⟩:=Sending.iteration_entry owned complete
  have same:=performed.symm.trans read
  simp only [Prod.mk.injEq,Except.ok.injEq] at same
  obtain ⟨⟨rfl,rfl⟩,rfl⟩:=same
  exact ⟨⟨ledger,debts,settlements,atRead,localDebts,paired⟩,resident⟩

/-- The actual selected list and captured packet supply the send callback's
own account and packet identity, even when its socket call later stops. -/
theorem SendEntry.accounted (before : Accounted h initial [] locals w.wg)
    (entry : SendEntry pid w h skb packet u middle) :
    ∃context : Context,context.pid=pid ∧ context.locals=locals ∧ context.items=entry.items ∧
      context.initialLedger=initial ∧
      Converse.Sending context initial [] (skb::entry.rest) middle u ∧ PacketAt skb packet u := by
  obtain ⟨context,peer,localEq,batch,origin,sending⟩:=
    loop_sending before entry.selected entry.prepared entry.shape entry.iterations
  obtain ⟨atPacket,resident⟩:=packet_sending sending entry.read
  exact ⟨context,peer,localEq,batch,origin,atPacket,resident⟩

def Evidence (initial : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (h : List CausalJournal.Event) (w : World) : Prop :=
  ∃ledger debts items,Staged.Obligations.Step initial ledger ∧
    Accounted h ledger debts (⟨.selected,pid,items⟩::locals) w.wg

theorem sending_evidence (peer : context.pid=pid) (localEq : context.locals=locals)
    (sending : Converse.Sending context initial [] rest h w) : Evidence initial locals pid h w := by
  obtain ⟨ledger,debts,settlements,owned,_,complete⟩:=sending
  refine ⟨ledger,debts,context.items,settlements.step,?_,complete⟩
  simpa only [Phase.active,peer,localEq] using owned.entry

/-- Security: every original completed send-list prefix and following
packet capture keeps the same lineage and settlement chain. Sent cells stay
owned by the selected batch until ordinary cleanup consumes their debts. -/
theorem Point.evidence (before : Accounted h initial [] locals w.wg)
    (point : Point pid w h u middle) : Evidence initial locals pid middle u := by
  cases point with
  | loopBoundary selected prepared shape iterations=>
    obtain ⟨context,peer,localEq,_,_,sending⟩:=loop_sending before selected prepared shape iterations
    exact sending_evidence peer localEq sending
  | packetRead selected prepared shape iterations read=>
    obtain ⟨context,peer,localEq,_,_,sending⟩:=loop_sending before selected prepared shape iterations
    exact sending_evidence peer localEq (packet_sending sending read).1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSending
