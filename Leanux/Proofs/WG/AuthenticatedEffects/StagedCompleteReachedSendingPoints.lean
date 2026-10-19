import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingLoop

/-! Every completed prefix of the original send list reaches its own
remaining-batch account. These points do not require a later failure:
successful calls expose all their original iteration entries as well. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {initial : Ledger}

theorem loop_append (pid : PeerId) (done rest : List SkbId) (dataSent : Bool) :
    sendLoop CausalJournal.completionOps pid (done++rest) dataSent =
      (sendLoop CausalJournal.completionOps pid done dataSent >>= fun next=>
        sendLoop CausalJournal.completionOps pid rest next) := by
  induction done generalizing dataSent with
  | nil => simp only [List.nil_append,sendLoop,pure_bind]
  | cons skb done ih => simp only [List.cons_append,sendLoop,ih,bind_assoc]

theorem prefix_carrier
    (before : Converse.Sending context initial original (done++rest) history w)
    (performed : runPrefix (sendLoop CausalJournal.completionOps context.pid done dataSent) w history=
      (.ok (next,u),middle)) :
    Converse.Sending context initial original rest middle u := by
  induction done generalizing dataSent w history with
  | nil =>
      simp only [sendLoop,runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at performed
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := performed
      exact before
  | cons skb done ih =>
      obtain ⟨_,_,checked⟩ := Converse.iteration_checked context initial original skb (done++rest)
        dataSent w history before
      rw [sendLoop,runPrefix_bind] at performed
      cases step : runPrefix (iteration CausalJournal.completionOps context.pid skb dataSent) w history with
      | mk result after =>
          rw [step] at performed checked
          cases result with
          | error reason => cases performed
          | ok value =>
              obtain ⟨flag,v⟩ := value
              exact ih checked performed

structure LoopPoint (pid : PeerId) (items : List SkbId) (dataSent : Bool)
    (w : World) (history : List CausalJournal.Event) (rest : List SkbId)
    (next : Bool) (u : World) (middle : List CausalJournal.Event) where
  done : List SkbId
  shape : items=done++rest
  performed : runPrefix (sendLoop CausalJournal.completionOps pid done dataSent) w history=
    (.ok (next,u),middle)

theorem LoopPoint.literal (point : LoopPoint pid items dataSent w history rest next u middle) :
    runPrefix (sendLoop CausalJournal.completionOps pid (items.take point.done.length) dataSent) w history=
      (.ok (next,u),middle) := by
  have taken : items.take point.done.length=point.done := by
    simpa using congrArg (List.take point.done.length) point.shape
  rw [taken]
  exact point.performed

theorem LoopPoint.continuation (point : LoopPoint pid items dataSent w history rest next u middle) :
    runPrefix (sendLoop CausalJournal.completionOps pid items dataSent) w history=
      runPrefix (sendLoop CausalJournal.completionOps pid rest next) u middle := by
  rw [point.shape,loop_append,runPrefix_bind,point.performed]

theorem LoopPoint.carrier (point : LoopPoint context.pid items dataSent w history rest next u middle)
    (before : Converse.Sending context initial original items history w) :
    Converse.Sending context initial original rest middle u :=
  prefix_carrier (point.shape ▸ before) point.performed

/-- A successful original send loop reaches every numeric list prefix,
including its endpoint. The cut is selected from the original list itself. -/
theorem normal_prefix (pid : PeerId) (items : List SkbId) (dataSent : Bool)
    (completed : runPrefix (sendLoop CausalJournal.completionOps pid items dataSent) w history=
      (.ok (result,v),last)) (count : Nat) :
    ∃ next u middle, Nonempty (LoopPoint pid items dataSent w history (items.drop count) next u middle) := by
  have whole : items=items.take count++items.drop count := (List.take_append_drop count items).symm
  rw [whole,loop_append,runPrefix_bind] at completed
  cases reached : runPrefix (sendLoop CausalJournal.completionOps pid (items.take count) dataSent) w history with
  | mk outcome middle =>
      rw [reached] at completed
      cases outcome with
      | error reason => cases completed
      | ok value =>
          obtain ⟨next,u⟩ := value
          exact ⟨next,u,middle,⟨⟨items.take count,whole,reached⟩⟩⟩

/-- Every reached nonempty list prefix supplies the actual packet capture
and branch entry of its next send, with the same settlement chain. -/
theorem LoopPoint.send_entry
    (point : LoopPoint context.pid items dataSent w history (skb::rest) next u middle)
    (before : Converse.Sending context initial original items history w) :
    ∃ ledger debts packet v after,
      SendSettlements context initial original ledger debts ∧
      runPrefix (iterationPrefix skb) u middle=(.ok (packet,v),after) ∧
      Owned context (.sending (skb::rest)) after ledger debts v ∧
      Complete after ledger ∧ PacketAt skb packet v := by
  obtain ⟨ledger,debts,trace,owned,_,complete⟩ := point.carrier before
  obtain ⟨packet,v,after,reached,kept,paired,resident⟩ := iteration_entry owned complete
  exact ⟨ledger,debts,packet,v,after,trace,reached,kept,paired,resident⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
