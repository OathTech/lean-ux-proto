import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedFamily

/-! The outer completed result is an observation of the same send. Once an
inner socket has settled a ticket, the outer result only extends its history:
even false cannot replace the first terminal or create another cleanup debt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations HandshakeSecurity.StagedConservation

/-- Lift an already indexed inner settlement through the actual outer
result observer. Failed accounting has no outer receipt; normal false and
true results keep the exact same ledger and debts. -/
theorem indexed_observed_after_settlement
    (context : Context) (skb : SkbId) (rest : List SkbId) (packet : RunWitness DataPacket)
    (w : World) (history settledAt : List CausalJournal.Event) (ledger : Ledger) (debts : List CleanupDebt)
    (prefixHistory : ∃ suffix,
      (runPrefix (FirstTerminal.focused (Completion.send context.pid skb packet)) w history).2 =
        settledAt ++ suffix)
    (safe : match (runPrefix (FirstTerminal.focused (Completion.send context.pid skb packet)) w history).1 with
      | .error reason => IndexedStopped context ledger debts reason
          (runPrefix (FirstTerminal.focused (Completion.send context.pid skb packet)) w history).2
      | .ok (_,after) => Owned context (.sending rest)
          (runPrefix (FirstTerminal.focused (Completion.send context.pid skb packet)) w history).2 ledger debts after) :
    ∃ suffix, (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).2 =
        settledAt ++ suffix ∧
      match (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).1 with
      | .error reason => IndexedStopped context ledger debts reason
          (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).2
      | .ok (_,after) => Owned context (.sending rest)
          (runPrefix (CausalJournal.completionOps.send context.pid skb packet) w history).2 ledger debts after := by
  have wrapper : CausalJournal.completionOps.send context.pid skb packet =
      SendResult.observed CausalJournal.Event.sendResult
        (FirstTerminal.focused (Completion.send context.pid skb packet)) context.pid skb packet := rfl
  simp only [wrapper,SendResult.observed,runPrefix_receiptObserved]
  obtain ⟨suffix,grown⟩ := prefixHistory
  cases run : runPrefix (FirstTerminal.focused (Completion.send context.pid skb packet)) w history with
  | mk result journal =>
    rw [run] at safe grown
    dsimp only at grown
    cases result with
    | error reason => exact ⟨suffix,grown,safe⟩
    | ok result =>
      obtain ⟨sent,after⟩ := result
      let event : CausalJournal.Event := .sendResult ⟨context.pid,skb,packet,⟨sent,w,after⟩⟩
      refine ⟨suffix ++ [event],?_,?_⟩
      · rw [grown]
        simp only [event,List.append_assoc]
      · exact safe.append [event] (by intro e member; cases List.mem_singleton.mp member; rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
