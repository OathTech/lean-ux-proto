import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingIteration

/-! A stopped send loop records each actual successful preceding iteration.
The retained ledger belongs to the failed iteration's native entry; the fixed
prefix is the original loop on precisely the already processed list. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {initial : Ledger}

inductive LoopStop (context : Context) (initial : Ledger) (original : List CleanupDebt) :
    List SkbId → Bool → World → List CausalJournal.Event → Stop → List CausalJournal.Event → Prop where
  | current (ledger : Ledger) (debts : List CleanupDebt)
      (trace : SendSettlements context initial original ledger debts)
      (cut : IterationStop context skb rest dataSent w history ledger debts reason last) :
      LoopStop context initial original (skb :: rest) dataSent w history reason last
  | later (next : Bool) (u : World) (middle : List CausalJournal.Event)
      (performed : runPrefix (iteration CausalJournal.completionOps context.pid skb dataSent) w history =
        (.ok (next,u),middle))
      (entry : Converse.Sending context initial original rest middle u)
      (tail : LoopStop context initial original rest next u middle reason last) :
      LoopStop context initial original (skb :: rest) dataSent w history reason last

theorem loop_failed (before : Converse.Sending context initial original remaining history w)
    (failed : runPrefix (sendLoop CausalJournal.completionOps context.pid remaining dataSent) w history =
      (.error reason,last)) :
    LoopStop context initial original remaining dataSent w history reason last := by
  induction remaining generalizing dataSent w history with
  | nil => cases failed
  | cons skb rest ih =>
    have checked := Converse.iteration_checked context initial original skb rest dataSent w history before
    obtain ⟨_,_,checked⟩ := checked
    rw [sendLoop,runPrefix_bind] at failed
    cases performed : runPrefix (iteration CausalJournal.completionOps context.pid skb dataSent) w history with
    | mk outcome middle =>
      rw [performed] at checked failed
      cases outcome with
      | error stop =>
        cases failed
        obtain ⟨ledger,debts,trace,owned,_,complete⟩ := before
        obtain ⟨cut⟩ := iteration_failed owned complete performed
        exact .current ledger debts trace cut
      | ok out =>
        obtain ⟨next,u⟩ := out
        exact .later next u middle performed checked (ih checked failed)

theorem LoopStop.source_failed
    (stopped : LoopStop context initial original remaining dataSent w history reason last) :
    runPrefix (sendLoop CausalJournal.completionOps context.pid remaining dataSent) w history =
      (.error reason,last) := by
  induction stopped with
  | current ledger debts trace cut => rw [sendLoop,runPrefix_bind,cut.source_failed]
  | later next u middle performed entry tail ih => rw [sendLoop,runPrefix_bind,performed]; exact ih

/-- The returned prefix is the source's own loop on the processed list, not
an arbitrary monadic action selected after observing its final state. -/
theorem LoopStop.iteration_prefix
    (stopped : LoopStop context initial original remaining dataSent w history reason last) :
    ∃ done skb rest next u middle ledger debts,
      remaining = done ++ (skb :: rest) ∧
      runPrefix (sendLoop CausalJournal.completionOps context.pid done dataSent) w history =
        (.ok (next,u),middle) ∧
      SendSettlements context initial original ledger debts ∧
      Nonempty (IterationStop context skb rest next u middle ledger debts reason last) := by
  induction stopped with
  | current ledger debts trace cut =>
    exact ⟨[],_,_,_,_,_,ledger,debts,rfl,rfl,trace,⟨cut⟩⟩
  | @later skb dataSent w history rest reason last next u middle performed entry tail ih =>
    obtain ⟨done,id,remaining,nextFlag,v,cutHistory,ledger,debts,shape,run,trace,cut⟩ := ih
    refine ⟨skb :: done,id,remaining,nextFlag,v,cutHistory,ledger,debts,?_,?_,trace,cut⟩
    · simp only [List.cons_append,shape]
    · rw [sendLoop,runPrefix_bind,performed]
      exact run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Sending
