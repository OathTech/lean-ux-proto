import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedFresh

/-! Whole scoped completion on one ledger: actual packet sends extend the
explicit first-terminal settlement chain, and passive timer/rekey callbacks
retain it. Internally stopped sends keep their actual indexed frontier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionCuts

theorem Sending.append (before : Sending context initial original remaining history w)
    (suffix : List CausalJournal.Event) (quiet : ∀ event ∈ suffix, birthPackets event = []) :
    Sending context initial original remaining (history ++ suffix) w := by
  obtain ⟨ledger,debts,trace,owned,localDebts⟩ := before
  exact ⟨ledger,debts,trace,owned.append suffix quiet,localDebts⟩

theorem sending_passive (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (action : PrefixM CausalJournal.Event α)
    (checked : ∀ ledger debts,
      Ensures (fun h w => Owned context (.sending remaining) h ledger debts w)
        (IndexedStopped context ledger debts) action
        (fun _ h w => Owned context (.sending remaining) h ledger debts w)) :
    Ensures (Sending context initial original remaining) (SendingStopped context initial original)
      action (fun _ => Sending context initial original remaining) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts⟩ := before
  obtain ⟨suffix,grown,result⟩ := checked ledger debts w history owned
  refine ⟨suffix,grown,?_⟩
  cases run : (runPrefix action w history).1 with
  | error reason => exact ⟨ledger,debts,trace,by simpa only [run] using result⟩
  | ok out => exact ⟨ledger,debts,trace,by simpa only [run] using result,localDebts⟩

theorem sending_choice (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (decision : Decision) (value : Bool) :
    Ensures (Sending context initial original remaining) (SendingStopped context initial original)
      (CausalJournal.completionOps.step (branch decision value))
      (fun _ => Sending context initial original remaining) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts⟩ := before
  rw [branch_run]
  exact ⟨[],by simp,ledger,debts,trace,owned.sameWG rfl,localDebts⟩

theorem indexed_finish_checked (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (dataSent : Bool) :
    Ensures (Sending context initial original []) (SendingStopped context initial original)
      (finish CausalJournal.completionOps context.pid dataSent)
      (fun _ => Sending context initial original []) := by
  unfold finish
  apply Ensures.bind (sending_choice context initial original [] _ _)
  intro _
  apply Ensures.bind (sending_choice context initial original [] _ _)
  intro sent
  have fresh := sending_passive context initial original [] _
    (indexed_fresh_checked context (.sending []))
  cases sent
  · exact fresh
  · exact Ensures.bind
      (sending_passive context initial original [] _ (indexed_dataSent_checked context (.sending [])))
      (fun _ => fresh)

theorem indexed_complete_checked (context : Context) (initial : Ledger) (original : List CleanupDebt) :
    Ensures (Sending context initial original context.items) (SendingStopped context initial original)
      (CompletionEffects.completeWith CausalJournal.completionOps context.pid context.items)
      (fun _ => Sending context initial original []) := by
  rw [← complete_factor]
  unfold complete
  exact Ensures.bind (sending_passive context initial original context.items _ (indexed_marker_checked context))
    (fun _ => Ensures.bind
      (sending_passive context initial original context.items _
        (indexed_traversal_checked context (.sending context.items)))
      (fun _ => Ensures.bind
        (sending_passive context initial original context.items _
          (indexed_authenticated_checked context (.sending context.items)))
        (fun _ => Ensures.bind (indexed_sendLoop_checked context initial original context.items false)
          (indexed_finish_checked context initial original))))

theorem indexed_completeScoped_checked (context : Context) (initial : Ledger) (original : List CleanupDebt) :
    Ensures (Sending context initial original context.items) (SendingStopped context initial original)
      (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
        CausalJournal.completionOps context.pid context.items)
      (fun _ => Sending context initial original []) := by
  intro w history before
  let cause := CausalSources.Cause.completion context.pid context.items
  let event := CausalJournal.Event.scope (.entered ⟨history.length,cause⟩)
  have entered := before.append [event]
    (by intro e member; cases List.mem_singleton.mp member; rfl)
  obtain ⟨suffix,grown,result⟩ := indexed_complete_checked context initial original w (history ++ [event]) entered
  unfold CompletionEffects.completeScoped
  rw [CausalScope.prefix_run]
  cases run : runPrefix (CompletionEffects.completeWith CausalJournal.completionOps context.pid context.items)
      w (history ++ [event]) with
  | mk outcome last =>
    simp only [run] at grown result
    cases outcome with
    | error reason =>
      exact ⟨event :: suffix,by simpa only [List.append_assoc,List.singleton_append] using grown,result⟩
    | ok out =>
      refine ⟨event :: (suffix ++ [CausalJournal.Event.scope (.exited history.length)]),?_,?_⟩
      · simp only [grown,List.append_assoc,List.cons_append,List.nil_append]
      · exact result.append [CausalJournal.Event.scope (.exited history.length)]
          (by intro e member; cases List.mem_singleton.mp member; rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
