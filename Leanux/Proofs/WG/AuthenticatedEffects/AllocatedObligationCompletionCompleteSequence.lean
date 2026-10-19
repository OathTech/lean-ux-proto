import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteFresh

/-! Scoped completion retains receipt completeness on the same explicit
ledger as every source settlement and physical cleanup debt. Passive timer
and rekey callbacks preserve that pair even when the native source Stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionCuts StagedTerminalComplete

theorem Sending.append (before : Sending context initial original remaining history w)
    (suffix : List CausalJournal.Event) (quiet : ∀ event ∈ suffix, birthPackets event = [])
    (terminalQuiet : ∀ event ∈ suffix, Quiet event) :
    Sending context initial original remaining (history ++ suffix) w := by
  obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before
  exact ⟨ledger,debts,trace,owned.append suffix quiet,localDebts,complete.append_quiet terminalQuiet⟩

theorem sending_choice (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (decision : Decision) (value : Bool) :
    Ensures (Sending context initial original remaining) (SendingStopped context initial original)
      (CausalJournal.completionOps.step (branch decision value))
      (fun _ => Sending context initial original remaining) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before
  rw [branch_run]
  exact ⟨[],by simp,ledger,debts,trace,owned.sameWG rfl,localDebts,complete⟩

theorem finish_checked (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (dataSent : Bool) :
    Ensures (Sending context initial original []) (SendingStopped context initial original)
      (finish CausalJournal.completionOps context.pid dataSent)
      (fun _ => Sending context initial original []) := by
  unfold finish
  apply Ensures.bind (sending_choice context initial original [] _ _)
  intro _
  apply Ensures.bind (sending_choice context initial original [] _ _)
  intro sent
  have fresh := sending_fresh context initial original []
  cases sent
  · exact fresh
  · exact Ensures.bind
      (sending_passive context initial original [] _ (indexed_dataSent_checked context (.sending []))
        (fun _ _ w complete => dataSent_complete context.pid complete w))
      (fun _ => fresh)

theorem complete_checked (context : Context) (initial : Ledger) (original : List CleanupDebt) :
    Ensures (Sending context initial original context.items) (SendingStopped context initial original)
      (CompletionEffects.completeWith CausalJournal.completionOps context.pid context.items)
      (fun _ => Sending context initial original []) := by
  rw [← complete_factor]
  unfold complete
  exact Ensures.bind (sending_passive context initial original context.items _ (indexed_marker_checked context)
      (fun _ _ w complete => marker_complete context.pid context.items complete w))
    (fun _ => Ensures.bind
      (sending_passive context initial original context.items _
        (indexed_traversal_checked context (.sending context.items))
        (fun _ _ w complete => traversal_complete context.pid complete w))
      (fun _ => Ensures.bind
        (sending_passive context initial original context.items _
          (indexed_authenticated_checked context (.sending context.items))
          (fun _ _ w complete => authenticated_complete context.pid complete w))
        (fun _ => Ensures.bind (sendLoop_checked context initial original context.items false)
          (finish_checked context initial original))))

theorem completeScoped_checked (context : Context) (initial : Ledger) (original : List CleanupDebt) :
    Ensures (Sending context initial original context.items) (SendingStopped context initial original)
      (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
        CausalJournal.completionOps context.pid context.items)
      (fun _ => Sending context initial original []) := by
  intro w history before
  let cause := CausalSources.Cause.completion context.pid context.items
  let event := CausalJournal.Event.scope (.entered ⟨history.length,cause⟩)
  have entered := before.append [event]
    (by intro e member; cases List.mem_singleton.mp member; rfl)
    (by intro e member; cases List.mem_singleton.mp member; intro position; rfl)
  obtain ⟨suffix,grown,result⟩ := complete_checked context initial original w (history ++ [event]) entered
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
          (by intro e member; cases List.mem_singleton.mp member; intro position; rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
