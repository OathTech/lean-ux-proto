import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionPassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionDispose

/-! Actual completion scopes and every callback preserve All Safe beside the
same sending ledger, settlement trace and debt list. Native scope tokens keep
the original history positions; there is no reindexed observer execution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {Safe : List CausalJournal.Event → Prop}

theorem sending_safe {initial : Ledger} (accountSafe : AccountSafe Safe)
    (before : Converse.Sending context initial original remaining history w) : Safe history := by
  obtain ⟨_,_,_,owned,_,complete⟩ := before
  exact owned_safe accountSafe owned complete

theorem fresh (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (accountSafe : AccountSafe Safe) :
    Checked (Converse.Sending context initial original remaining) Safe (Converse.SendingStopped context initial original)
      (CausalJournal.completionOps.fresh context.pid) (fun _ => Converse.Sending context initial original remaining) :=
  sending_passive context initial original remaining _ accountSafe
    (indexed_fresh_checked context (.sending remaining))
    (fun _ _ _ _ owned complete => Converse.fresh_complete context.pid owned complete)

theorem finish (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (dataSent : Bool) (accountSafe : AccountSafe Safe) :
    Checked (Converse.Sending context initial original []) Safe (Converse.SendingStopped context initial original)
      (CompletionBatch.finish CausalJournal.completionOps context.pid dataSent)
      (fun _ => Converse.Sending context initial original []) := by
  unfold CompletionBatch.finish
  apply Checked.bind (sending_branch context initial original [] _ _)
  intro _
  apply Checked.bind (sending_branch context initial original [] _ _)
  intro sent
  cases sent
  · exact fresh context initial original [] accountSafe
  · exact Checked.bind
      (sending_passive context initial original [] _ accountSafe (indexed_dataSent_checked context (.sending []))
        (fun _ _ _ w _ complete => Converse.dataSent_complete context.pid complete w))
      (fun _ => fresh context initial original [] accountSafe)

theorem complete (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (accountSafe : AccountSafe Safe) :
    Checked (Converse.Sending context initial original context.items) Safe (Converse.SendingStopped context initial original)
      (CompletionEffects.completeWith CausalJournal.completionOps context.pid context.items)
      (fun _ => Converse.Sending context initial original []) := by
  rw [← complete_factor]
  unfold CompletionBatch.complete
  exact Checked.bind
    (sending_passive context initial original context.items _ accountSafe (indexed_marker_checked context)
      (fun _ _ _ w _ complete => Converse.marker_complete context.pid context.items complete w))
    (fun _ => Checked.bind
      (sending_passive context initial original context.items _ accountSafe
        (indexed_traversal_checked context (.sending context.items))
        (fun _ _ _ w _ complete => Converse.traversal_complete context.pid complete w))
      (fun _ => Checked.bind
        (sending_passive context initial original context.items _ accountSafe
          (indexed_authenticated_checked context (.sending context.items))
          (fun _ _ _ w _ complete => Converse.authenticated_complete context.pid complete w))
        (fun _ => Checked.bind (send_loop context initial original context.items false accountSafe)
          (fun sent => finish context initial original sent accountSafe))))

theorem complete_scoped (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (accountSafe : AccountSafe Safe) :
    Checked (Converse.Sending context initial original context.items) Safe (Converse.SendingStopped context initial original)
      (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
        CausalJournal.completionOps context.pid context.items)
      (fun _ => Converse.Sending context initial original []) := by
  intro w history before
  let cause := CausalSources.Cause.completion context.pid context.items
  let event := CausalJournal.Event.scope (.entered ⟨history.length,cause⟩)
  have entered := before.1.append [event]
    (by intro e member; cases List.mem_singleton.mp member; rfl)
    (by intro e member; cases List.mem_singleton.mp member; intro position; rfl)
  have enteredAll := before.2.append (Cuts.singleton before.2.last (sending_safe accountSafe entered))
  obtain ⟨suffix,grown,result⟩ := complete context initial original accountSafe w (history ++ [event]) ⟨entered,enteredAll⟩
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
      have exited := result.1.append [CausalJournal.Event.scope (.exited history.length)]
        (by intro e member; cases List.mem_singleton.mp member; rfl)
        (by intro e member; cases List.mem_singleton.mp member; intro position; rfl)
      refine ⟨event :: (suffix ++ [CausalJournal.Event.scope (.exited history.length)]),?_,exited,?_⟩
      · simp only [grown,List.append_assoc,List.cons_append,List.nil_append]
      · exact result.2.append (Cuts.singleton result.2.last (sending_safe accountSafe exited))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
