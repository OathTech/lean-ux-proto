import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedObservedTimers

/-! Native packet capture, branch bookkeeping and the send-to-free phase
switch retain one explicit ledger/debt pair and the actual selected batch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity CompletionCuts

theorem Owned.sameWG (before : Owned context phase history ledger debts w) (same : v.wg = w.wg) :
    Owned context phase history ledger debts v := before.same_view (congrArg StagedEntry.view same)

theorem Owned.ready_to_free (before : Owned context (.sending []) history ledger debts w) :
    Owned context (.freeing context.items) history ledger debts w := by
  refine ⟨⟨before.cursor.step,before.cursor.recorded,⟨[],rfl⟩,?_⟩,before.entry,before.domain⟩
  intro binding member
  obtain ⟨outcome,debt,terminal⟩ := (before.cursor.assigned binding member).2 (by simp)
  exact ⟨⟨outcome,terminal⟩,fun _ => ⟨outcome,debt,terminal⟩⟩

theorem indexed_packet_checked (context : Context) (skb : SkbId) (remaining : List SkbId)
    (ledger : Ledger) (debts : List CleanupDebt) :
    Ensures (fun h w => Owned context (.sending (skb :: remaining)) h ledger debts w)
      (IndexedStopped context ledger debts)
      (captureObserved (CausalJournal.completionOps.packet skb))
      (fun receipt h w => Owned context (.sending (skb :: remaining)) h ledger debts w ∧
        PacketAt skb receipt w) := by
  intro w history before
  obtain ⟨packet,resident⟩ := before.state.sending_resident
  have original := native_packet_total resident
  have erases : ErasesPrefix (CausalJournal.completionOps.packet skb) (liftWG (getTxSkb skb)) :=
    focusPrefix_erases _ _ (Completion.access_erases (getTxSkbPrefix_erases skb))
  have appends : Appends (CausalJournal.completionOps.packet skb) := Appends.focus _ _ _
  obtain ⟨suffix,grown⟩ := appends w history
  have run : runPrefix (CausalJournal.completionOps.packet skb) w history =
      (.ok (packet,w),history ++ suffix) := Prod.ext ((erases w history).trans original) grown
  have quiet : ∀ event ∈ suffix, birthPackets event = [] :=
    focus_birth_free _ _ completion_encode_births _ w history suffix grown
  rw [runPrefix_captureObserved,run]
  exact ⟨suffix,rfl,before.append suffix quiet,original,rfl,resident⟩

theorem indexed_marker_checked (context : Context) (ledger : Ledger) (debts : List CleanupDebt) :
    Ensures (fun h w => Owned context (.sending context.items) h ledger debts w)
      (IndexedStopped context ledger debts)
      (CausalJournal.completionOps.completion context.pid context.items)
      (fun _ h w => Owned context (.sending context.items) h ledger debts w) := by
  intro w history before
  let event : CausalJournal.Event := .old (.disposition (.completion context.pid context.items))
  have run : runPrefix (CausalJournal.completionOps.completion context.pid context.items) w history =
      (.ok ((),w),history ++ [event]) := by
    exact focusPrefix_suffix FirstTerminal.encode CausalJournal.completion?
      (emitPrefix (.disposition (.completion context.pid context.items))) w history (.ok ((),w))
      [.disposition (.completion context.pid context.items)] (runPrefix_emit _ w _)
  rw [run]
  exact ⟨[event],rfl,before.append [event] (by intro e member; cases List.mem_singleton.mp member; rfl)⟩

theorem indexed_branch_checked (decision : Decision) (value : Bool) (context : Context)
    (phase : Phase) (ledger : Ledger) (debts : List CleanupDebt) (fact : Prop) :
    Ensures (fun h w => Owned context phase h ledger debts w ∧ fact)
      (IndexedStopped context ledger debts) (CausalJournal.completionOps.step (branch decision value))
      (fun _ h w => Owned context phase h ledger debts w ∧ fact) := by
  intro w history before
  rw [branch_run]
  exact ⟨[],by simp,before.1.sameWG rfl,before.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
