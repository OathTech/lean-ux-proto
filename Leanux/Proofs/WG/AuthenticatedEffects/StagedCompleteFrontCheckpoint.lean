import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteLedgerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteSettlement
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryFront

/-! Front accounting is paired at its existing exact checkpoint. Counted
overflow and final release settle that checkpoint's fixed incoming tickets;
the routed receipt appends births without changing older terminal counts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteFront
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal StagedProvenance StagedAdmission.Front StagedTerminalComplete

theorem checkpoint (cut : Checkpoint entry history ledger snapshot)
    (justified : Justified entry.history entry.ledger)
    (complete : Complete entry.history entry.ledger) : Complete history ledger := by
  cases cut with
  | initial => exact complete
  | nonfinal peer r native value queues =>
    apply complete.append_quiet
    intro event member
    cases List.mem_singleton.mp member
    exact release_none_quiet value
  | released peer r native pid p value generation epoch queues =>
    obtain ⟨device,_,present,resident,_,_,_,_,_⟩ :=
      HandshakeSecurity.StagedDisposal.release_exact peer r native pid p value
    have staged : Staged.stagedAt r.before pid = some (p.internalId,p.staged) := by
      simp only [Staged.stagedAt,present,Option.bind_some,resident,Option.map_some]
    have aligned := queues generation pid p.internalId
    simp only [stagedPackets,epoch,staged,ite_true,eq_self] at aligned
    apply complete.settle_cut
      (chosen := pendingAt (.staged generation pid p.internalId) entry.ledger)
      (requested := ⟨.counted entry.history.length .finalRelease,p.staged.length⟩)
      entry.valid justified
      (pendingAt_unique (entry.valid.1.symm ▸ entry.valid.2) _)
    · intro ticket member
      exact ⟨_,mem_pendingAt.mp member⟩
    · exact release_some_demand value
    · exact HandshakeSecurity.StagedConservation.aligned_length aligned
  | trimmed pid r native partition generation epoch queues =>
    obtain ⟨_,_,_,count,_,_⟩ :=
      counted_step partition entry.valid queues epoch entry.history.length .overflow
    apply complete.settle_cut
      (chosen := (pendingAt (.staged generation pid partition.stamp) entry.ledger).take partition.removed)
      (requested := ⟨.counted entry.history.length .overflow,partition.removed⟩)
      entry.valid justified
      (pendingAt_unique (entry.valid.1.symm ▸ entry.valid.2) _).take
    · intro ticket member
      exact ⟨_,mem_pendingAt.mp (List.mem_of_mem_take member)⟩
    · exact overflow_demand partition
    · exact count

/-- This uses the very ledger returned by the actual front, rather than
choosing a separate existential successor for the converse. -/
theorem normal (result : Normal entry input r history ledger)
    (justified : Justified entry.history entry.ledger)
    (complete : Complete entry.history entry.ledger) :
    Complete (history ++ [routedEvent input r]) ledger := by
  obtain ⟨_,_,_,_,prior,snapshot,cut,next⟩ := result
  have priorComplete := checkpoint cut justified complete
  have routedQuiet : StagedTerminalComplete.Quiet (routedEvent input r) := by intro position; rfl
  cases value : r.value with
  | error code =>
    simp only [value] at next
    rw [next.1]
    exact priorComplete.append_quiet (fun _ member => List.mem_singleton.mp member ▸ routedQuiet)
  | ok pid =>
    simp only [value] at next
    obtain ⟨w,a,generation,stamp,_,_,rfl⟩ := next
    exact (priorComplete.admitted history.length (.staged generation pid stamp)
      (input.packets.map (fun p => {p with mtu := input.mtu}))).append_quiet
        (fun _ member => List.mem_singleton.mp member ▸ routedQuiet)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteFront
