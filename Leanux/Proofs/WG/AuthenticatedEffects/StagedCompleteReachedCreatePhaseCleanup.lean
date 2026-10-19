import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseRelease

/-! Each original refused-batch free advances the ordered cleanup phase on
its exact singleton settlement. The silent erased-cell interval retains a
pending receipt and explicitly cannot retain the old allocated account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation CreatePoints
set_option maxHeartbeats 600000

theorem cut_dropped (cut : FreeCut reason pid skb remaining h ledger debts locals w) :
    Dropped (CleanupPrimitive.finished reason skb w cut.after h) cut.next reason skb := by
  refine ⟨cut.ticket,cut.position,cut.ordinal,cut.generation,cut.packet,
    (h++[CleanupPrimitive.readEvent w.wg skb,CleanupPrimitive.releaseEvent w.wg skb]).length,
    CleanupPrimitive.receipt reason skb w cut.after,cut.origin.append _,?_,?_,rfl,rfl,cut.terminal⟩
  · change (h++([CleanupPrimitive.readEvent w.wg skb,CleanupPrimitive.releaseEvent w.wg skb]++
      [CausalJournal.Event.terminalDrop (CleanupPrimitive.receipt reason skb w cut.after)]))[_]?=_
    rw [←List.append_assoc,List.getElem?_concat_length]
  · exact (FirstTerminal.labelled_cut reason skb w cut.after h _
      (CleanupPrimitive.cleanup_run skb w cut.after h cut.native)).1

theorem cut_pending (cut : FreeCut reason pid skb remaining h ledger debts locals w)
    (pending : PendingBatch h ledger (skb::remaining)) :
    PendingBatch (CleanupPrimitive.finished reason skb w cut.after h) cut.next remaining := by
  have unique : (skb::remaining).Nodup := (List.nodup_append.mp cut.entry.entry.inventory.localUnique).1
  have rest : PendingBatch h ledger remaining:=fun id member=>pending id (List.mem_cons_of_mem skb member)
  rw [cut.assigned]
  exact (rest.settle_other cut.entry.entry.core.valid cut.pending cut.origin (List.nodup_cons.mp unique).1 _).append _

theorem cut_phase (steps : Staged.Obligations.Step rootLedger ledger)
    (ordered : items=done++(skb::remaining)) (settled : AllDropped h ledger reason done)
    (cut : FreeCut reason pid skb remaining h ledger debts locals w)
    (pending : PendingBatch h ledger (skb::remaining)) :
    Live rootLedger debts locals pid items (CleanupPrimitive.finished reason skb w cut.after h) cut.after.wg := by
  refine .cleanup cut.next (steps.trans cut.step) reason (done++[skb]) remaining ?_ ?_
    (cut_pending cut pending) cut.accounted
  · simpa only [List.append_assoc,List.singleton_append] using ordered
  · intro id member
    rcases List.mem_append.mp member with old | current
    · exact (settled id old).transport _ cut.step
    · cases List.mem_singleton.mp current
      exact cut_dropped cut

theorem cleanup_covers (steps : Staged.Obligations.Step rootLedger ledger)
    (ordered : items=done++remaining) (settled : AllDropped h ledger reason done)
    (pending : PendingBatch h ledger remaining)
    (before : Accounted h ledger debts (⟨.unpublished,pid,remaining⟩::locals) w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (freeShape reason remaining) w h := by
  induction remaining generalizing done h ledger w with
  | nil=>exact covers_pure _ (.cleanup ledger steps reason done [] ordered settled pending before)
  | cons skb rest ih=>
    obtain ⟨cut⟩:=free_cut reason before pending
    unfold freeShape
    erw [covers_type_cast _ (loop_cons reason skb rest).symm]
    apply covers_bind (covers_child (.free reason skb) (.cleanup ledger steps reason done (skb::rest) ordered settled pending before) ?_)
    · intro ignored v last performed
      rw [cut.original] at performed
      cases performed
      apply ih (done:=done++[skb]) (steps.trans cut.step)
      · simpa only [List.append_assoc,List.singleton_append] using ordered
      · intro id member
        rcases List.mem_append.mp member with old | current
        · exact (settled id old).transport _ cut.step
        · cases List.mem_singleton.mp current
          exact cut_dropped cut
      · exact cut_pending cut pending
      · exact cut.accounted
    · intro value v last performed
      rw [cut.original] at performed
      cases performed
      exact cut_phase steps ordered settled cut pending

/-- Literal erased-cell subpoints carry the exact original pending receipt,
with the source run and remaining emission suffix retained by FreeCut. -/
theorem cleanup_pending (steps : Staged.Obligations.Step rootLedger ledger)
    (ordered : items=done++(skb::remaining)) (settled : AllDropped h ledger reason done)
    (cut : FreeCut reason pid skb remaining h ledger debts locals w) (phase : CleanupPrimitive.Phase) :
    Evidence rootLedger debts locals pid items (CleanupPrimitive.current phase w skb h) cut.after ∧
      runPrefix (CleanupPrimitive.atPhase phase w skb) w h=
        (.ok ((),cut.after),CleanupPrimitive.current phase w skb h) ∧
      runPrefix (free reason skb) w h=runPrefix (CleanupPrimitive.due phase reason skb w cut.after)
        cut.after (CleanupPrimitive.current phase w skb h) :=
  ⟨.awaiting ledger steps reason done ordered settled cut phase,
    (cut.pending_receipt phase).1,(cut.pending_receipt phase).2.2.1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
