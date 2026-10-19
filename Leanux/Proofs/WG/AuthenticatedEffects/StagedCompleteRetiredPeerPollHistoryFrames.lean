import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollBoundaryFrames
import Leanux.Proofs.WG.Queues.HolderNapi

/-! The original poll and NAPI observers retain the same exact peer account,
subtracting only their actual fresh removal suffix. These are normal endpoint
contracts; no endpoint world is invented for a stopped native action. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.ExactAt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
open NapiCarrier (removed removedPackets promote_removed normal_spec)

theorem observePoll (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (pid budget : Nat) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) (RxHistory.observePoll pid budget) := by
  apply normal_spec (RxHistory.observePoll_appends pid budget)
  intro w h n v hi hr
  obtain ⟨old,history,hstable⟩ := hi
  obtain ⟨fresh,hfresh⟩ := RxJoint.poll_appends pid budget w (RxJoint.seed (RxHistory.prior h))
  have global := RxHistory.observePoll_suffix pid budget w h _ fresh (Prod.ext rfl hfresh)
  have original := (RxHistory.observePoll_erases pid budget w h).symm.trans hr
  have post := Poll.normal pid budget w v n
    (remaining initial (removedPackets old)) loans (RxHistory.prior h) hstable original
  have freshRemoved : PollCarrier.removedPackets
      (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior h))).2 =
      PollCarrier.removedPackets fresh := by
    rw [hfresh]
    simp only [PollCarrier.removedPackets,RxJoint.removedStamps,List.filterMap_append,List.map_append]
    change PollCarrier.removedPackets (RxJoint.seed _) ++ _ = _
    rw [PollCarrier.seed_removedPackets,List.nil_append]
  refine ⟨old ++ fresh.map RxHistory.promote,?_,?_⟩
  · rw [global]
    simp only [history,List.append_assoc]
  · simp only [removedPackets,List.filterMap_append]
    change ExactBoundary (remaining initial (removedPackets old ++ removedPackets (fresh.map RxHistory.promote))) loans v.wg
    rw [promote_removed,remaining_append]
    simpa only [freshRemoved] using post.1

theorem audit_frame (a : AuditM α) (original : Leanux.M α)
    (erase : ErasesPrefix a original) (same : SameProductStore original) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) (RxHistory.audit a) :=
  ExactAt.frame _ _ id (Appends.focus _ _ _) (RxHistory.audit_erases erase).to_projected same
    (fun w h => focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent removed (fun _ => rfl) a w h)

private theorem pending_store : SameProductStore (liftWG RxNapi.pendingSource) := by
  apply liftWG_sameProductStore
  unfold RxNapi.pendingSource
  exact getDev_sameWGStore.bind (fun d => SameView.pure _ _)

private theorem scheduled_store : SameProductStore (liftWG RxNapi.scheduledSource) := by
  apply liftWG_sameProductStore
  unfold RxNapi.scheduledSource
  exact getDev_sameWGStore.bind (fun d => SameView.pure _ _)

theorem softirq_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) RxHistory.napiSoftirq := by
  unfold RxHistory.napiSoftirq
  apply RxNapi.softirq_preserves (I := ExactAt initial loans before) (fun _ _ _ => True.intro) (fun _ _ _ he hi => ExactAt.store hi he)
  · exact audit_frame _ _ (auditFocus_erases (liftWGObserver_erases RxNapi.pending_erases)) pending_store
  · exact observePoll initial loans before

theorem inline_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) RxHistory.pollScheduledInline := by
  unfold RxHistory.pollScheduledInline
  apply RxNapi.inline_preserves (I := ExactAt initial loans before) (fun _ _ _ => True.intro) (fun _ _ _ he hi => ExactAt.store hi he)
  · exact audit_frame _ _ (auditFocus_erases (liftWGObserver_erases RxNapi.pending_erases)) pending_store
  · exact observePoll initial loans before

theorem irq_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) RxHistory.napiIrqExit := by
  unfold RxHistory.napiIrqExit
  apply RxNapi.irqExit_preserves (I := ExactAt initial loans before) (fun _ _ _ => True.intro) (fun _ _ _ he hi => ExactAt.store hi he)
  · exact audit_frame _ _ (auditFocus_erases (liftWGObserver_erases RxNapi.scheduled_erases)) scheduled_store
  · exact softirq_preserves initial loans before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.ExactAt
