import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSelectedPositions
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationStoppedTake

/-! Fixed-ticket accounting at the actual staging take. The position bound is
transported from preceding take receipts, and the accounting cut precedes key
borrowing. This local source theorem retains meaningful accounting on Stop;
initialized transport and the later checked continuation are separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
open HandshakeSecurity.StagedConservation

structure TakeAccounted (births : List Ticket) (before : Ledger) (history : List Event)
    (r : Take.Receipt) (after : Ledger) : Prop where
  step : Step before after
  valid : Valid births after
  queues : QueueInv (history ++ [.stagingTaken r]) after r.run.after
  selected : SelectedRecorded (history ++ [.stagingTaken r]) after
  exactTransfer : match r.run.value with
    | none => after = before
    | some peer => ∃ generation,
        Packets.epoch r.run.before = some generation ∧
        after = transferLocation (.staged generation r.pid peer.internalId)
          (.selected history.length) before ∧
        pendingAt (.selected history.length) after =
          pendingAt (.staged generation r.pid peer.internalId) before ∧
        Aligned (Born (history ++ [.stagingTaken r]) generation r.pid peer.internalId)
          (pendingAt (.selected history.length) after) peer.staged

/-- Every completed take accounts for its whole native queue before key
borrowing. The next selected position is fresh by prior recorded positions,
including after earlier completed, empty or stopped selections. -/
theorem take_accounted (r : Take.Receipt) (native : r.Valid)
    (valid : Valid births ledger) (queues : QueueInv history ledger r.run.before)
    (selected : SelectedRecorded history ledger) :
    ∃ after, TakeAccounted births ledger history r after := by
  cases result : r.run.value with
  | none =>
    exact ⟨ledger,Step.refl ledger,valid,
      (take_none_step r native result queues).append_history _,selected.append _,result ▸ rfl⟩
  | some peer =>
    obtain ⟨generation,epoch,_⟩ := take_receipt_views r native peer result
    let after := transferLocation (.staged generation r.pid peer.internalId)
      (.selected history.length) ledger
    obtain ⟨step,kept,afterQueues,located,aligned,_,_⟩ :=
      take_step r native peer result valid queues epoch history.length selected.fresh
    refine ⟨after,step,kept,afterQueues.append_history _,selected.taken r generation peer.internalId,?_⟩
    rw [result]
    exact ⟨generation,epoch,rfl,located,located ▸ aligned.history_append _⟩

/-- Key borrowing has no opportunity to lose the completed take's ledger.
This exact source identity exposes the same native borrow result and keeps
its accounted cut even when there is no completed outer selection receipt. -/
theorem selection_after_accounted_take (r : Take.Receipt) (native : r.Valid)
    (valid : Valid births ledger) (queues : QueueInv history ledger r.run.before)
    (selected : SelectedRecorded history ledger) :
    ∃ after, TakeAccounted births ledger history r after ∧
      runWGPrefix (CausalJournal.selection r.pid) r.run.before r.run.ambientBefore history =
        let borrowed := ((Take.borrow r.run.value).run r.run.after).run r.run.ambientAfter
        match borrowed with
        | .error stop => (.error stop,history ++ [.stagingTaken r])
        | .ok ((value,w),a) => (.ok ((value,w),a),
            (history ++ [.stagingTaken r]) ++
              [.old (.responder (.selected r.pid
                ⟨value,r.run.before,w,r.run.ambientBefore,a⟩))]) := by
  obtain ⟨after,accounted⟩ := take_accounted r native valid queues selected
  refine ⟨after,accounted,?_⟩
  have taken := Take.observed_after_take Event.stagingTaken r.pid
    r.run.before r.run.after r.run.ambientBefore r.run.ambientAfter history r.run.value native
  have same : (⟨r.pid,⟨r.run.value,r.run.before,r.run.after,r.run.ambientBefore,r.run.ambientAfter⟩⟩ : Take.Receipt) = r := by
    cases r with
    | mk pid run => cases run; rfl
  rw [same,runWGPrefix_lift] at taken
  have outer := runWGPrefix_receiptWGObserved (Take.observed Event.stagingTaken r.pid)
    (fun run => Event.old (.responder (.selected r.pid run))) r.run.before r.run.ambientBefore history
  rw [taken] at outer
  unfold CausalJournal.selection Take.selection
  cases borrowed : ((Take.borrow r.run.value).run r.run.after).run r.run.ambientAfter with
  | error stop => simpa only [borrowed] using outer
  | ok out =>
    obtain ⟨⟨value,w⟩,a⟩ := out
    simpa only [borrowed] using outer

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
