import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTake
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource

/-! Exact accounting at the stopped borrow frontier. The completed take cut
retains its native snapshot and every fixed ticket although the enclosing
selection produces no completed-selection receipt. This local theorem does
not supply the incoming ledger or the initialized source carrier. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins
open AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity.StagedConservation

theorem selection_borrow_stop (r : Take.Receipt) (valid : r.Valid)
    (stopped : ((Take.borrow r.run.value).run r.run.after).run r.run.ambientAfter = .error stop)
    (history : List Event) :
    runWGPrefix (CausalJournal.selection r.pid) r.run.before r.run.ambientBefore history =
      (.error stop,history ++ [.stagingTaken r]) := by
  have taken := Take.observed_after_take Event.stagingTaken r.pid
    r.run.before r.run.after r.run.ambientBefore r.run.ambientAfter history r.run.value valid
  have receipt : (⟨r.pid,⟨r.run.value,r.run.before,r.run.after,r.run.ambientBefore,r.run.ambientAfter⟩⟩ : Take.Receipt) = r := by
    cases r with
    | mk pid run => cases run; rfl
  rw [receipt,runWGPrefix_lift,stopped] at taken
  have outer := runWGPrefix_receiptWGObserved (Take.observed Event.stagingTaken r.pid)
    (fun run => Event.old (.responder (.selected r.pid run))) r.run.before r.run.ambientBefore history
  rw [taken] at outer
  exact outer

/-- A Stop while borrowing the current key cannot erase a staged packet:
every incoming birth still has exactly one status, the taken tickets occupy
the actual caller-local take position, and all older terminal results remain.
The queue and plaintext witnesses are tied to the retained native take cut. -/
theorem stopped_take_accounted (r : Take.Receipt) (run : r.Valid)
    (peer : Peer) (chosen : r.run.value = some peer)
    (stopped : ((Take.borrow r.run.value).run r.run.after).run r.run.ambientAfter = .error stop)
    (valid : Valid births ledger) (before : QueueInv history ledger r.run.before)
    (epoch : Packets.epoch r.run.before = some generation)
    (unused : pendingAt (.selected history.length) ledger = []) :
    let source := Pending.staged generation r.pid peer.internalId
    let after := transferLocation source (.selected history.length) ledger
    let retained := history ++ [Event.stagingTaken r]
    runWGPrefix (CausalJournal.selection r.pid) r.run.before r.run.ambientBefore history =
      (.error stop,retained) ∧
    Step ledger after ∧ Valid births after ∧ QueueInv retained after r.run.after ∧
    pendingAt (.selected history.length) after = pendingAt source ledger ∧
    Aligned (Born retained generation r.pid peer.internalId) (pendingAt source ledger) peer.staged ∧
    (∀ ticket ∈ births, ∃ status, (ticket,status) ∈ after ∧
      ∀ other, (ticket,other) ∈ after → other = status) ∧
    (∀ ticket outcome, (ticket,.terminal outcome) ∈ ledger →
      (ticket,.terminal outcome) ∈ after) := by
  dsimp only
  obtain ⟨step,kept,queues,selected,aligned,_,terminals⟩ :=
    take_step r run peer chosen valid before epoch history.length unused
  refine ⟨selection_borrow_stop r run stopped history,step,kept,
    queues.append_history [Event.stagingTaken r],selected,?_,?_,terminals⟩
  · exact aligned.history_append _
  · intro ticket born
    exact step.total_partition valid born

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
