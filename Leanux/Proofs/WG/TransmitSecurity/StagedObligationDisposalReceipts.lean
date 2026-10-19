import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRelease

/-! Native disposal receipts bind the terminal arm and journal position.
The incoming ledger invariant remains explicit until Runner transport closes. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins
open AuthenticatedEffects.CausalJournal

theorem purge_receipt (pid : PeerId) (r : WGRunWitness Unit)
    (run : r.Valid (purgeStagedPackets pid))
    (valid : Valid births ledger) (before : QueueInv history ledger r.before)
    (epoch : Packets.epoch r.before = some generation) :
    ∃ stamp after,
      Step ledger after ∧ Valid births after ∧
      QueueInv (history ++ [.stagedDisposal (.purge pid r)]) after r.after ∧
      (∀ ticket ∈ pendingAt (.staged generation pid stamp) ledger,
        (ticket,Status.terminal (.counted history.length .purge)) ∈ after) ∧
      (∃ count, dropped r.before = some count ∧ dropped r.after =
        some (count+(pendingAt (.staged generation pid stamp) ledger).length)) := by
  obtain ⟨partition,whole⟩ := HandshakeSecurity.StagedDisposal.purge_exact pid r run
  let tickets := pendingAt (.staged generation pid partition.stamp) ledger
  have aligned : Aligned (Born history generation pid partition.stamp) tickets partition.packets := by
    have related := before generation pid partition.stamp
    rw [partition_before partition epoch] at related
    exact related
  have length := HandshakeSecurity.StagedConservation.aligned_length aligned
  have all : tickets.take partition.removed = tickets := by
    rw [whole,← length,List.take_length]
  obtain ⟨step,kept,queues,_,settled,charged⟩ :=
    counted_step partition valid before epoch history.length .purge
  change Step ledger (settle (tickets.take partition.removed) _ ledger) at step
  change Valid births (settle (tickets.take partition.removed) _ ledger) at kept
  change QueueInv history (settle (tickets.take partition.removed) _ ledger) r.after at queues
  change ∀ ticket ∈ tickets.take partition.removed, _ at settled
  change ∃ count, dropped r.before = some count ∧
    dropped r.after = some (count+(tickets.take partition.removed).length) at charged
  rw [all] at step kept queues settled charged
  refine ⟨partition.stamp,_,step,kept,queues.append_history _,?_,charged⟩
  exact settled

theorem release_receipt (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer)))
    (run : r.Valid (HandshakeSecurity.StagedDisposal.releaseCut peer))
    (released : r.value = some (pid,p))
    (valid : Valid births ledger) (before : QueueInv history ledger r.before)
    (epoch : Packets.epoch r.before = some generation) :
    ∃ after,
      Step ledger after ∧ Valid births after ∧
      QueueInv (history ++ [.stagedDisposal (.release peer r)]) after r.after ∧
      (∀ ticket ∈ pendingAt (.staged generation pid p.internalId) ledger,
        (ticket,Status.terminal (.counted history.length .finalRelease)) ∈ after) ∧
      (∃ count, dropped r.before = some count ∧ dropped r.after =
        some (count+(pendingAt (.staged generation pid p.internalId) ledger).length)) := by
  obtain ⟨step,kept,queues,settled,charged⟩ :=
    release_step peer r run released valid before epoch history.length
  exact ⟨_,step,kept,queues.append_history _,settled,charged⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
