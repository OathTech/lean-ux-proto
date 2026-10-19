import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionNative
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCounted

/-! The existing counted-disposal transition is applied at the real overflow
receipt before admission. It settles the removed old prefix exactly once;
subsequent birth admission retains those terminal records. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal

/-- Native overflow settles exactly the incoming prefix tickets at its own
receipt position and charges their count once. The retained queue and bounded
births are ready for the later actual splice admission. -/
theorem overflow (pid : PeerId) (r : WGRunWitness Unit)
    (run : r.Valid (Lifetimes.xmitTrim pid))
    (validBefore : Valid births ledger) (bounded : Bounded history.length births)
    (before : QueueInv history ledger r.before)
    (epoch : Packets.epoch r.before = some generation) :
    ∃ partition : HandshakeSecurity.StagedDisposal.Partition pid r.before r.after,
      let chosen := (pendingAt (.staged generation pid partition.stamp) ledger).take partition.removed
      let event := Event.stagedDisposal (.overflow pid r)
      let next := settle chosen (.counted history.length .overflow) ledger
      Staged.Obligations.Step ledger next ∧ Valid births next ∧
        Bounded (history ++ [event]).length births ∧
        QueueInv (history ++ [event]) next r.after ∧
        chosen.length = partition.removed ∧
        (∀ ticket ∈ chosen, (ticket,Status.terminal (.counted history.length .overflow)) ∈ next) ∧
        (∃ count, Staged.dropped r.before = some count ∧ Staged.dropped r.after = some (count+chosen.length)) ∧
        (∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
          (ticket,Status.terminal outcome) ∈ next) := by
  obtain ⟨partition⟩ := HandshakeSecurity.StagedDisposal.overflow_exact pid r run
  obtain ⟨step,validNext,queues,count,settled,charged⟩ :=
    counted_step partition validBefore before epoch history.length .overflow
  refine ⟨partition,step,validNext,bounded_mono bounded (by simp),queues.append_history _,count,settled,charged,?_⟩
  intro ticket outcome member
  exact step.terminal member

/-- The first counted overflow outcome remains unique after a later fresh
birth append. Cleanup and equal new payloads cannot relabel that ticket. -/
theorem settled_retained_after_admission
    (validBefore : Valid births ledger) (bounded : Bounded position births)
    (step : Staged.Obligations.Step ledger settled)
    (already : (ticket,Status.terminal outcome) ∈ settled)
    (later : (ticket,status) ∈ appendBirths settled position location packets) :
    status = .terminal outcome :=
  terminal_unchanged (step.valid validBefore) bounded already later

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission
