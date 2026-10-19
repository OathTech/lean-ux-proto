import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionOverflow
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationDisposalReceipts

/-! Before a front admits new packets, it can pass one counted disposal.
A stopped path retains the actual entry or completed disposal checkpoint and
its exact fixed ledger; it is never discharged by a trivial error predicate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal

structure Entry where
  history : List Event
  births : List Ticket
  ledger : Ledger
  world : WGWorld
  valid : Valid births ledger
  bounded : Bounded history.length births
  queues : QueueInv history ledger world

/-- The history is the complete front prefix at the accounted cut. The
snapshot is the actual entry state or the after-state of its native receipt. -/
inductive Checkpoint (entry : Entry) : List Event → Ledger → WGWorld → Prop where
  | initial : Checkpoint entry entry.history entry.ledger entry.world
  | nonfinal (peer : Option PeerId) (r : WGRunWitness (Option (PeerId × Peer)))
      (run : r.Valid (HandshakeSecurity.StagedDisposal.releaseCut peer)) (value : r.value = none)
      (queues : QueueInv entry.history entry.ledger r.after) :
      Checkpoint entry (entry.history ++ [.stagedDisposal (.release peer r)]) entry.ledger r.after
  | released (peer : Option PeerId) (r : WGRunWitness (Option (PeerId × Peer)))
      (run : r.Valid (HandshakeSecurity.StagedDisposal.releaseCut peer))
      (pid : PeerId) (p : Peer) (value : r.value = some (pid,p))
      (generation : Nat) (epoch : Packets.epoch r.before = some generation)
      (queues : QueueInv entry.history entry.ledger r.before) :
      Checkpoint entry (entry.history ++ [.stagedDisposal (.release peer r)])
        (settle (pendingAt (.staged generation pid p.internalId) entry.ledger)
          (.counted entry.history.length .finalRelease) entry.ledger) r.after
  | trimmed (pid : PeerId) (r : WGRunWitness Unit)
      (run : r.Valid (Lifetimes.xmitTrim pid))
      (partition : HandshakeSecurity.StagedDisposal.Partition pid r.before r.after)
      (generation : Nat) (epoch : Packets.epoch r.before = some generation)
      (queues : QueueInv entry.history entry.ledger r.before) :
      Checkpoint entry (entry.history ++ [.stagedDisposal (.overflow pid r)])
        (settle ((pendingAt (.staged generation pid partition.stamp) entry.ledger).take partition.removed)
          (.counted entry.history.length .overflow) entry.ledger) r.after

theorem Checkpoint.accounted (cut : Checkpoint entry history ledger snapshot) :
    Staged.Obligations.Step entry.ledger ledger ∧ Valid entry.births ledger ∧
      Bounded history.length entry.births ∧ QueueInv history ledger snapshot := by
  cases cut with
  | initial => exact ⟨.refl _,entry.valid,entry.bounded,entry.queues⟩
  | nonfinal peer r run value queues =>
    exact ⟨.refl _,entry.valid,bounded_mono entry.bounded (by simp),queues.append_history _⟩
  | released peer r run pid p value generation epoch queues =>
    obtain ⟨step,valid,after,_,_⟩ := release_step peer r run value entry.valid queues epoch entry.history.length
    exact ⟨step,valid,bounded_mono entry.bounded (by simp),after.append_history _⟩
  | trimmed pid r run partition generation epoch queues =>
    obtain ⟨step,valid,after,_,_,_⟩ := counted_step partition entry.valid queues epoch entry.history.length .overflow
    exact ⟨step,valid,bounded_mono entry.bounded (by simp),after.append_history _⟩

def Safe (entry : Entry) (history : List Event) : Prop :=
  ∃ ledger snapshot, Checkpoint entry history ledger snapshot

def Carry (entry : Entry) (history : List Event) (w : WGWorld) (_a : Ambient) : Prop :=
  ∃ ledger snapshot, Checkpoint entry history ledger snapshot ∧ QueueInv history ledger w

theorem Carry.safe (before : Carry entry history w a) : Safe entry history := by
  obtain ⟨ledger,snapshot,cut,_⟩ := before
  exact ⟨ledger,snapshot,cut⟩

theorem initial : Carry entry entry.history entry.world a :=
  ⟨entry.ledger,entry.world,.initial,entry.queues⟩

theorem carry_native {action : WG.M α}
    (frame : ∀ history ledger, Leanux.Proofs.Framing.Preserves (QueueInv history ledger) action) :
    StatePrefixPreserves (Carry entry) (Safe entry) (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift
  · intro history w a before
    exact before.safe
  · intro history w a value v b before run
    obtain ⟨ledger,snapshot,cut,queues⟩ := before
    exact ⟨ledger,snapshot,cut,(Leanux.Proofs.Framing.hoare_iff_run_ambient _ _ _).mp
      (frame history ledger) w a value v b queues run⟩

/-- A retained checkpoint has the same old keys and cannot lose or replace
an earlier terminal outcome, including after a stopped suffix. -/
theorem Safe.retains (safe : Safe entry history) :
    ∃ ledger snapshot, Checkpoint entry history ledger snapshot ∧
      Valid entry.births ledger ∧ QueueInv history ledger snapshot ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ entry.ledger →
        (ticket,Status.terminal outcome) ∈ ledger := by
  obtain ⟨ledger,snapshot,cut⟩ := safe
  obtain ⟨step,valid,_,queues⟩ := cut.accounted
  exact ⟨ledger,snapshot,cut,valid,queues,fun _ _ member => step.terminal member⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
