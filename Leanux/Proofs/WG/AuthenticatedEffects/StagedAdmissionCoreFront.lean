import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionCoreCheckpoint
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionMaterialObserved

/-! The actual whole front transports the complete fixed ledger carrier.
The caller supplies only the incoming Core, not disconnected intermediate
native cuts. Stop exposes its last accounted native checkpoint and backing. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal AllocatedObligation

def coreEntry (before : Core history ledger debts w) : Entry where
  history := history
  births := births history
  ledger := ledger
  world := w
  valid := before.valid
  bounded := births_bounded history
  queues := before.queues

theorem input_core {entry : Entry} (before : Core entry.history entry.ledger debts entry.world) (input : Input) :
    Core (entry.withInput input).history (entry.withInput input).ledger debts (entry.withInput input).world :=
  before.quiet_views [.transmitInput input] (by
    intro e member
    have same := List.mem_singleton.mp member
    subst e
    rfl) rfl rfl rfl

/-- Every normal actual front retains all allocated backing and cleanup debts,
while accounting for canonical admissions and any preceding counted disposal. -/
theorem core_normal (input : Input) (before : Core h ledger debts w)
    (a b : Ambient) (v : WGWorld) (history : List Event) (value : Except Int PeerId)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      w a h = (.ok ((value,v),b),history)) :
    ∃ after, Core history after debts v ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after := by
  let entry := coreEntry before
  obtain ⟨priorHistory,r,after,position,_,_,atAfter,_,normal⟩ :=
    normal_result entry input rfl a b v history value run
  have physical := Material.front_checked input w a h
  rw [run] at physical
  have equal : PacketOrigins.snapshot r.after = PacketOrigins.snapshot entry.world := by
    rw [atAfter]
    exact physical.2
  refine ⟨after,?_,normal.2.2.2.1⟩
  rw [position,←atAfter]
  exact normal.core (input_core (entry := entry) before input) equal

/-- A stopped actual front retains Core at its entry or its last completed
disposal cut, including the physical epoch/material equality to this entry.
There is no post-state assertion about a failed native continuation. -/
theorem core_stopped (input : Input) (before : Core h ledger debts w)
    (a : Ambient) (history : List Event) (stop : Stop)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      w a h = (.error stop,history)) :
    ∃ after snapshot, Checkpoint ((coreEntry before).withInput input) history after snapshot ∧
      Core history after debts snapshot ∧
      PacketOrigins.snapshot snapshot = PacketOrigins.snapshot w ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after := by
  let entry := coreEntry before
  obtain ⟨after,snapshot,cut,_,_,retained⟩ := stopped_conservation entry input rfl a history stop run
  have physical := Material.front_checked input w a h
  rw [run] at physical
  have equal := physical.1.checkpoint cut
  exact ⟨after,snapshot,cut,cut.core (entry.withInput_canonical input rfl) (input_core (entry := entry) before input) equal,equal,retained⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
