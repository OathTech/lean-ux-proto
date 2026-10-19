import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalProvenanceCounted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionCoreFront

/-! Whole-front source transport preserves terminal meaning along with Core.
Stopped prefixes retain the very same accounted ledger and native snapshot,
including an overflow or final release completed before a later Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal AllocatedObligation StagedAdmission.Front

theorem front_normal (input : Input) (before : Core h ledger debts w)
    (justified : Justified h ledger) (links : AllocationLinks h ledger) (a b : Ambient) (v : WGWorld)
    (history : List Event) (value : Except Int PeerId)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      w a h = (.ok ((value,v),b),history)) :
    ∃ after, Core history after debts v ∧ Justified history after ∧ AllocationLinks history after ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after := by
  let entry := coreEntry before
  obtain ⟨priorHistory,r,after,position,_,_,atAfter,_,accounted⟩ :=
    normal_result entry input rfl a b v history value run
  have physical := Material.front_checked input w a h
  rw [run] at physical
  have equal : PacketOrigins.snapshot r.after = PacketOrigins.snapshot entry.world := by
    rw [atAfter]
    exact physical.2
  refine ⟨after,?_,?_,?_,accounted.2.2.2.1⟩
  · rw [position,←atAfter]
    exact accounted.core (input_core (entry := entry) before input) equal
  · rw [position]
    exact normal accounted (justified.append [.transmitInput input])
  · rw [position]
    exact normal_links accounted (links.append [.transmitInput input])

theorem front_stopped (input : Input) (before : Core h ledger debts w)
    (justified : Justified h ledger) (links : AllocationLinks h ledger) (a : Ambient) (history : List Event) (stop : Stop)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      w a h = (.error stop,history)) :
    ∃ after snapshot, Checkpoint ((coreEntry before).withInput input) history after snapshot ∧
      Core history after debts snapshot ∧ Justified history after ∧ AllocationLinks history after ∧
      PacketOrigins.snapshot snapshot = PacketOrigins.snapshot w ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after := by
  obtain ⟨after,snapshot,cut,core,physical,retained⟩ :=
    core_stopped input before a history stop run
  exact ⟨after,snapshot,cut,core,checkpoint cut (justified.append [.transmitInput input]),
    checkpoint_links cut (links.append [.transmitInput input]),physical,retained⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
