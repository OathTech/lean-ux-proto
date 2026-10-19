import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontCheckpoint
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCompleteCarrier

/-! Paired accounting through the actual routed front. A Stop retains the
original or completed counted cut; normal admission uses the same exact
successor for ownership, terminal provenance and receipt completeness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteFront
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal StagedProvenance StagedAdmission.Front StagedTerminalComplete CompleteCarrier

theorem front_normal (input : Input) (before : Accounted h ledger debts locals w)
    (a b : Ambient) (v : WGWorld) (history : List Event) (value : Except Int PeerId)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      w a h = (.ok ((value,v),b),history)) :
    ∃ after, Accounted history after debts locals v ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after := by
  let entry := coreEntry before.entry.core
  obtain ⟨priorHistory,r,after,position,_,_,atAfter,_,accounted⟩ :=
    normal_result entry input rfl a b v history value run
  have material := Material.front_checked input w a h
  have ownership := Ownership.front_checked input w a h
  rw [run] at material ownership
  have equal : PacketOrigins.snapshot r.after = PacketOrigins.snapshot entry.world := by
    rw [atAfter]
    exact material.2
  have native := physical before.entry ownership.2
  have complete : Complete ((entry.withInput input).history) entry.ledger :=
    before.complete.append_quiet (fun _ member => by cases List.mem_singleton.mp member; intro pos; rfl)
  refine ⟨after,⟨?_,?_⟩,accounted.2.2.2.1⟩
  · refine ⟨?_,?_,?_,normal_no_selected accounted before.entry.noSelected,
      native.1,native.2.1,native.2.2⟩
    · rw [position,←atAfter]
      exact accounted.core (input_core (entry := entry) before.entry.core input) equal
    · rw [position]
      exact StagedProvenance.normal accounted (before.entry.justified.append [.transmitInput input])
    · rw [position]
      exact normal_links accounted (before.entry.allocationLinks.append [.transmitInput input])
  · rw [position]
    exact normal accounted (before.entry.justified.append [.transmitInput input]) complete

theorem front_stopped (input : Input) (before : Accounted h ledger debts locals w)
    (a : Ambient) (history : List Event) (stop : Stop)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      w a h = (.error stop,history)) :
    ∃ after snapshot, Checkpoint ((coreEntry before.entry.core).withInput input) history after snapshot ∧
      Accounted history after debts locals snapshot ∧
      PacketOrigins.snapshot snapshot = PacketOrigins.snapshot w ∧
      Ownership.view snapshot = Ownership.view w := by
  obtain ⟨after,snapshot,cut,inv,material,ownership,_⟩ :=
    StagedEntry.front_stopped input before.entry a history stop run
  refine ⟨after,snapshot,cut,⟨inv,?_⟩,material,ownership⟩
  apply checkpoint cut (before.entry.justified.append [.transmitInput input])
  exact before.complete.append_quiet
    (fun _ member => by cases List.mem_singleton.mp member; intro position; rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteFront
