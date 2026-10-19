import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryFrontClosure

/-! The complete enriched front preserves one entry bundle. Normal and stopped
results use its actual routed/disposal prefix and the same accounted ledger;
no unrelated native snapshot is supplied as an ownership premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal RetirementSecurity StagedProvenance StagedAdmission.Front

private theorem physical (before : Inv h ledger debts locals w)
    (same : Ownership.view v = Ownership.view w) :
    Packets.Inv v ∧ TxCoverage locals v ∧ TxInventory locals v := by
  have snapshot : Packets.snapshot v = Packets.snapshot w := congrArg (fun x => x.1.1) same
  have cells : Queues.TxDisposition.txPackets v = Queues.TxDisposition.txPackets w :=
    congrArg (fun x => x.1.2) same
  have owners : txQueueContents v = txQueueContents w := congrArg Prod.snd same
  exact ⟨by simpa only [Packets.Inv,snapshot] using before.packets,
    before.coverage.cells cells owners,before.inventory.queueContents owners cells⟩

/-- The actual full front transports canonical ledger meaning and native TX
ownership, including rejected fronts and counted overflow before splice. -/
theorem front_normal (input : Input) (before : Inv h ledger debts locals w)
    (a b : Ambient) (v : WGWorld) (history : List Event) (value : Except Int PeerId)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      w a h = (.ok ((value,v),b),history)) :
    ∃ after, Inv history after debts locals v ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after := by
  let entry := coreEntry before.core
  obtain ⟨priorHistory,r,after,position,_,_,atAfter,_,accounted⟩ :=
    normal_result entry input rfl a b v history value run
  have material := Material.front_checked input w a h
  have ownership := Ownership.front_checked input w a h
  rw [run] at material ownership
  have equal : PacketOrigins.snapshot r.after = PacketOrigins.snapshot entry.world := by
    rw [atAfter]
    exact material.2
  have native := physical before ownership.2
  refine ⟨after,?_,accounted.2.2.2.1⟩
  refine ⟨?_,?_,?_,normal_no_selected accounted before.noSelected,native.1,native.2.1,native.2.2⟩
  · rw [position,←atAfter]
    exact accounted.core (input_core (entry := entry) before.core input) equal
  · rw [position]
    exact StagedProvenance.normal accounted (before.justified.append [.transmitInput input])
  · rw [position]
    exact normal_links accounted (before.allocationLinks.append [.transmitInput input])

/-- A stopped front retains its actual entry or last completed counted cut.
The complete ownership bundle holds at that cut, with exact native allocation
frontier, packet records and owning queues connected to this invocation. -/
theorem front_stopped (input : Input) (before : Inv h ledger debts locals w)
    (a : Ambient) (history : List Event) (stop : Stop)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      w a h = (.error stop,history)) :
    ∃ after snapshot, Checkpoint ((coreEntry before.core).withInput input) history after snapshot ∧
      Inv history after debts locals snapshot ∧
      PacketOrigins.snapshot snapshot = PacketOrigins.snapshot w ∧
      Ownership.view snapshot = Ownership.view w ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after := by
  obtain ⟨after,snapshot,cut,core,material,retained⟩ :=
    core_stopped input before.core a history stop run
  have ownership := Ownership.front_checked input w a h
  rw [run] at ownership
  have same : Ownership.view snapshot = Ownership.view w := ownership.1.checkpoint cut
  have native := physical before same
  exact ⟨after,snapshot,cut,⟨core,
    checkpoint cut (before.justified.append [.transmitInput input]),
    checkpoint_links cut (before.allocationLinks.append [.transmitInput input]),
    checkpoint_no_selected cut before.noSelected,native.1,native.2.1,native.2.2⟩,
    material,same,retained⟩

/-- Stop is presented by a connected accounted cut, never by True. This result
is local to the actual front invocation; full Driver transport remains separate. -/
def Finished (before : Inv h ledger debts locals w) (input : Input)
    (history : List Event) : Prop :=
  (∃ after snapshot, Checkpoint ((coreEntry before.core).withInput input) history after snapshot ∧
    Inv history after debts locals snapshot ∧ PacketOrigins.snapshot snapshot = PacketOrigins.snapshot w ∧
    Ownership.view snapshot = Ownership.view w) ∨
  (∃ after snapshot, Inv history after debts locals snapshot)

theorem front_checked (input : Input) (before : Inv h ledger debts locals w) (a : Ambient) :
    let result := runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h
    Finished before input result.2 ∧
      match result.1 with
      | .error _ => ∃ after snapshot, Checkpoint ((coreEntry before.core).withInput input) result.2 after snapshot ∧
          Inv result.2 after debts locals snapshot
      | .ok ((_,v),_) => ∃ after, Inv result.2 after debts locals v := by
  cases executed : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h with
  | mk result history =>
    cases result with
    | error stop =>
      obtain ⟨after,snapshot,cut,inv,material,ownership,_⟩ := front_stopped input before a history stop executed
      exact ⟨Or.inl ⟨after,snapshot,cut,inv,material,ownership⟩,after,snapshot,cut,inv⟩
    | ok out =>
      rcases out with ⟨⟨value,v⟩,b⟩
      obtain ⟨after,inv,_⟩ := front_normal input before a b v history value executed
      exact ⟨Or.inr ⟨after,v,inv⟩,after,inv⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
