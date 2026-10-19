import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteConverse
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPurgeSource

/-! The actual purge settles the same incoming staged tickets in Entry and
Complete. The completed native receipt is the only new terminal demand;
a native Stop retains the unchanged history and ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete.Source
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal StagedProvenance HandshakeSecurity.StagedDisposal

theorem purge_receipt (pid : PeerId) (r : WGRunWitness Unit)
    (native : r.Valid (purgeStagedPackets pid))
    (before : StagedEntry.Inv history ledger debts locals r.before) (complete : Complete history ledger) :
    ∃ (part : Partition pid r.before r.after) (generation : Nat),
      part.removed = part.packets.length ∧ Packets.epoch r.before = some generation ∧
      let chosen := (pendingAt (.staged generation pid part.stamp) ledger).take part.removed
      let after := settle chosen (.counted history.length .purge) ledger
      Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
      StagedEntry.Inv (history ++ [.stagedDisposal (.purge pid r)]) after debts locals r.after ∧
      Complete (history ++ [.stagedDisposal (.purge pid r)]) after ∧
      chosen.length = part.removed := by
  obtain ⟨part,generation,whole,epoch,step,frame,entry,count,_,_⟩ := StagedEntry.Purge.receipt pid r native before
  refine ⟨part,generation,whole,epoch,step,frame,entry,?_,count⟩
  apply complete.settle_cut
    (chosen := (pendingAt (.staged generation pid part.stamp) ledger).take part.removed)
    (requested := ⟨.counted history.length .purge,part.removed⟩)
    before.core.valid before.justified
    (pendingAt_unique (before.core.valid.1.symm ▸ before.core.valid.2) _).take
  · intro ticket member
    exact ⟨_,mem_pendingAt.mp (List.mem_of_mem_take member)⟩
  · exact purge_demand part whole
  · exact count

/-- Original purge execution returns the same paired successor ledger, or
retains its native failed call with no invented terminal receipt. -/
theorem purge_cases (pid : PeerId) (before : StagedEntry.Inv history ledger debts locals w)
    (complete : Complete history ledger) (ambient : Ambient) :
    match (runWGPrefix (CausalJournal.stagedPurge pid) w ambient history).1 with
    | .error _ =>
        (runWGPrefix (CausalJournal.stagedPurge pid) w ambient history).2 = history ∧
        StagedEntry.Inv history ledger debts locals w ∧ Complete history ledger
    | .ok ((_,v),_) => ∃ after,
        Staged.Obligations.Step ledger after ∧
        StagedEntry.Inv (runWGPrefix (CausalJournal.stagedPurge pid) w ambient history).2 after debts locals v ∧
        Complete (runWGPrefix (CausalJournal.stagedPurge pid) w ambient history).2 after := by
  rw [StagedEntry.Purge.run]
  cases performed : ((purgeStagedPackets pid).run w).run ambient with
  | error stop => exact ⟨rfl,before,complete⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,clock⟩ := out
    cases value
    obtain ⟨part,generation,_,_,step,_,entry,finished,_⟩ :=
      purge_receipt pid ⟨(),w,v,ambient,clock⟩ performed before complete
    exact ⟨_,step,entry,finished⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete.Source
