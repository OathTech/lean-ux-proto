import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteConverse
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryOriginalRelease

/-! Both peer-release observers use the same original releaseCut successor.
The final arm settles exactly its staged tickets; nonfinal repayment is
terminal-quiet. Entry and converse refer to this one successor ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete.Source
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal StagedProvenance HandshakeSecurity.StagedDisposal

theorem release_successor (peer : Option PeerId) (r : WGRunWitness (Option (PeerId × Peer)))
    (native : r.Valid (releaseCut peer))
    (before : StagedEntry.Inv history ledger debts locals r.before) (complete : Complete history ledger)
    (successor : PeerRelease.Successor r.value r.before history.length ledger afterLedger) :
    Complete (history ++ [.stagedDisposal (.release peer r)]) afterLedger := by
  cases value : r.value with
  | none =>
    have equal : afterLedger = ledger := by simpa only [PeerRelease.Successor,value] using successor
    subst afterLedger
    apply complete.append_quiet
    intro event member
    cases List.mem_singleton.mp member
    exact release_none_quiet value
  | some pair =>
    obtain ⟨pid,p⟩ := pair
    have selected : ∃ generation, Packets.epoch r.before = some generation ∧
        afterLedger = settle (pendingAt (.staged generation pid p.internalId) ledger)
          (.counted history.length .finalRelease) ledger := by
      simpa only [PeerRelease.Successor,value] using successor
    obtain ⟨generation,epoch,rfl⟩ := selected
    obtain ⟨device,_,present,resident,_,_,_,_,_⟩ := release_exact peer r native pid p value
    have staged : Staged.stagedAt r.before pid = some (p.internalId,p.staged) := by
      simp only [Staged.stagedAt,present,Option.bind_some,resident,Option.map_some]
    have aligned := before.core.queues generation pid p.internalId
    simp only [stagedPackets,epoch,staged,ite_true,eq_self] at aligned
    apply complete.settle_cut
      (chosen := pendingAt (.staged generation pid p.internalId) ledger)
      (requested := ⟨.counted history.length .finalRelease,p.staged.length⟩)
      before.core.valid before.justified
      (pendingAt_unique (before.core.valid.1.symm ▸ before.core.valid.2) _)
    · intro ticket member
      exact ⟨_,mem_pendingAt.mp member⟩
    · exact release_some_demand value
    · exact HandshakeSecurity.StagedConservation.aligned_length aligned

theorem original_native_entry (peer : Option PeerId)
    (before : StagedEntry.Inv history ledger debts locals w) (complete : Complete history ledger)
    (a b : Ambient) (native : ((releaseCut peer).run w).run a = .ok ((value,v),b)) :
    ∃ after, Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
      PeerRelease.Successor value w history.length ledger after ∧
      StagedEntry.Inv (history ++ [.stagedDisposal (.release peer ⟨value,w,v,a,b⟩)]) after debts locals v ∧
      Complete (history ++ [.stagedDisposal (.release peer ⟨value,w,v,a,b⟩)]) after := by
  obtain ⟨after,step,frame,successor,entry⟩ := StagedEntry.OriginalRelease.native_entry peer before a b native
  exact ⟨after,step,frame,successor,entry,
    release_successor peer ⟨value,w,v,a,b⟩ native before complete successor⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete.Source
