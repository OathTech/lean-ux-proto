import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueue
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionReleaseEntry
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPeerReleaseFrontier

/-! Full semantic entry at actual reference repayment. The source-derived
native ownership transport and receipt settlement share one canonical ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Release
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations AllocatedObligation PeerRelease

/-- The counted native release preserves terminal provenance and allocation
lineage while settling exactly its own staged final-release obligations. -/
theorem cut_entry {w : World} (peer : Option PeerId)
    (before : Inv history ledger debts locals w.wg)
    (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),ambient),last)) :
    ∃ after, Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
      Successor value w.wg last.length ledger after ∧
      Inv (last ++ [receipt peer value w.wg g w.ambient ambient]) after debts locals g := by
  have native := cut_valid peer performed
  obtain ⟨suffix,extended,quiet⟩ := cut_birth_quiet peer w.wg w.ambient history
  rw [performed] at extended
  change last = history ++ suffix at extended
  have atEntry : Inv last ledger debts locals w.wg := by
    rw [extended]
    exact before.views suffix quiet rfl rfl rfl rfl rfl rfl
  obtain ⟨covered,unique,bounds⟩ := cut_ownership peer before.coverage before.inventory before.packets
    w.ambient ambient native
  cases value with
  | none =>
    exact ⟨ledger,Staged.Obligations.Step.refl _,AllocatedFrame.refl _,rfl,
      CompletionBatch.release_none_entry peer ⟨none,w.wg,g,w.ambient,ambient⟩ native rfl atEntry bounds covered unique⟩
  | some pair =>
    obtain ⟨pid,p⟩ := pair
    obtain ⟨generation,epoch,step,frame,entry,_,_⟩ := CompletionBatch.release_final_entry peer
      ⟨some (pid,p),w.wg,g,w.ambient,ambient⟩ native rfl atEntry bounds covered unique
    exact ⟨_,step,frame,⟨generation,epoch,rfl⟩,entry⟩

theorem finish_entry (value : Option (PeerId × Peer))
    (before : Inv history ledger debts locals w.wg)
    (performed : runPrefix (finish value) w history = (.ok ((),v),last)) :
    last = history ∧ Inv last ledger debts locals v.wg := by
  obtain ⟨same,owned,bounds⟩ := finish_returned value (Queue.owned before) before.packets performed
  refine ⟨same,owned.1,?_,?_,before.noSelected,bounds,owned.2.1,owned.2.2⟩
  · simpa only [same] using before.justified
  · simpa only [same] using before.allocationLinks

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Release
