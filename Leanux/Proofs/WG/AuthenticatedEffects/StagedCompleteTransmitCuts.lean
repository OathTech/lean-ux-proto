import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTransmit

/-! Staging safety exposes its two actual retained cuts. A selected Stop is
backed by its recorded native take, with later permitted receipts, rather than
being converted into an idle entry with no selected tickets. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteTransmit
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations RetirementSecurity
open AllocatedObligation CausalJournal CompleteCarrier StagedProvenance StagedTerminalComplete
open HandshakeSecurity.StagedConservation

/-- The selected branch retains its native take anchor and the core at that
same receipt's after-state, extended only by the permitted selected history. -/
theorem Safe.cuts (before : Safe debts history) :
    (∃ ledger locals w, Accounted history ledger debts locals w) ∨
    (∃ ledger generation pid peer position,
      CompleteSelected.Active ledger debts generation pid peer position history ∧
      ∃ r : Take.Receipt, r.Valid ∧ r.run.value = some peer ∧
        Core history ledger debts r.run.after ∧
        Aligned (Born history generation pid peer.internalId)
          (pendingAt (.selected position) ledger) peer.staged) := by
  cases before with
  | accounted ledger locals h w kept => exact Or.inl ⟨ledger,locals,w,kept⟩
  | selected ledger generation pid peer position h kept =>
    exact Or.inr ⟨ledger,generation,pid,peer,position,kept,kept.1.1.accounted⟩

/-- Both branches imply a canonical fixed-ledger account at one snapshot.
The accounted branch does not itself retain an execution-reachability relation;
that additional source claim must be kept separately. `Safe.cuts` retains the
branch distinction and the selected branch's recorded take. -/
theorem Safe.account (before : Safe debts history) :
    ∃ ledger w, Core history ledger debts w ∧ Justified history ledger ∧
      AllocationLinks history ledger ∧ Complete history ledger := by
  rcases before.cuts with ⟨ledger,locals,w,kept⟩ | ⟨ledger,generation,pid,peer,position,kept,r,_,_,core,_⟩
  · exact ⟨ledger,w,kept.entry.core,kept.entry.justified,kept.entry.allocationLinks,kept.complete⟩
  · exact ⟨ledger,r.run.after,core,kept.1.2.1,kept.1.2.2.1,kept.2.1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteTransmit
