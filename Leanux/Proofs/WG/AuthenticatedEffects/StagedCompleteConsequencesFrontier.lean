import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteConverse

/-! Conservation consequences share one snapshot and one fixed ledger.
Selected failures name the recorded take snapshot. The accounted branch keeps
ownership and cleanup predicates but requires a separate source-reachability
certificate before its snapshot can be identified with an execution point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConsequences
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity AllocatedObligation CausalJournal StagedProvenance StagedTerminalComplete
open HandshakeSecurity.StagedConservation

/-- Selected plaintext has a native receipt, at the same cut as the account. -/
def Selected (history : List Event) (ledger : Ledger) (w : WGWorld) : Prop :=
  ∀ ticket position, (ticket,Status.pending (.selected position)) ∈ ledger →
    ∃ (r : Take.Receipt) (peer : Peer) (generation : Nat),
      history[position]? = some (.stagingTaken r) ∧ r.Valid ∧ r.run.value = some peer ∧
      w = r.run.after ∧
      Aligned (Born history generation r.pid peer.internalId)
        (pendingAt (.selected position) ledger) peer.staged

structure Cut (history : List Event) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (w : WGWorld) : Prop where
  core : Core history ledger debts w
  justified : Justified history ledger
  links : AllocationLinks history ledger
  complete : Complete history ledger
  native : NativeReady.Inv locals w
  selected : Selected history ledger w

theorem accounted (before : CompleteCarrier.Accounted history ledger debts locals w) :
    Cut history ledger debts locals w := by
  refine ⟨before.entry.core,before.entry.justified,before.entry.allocationLinks,before.complete,
    ⟨before.entry.packets,before.entry.coverage,before.entry.inventory⟩,?_⟩
  intro ticket position member
  have impossible := mem_pendingAt.mpr member
  rw [before.entry.noSelected position] at impossible
  cases impossible

theorem selected (before : CompleteSelected.Active ledger debts generation pid peer position history) :
    ∃ (r : Take.Receipt) (locals : List TxLocalBatch), r.Valid ∧ r.run.value = some peer ∧
      Cut history ledger debts locals r.run.after := by
  obtain ⟨past,suffix,r,historyEq,positionEq,pidEq,native,chosen,core,vacant,aligned,allowed⟩ := before.1.1.reached
  have recorded : history[position]? = some (.stagingTaken r) := by
    rw [historyEq,positionEq]
    simp
  obtain ⟨actual,locals,actualAt,ownership⟩ := before.2.2
  have same := Option.some.inj (recorded.symm.trans actualAt)
  cases same
  have currentCore : Core history ledger debts r.run.after := by
    rw [historyEq]
    exact core.quiet_views suffix (fun event member=>HeldFrontier.progress_quiet (allowed event member)) rfl rfl rfl
  have currentAligned : Aligned (Born history generation r.pid peer.internalId)
      (pendingAt (.selected position) ledger) peer.staged := by
    rw [historyEq,pidEq]
    exact aligned.history_append suffix
  refine ⟨r,locals,native,chosen,currentCore,before.1.2.1,before.1.2.2.1,before.2.1,ownership,?_⟩
  intro ticket other member
  have equal : other=position := by
    by_cases same : other=position
    · exact same
    · have impossible := mem_pendingAt.mpr member
      rw [before.1.2.2.2 other same] at impossible
      cases impossible
  subst other
  exact ⟨r,peer,generation,recorded,native,chosen,rfl,currentAligned⟩

/-- `Safe` supplies a common snapshot satisfying the native ownership
predicates. Only the selected branch identifies that snapshot with a recorded
take here; execution reachability of the accounted branch is not concluded.
Neither branch manufactures a normal return from a failed call. -/
theorem safe_cut (safe : CompleteProduct.Safe history) :
    ∃ ledger debts locals w, Cut history ledger debts locals w := by
  obtain ⟨debts,safe⟩ := safe
  cases safe with
  | accounted ledger locals h w before => exact ⟨ledger,debts,locals,w,accounted before⟩
  | selected ledger generation pid peer position h before =>
    obtain ⟨r,locals,_,_,cut⟩ := selected before
    exact ⟨ledger,debts,locals,r.run.after,cut⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConsequences
