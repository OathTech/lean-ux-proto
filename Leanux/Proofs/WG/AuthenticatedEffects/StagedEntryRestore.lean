import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRestoreFrames

/-! Whole-batch restoration finishes the active selected location and recovers
the same fixed-ledger entry bundle. The generation, vacant destination and
ordered selected-ticket alignment remain explicit native caller obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Restoration
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal RetirementSecurity StagedProvenance Staged
open HandshakeSecurity.StagedConservation

/-- The actual restore receipt moves all selected tickets back to their own
vacant staged queue, preserves earlier terminal evidence and clears every
selected location. No fresh ticket or terminal is created. -/
theorem restored (r : Restore.Receipt) (valid : r.Valid)
    (before : Active history ledger debts locals position r.run.before)
    (epoch : Packets.epoch r.run.before = some generation)
    (vacant : stagedAt r.run.before r.pid = some (allocation,[]))
    (aligned : Aligned (Born history generation r.pid allocation)
      (pendingAt (.selected position) ledger) r.packets) :
    let after := transferLocation (.selected position) (.staged generation r.pid allocation) ledger
    Staged.Obligations.Step ledger after ∧
      Inv (history ++ [.stagedRestored r]) after debts locals r.run.after ∧
      pendingAt (.selected position) after = [] ∧
      pendingAt (.staged generation r.pid allocation) after = pendingAt (.selected position) ledger ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after := by
  dsimp only
  obtain ⟨step,core,empty,located⟩ := core_restore r valid before.core epoch vacant position aligned
  have native := physical r valid before
  exact ⟨step,⟨core,(before.justified.transfer _ _).append _,
    (before.allocationLinks.transferred _ _ (by simp) (by simp)).append _,
    before.onlySelected.restored generation r.pid allocation,native.1,native.2.1,native.2.2⟩,
    empty,located,fun _ _ member => step.terminal member⟩

/-- These are the explicit native caller facts needed at restore, in addition
to the active ownership bundle. They are not inferred from a key identifier. -/
structure Ready (history : List Event) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (position generation : Nat) (pid : PeerId)
    (allocation : Nat) (packets : List Packet) (w : WGWorld) : Prop where
  active : Active history ledger debts locals position w
  epoch : Packets.epoch w = some generation
  vacant : stagedAt w pid = some (allocation,[])
  aligned : Aligned (Born history generation pid allocation) (pendingAt (.selected position) ledger) packets

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Restoration
