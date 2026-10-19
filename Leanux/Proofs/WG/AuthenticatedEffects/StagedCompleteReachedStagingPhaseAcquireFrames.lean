import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseFrames

/-! Strict reference acquisition has a read-only guard and a reference-count
choice before its final peer write. The write is joined to the original
whole acquisition, not framed as an arbitrary replacement peer. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity CausalJournal Staged.Obligations Staging.Points
set_option maxHeartbeats 600000

theorem native_not_pending (pid : PeerId) : SameView id (Native.action (.notPending pid)) :=
  SameView.pure _ _

theorem native_inc (count : Nat) : SameView id (refcountInc count : WG.M Unit) := by
  intro initial
  change Preserves (fun w=>w=initial) _
  unfold refcountInc
  simp only [branch,branchCmp,unsupported]
  repeat' first
    | (rx_retention_head MonadLiftT.monadLift; exact hoare_liftAmbient _ _)
    | (rx_retention_head MonadLift.monadLift; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem selected_put_key (kid : Option KeypairId)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position) (.child (.repayment kid)) w a h := by
  refine ⟨before,fun value u b middle run=>?_⟩
  exact preserved (CompleteSelected.decorate (ReadyCarrier.put_key (fun _=>id) kid)
    (Driver.History.state_lift _) (fun _=>id)) before run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
