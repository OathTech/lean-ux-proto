import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedSendLoop
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionKeyRelease

/-! Native key repayment preserves every indexed entry component. It does
not settle another ticket or remove a first terminal; a failure retains the
actual repayment entry after the selected batch's cleanup. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity HandshakeSecurity.StagedDisposal CompletionCuts
open TransmitSecurity.Staged.Obligations Queues.RxCredits

theorem keyRelease_entry_view (key : KeypairId) :
    SameView StagedEntry.view (keypairPut (some key) false) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b native
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PacketOrigins.snapshot_pair (PacketOrigins.epoch_ring (TxRing.keypairPut_frame (some key) false))
      (PacketMaterial.of_packets (TxDisposition.keyPut_packets (some key) false))) w a value v b native
  have staged := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Staged.Exact.key_put (some key) false) w a value v b native
  have geometry := (ProjectedAction.iff_run_ambient _ _ _).mp
    (StagingOccurrences.key_put_geometry (some key) false) w a value v b native
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((keypairPut_protect (some key) false).factor (fun fields => fields.2.2.1)) w a value v b native
  have owners := queueContents_of_exact queues
  obtain ⟨epoch,cells⟩ := Prod.mk.inj material
  obtain ⟨snapshot,packets⟩ := Prod.mk.inj geometry
  change Packets.epoch v = Packets.epoch w at epoch
  simp only [StagedEntry.view,epoch,staged,cells,snapshot,packets,owners]

theorem indexed_keyRelease_checked (context : Context) (key : KeypairId) (phase : Phase)
    (ledger : Staged.Obligations.Ledger) (debts : List CleanupDebt) :
    Ensures (fun h w => Owned context phase h ledger debts w) (IndexedStopped context ledger debts)
      ((TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal).access (keypairPutPrefix (some key) false))
      (fun _ h w => Owned context phase h ledger debts w) := by
  have quiet : HistoryFrame ledgerEvent?
      ((TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal).access (keypairPutPrefix (some key) false)) :=
    focusPrefix_other _ _ _ (fun _ => rfl) _
  apply indexed_passive_checked (.keyRelease key) (discard_unit _).symm
    (Appends.focus _ _ _) quiet (ledger_history_birth_free quiet)
  · exact focusPrefix_erases _ _ (TxDisposition.nativeAccess_erases (keypairPutPrefix_erases _ _))
  · exact sameView_liftWG (fun w : World => StagedEntry.view w.wg) StagedEntry.view _
      (keyRelease_entry_view key) (fun _ _ _ same => same)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
