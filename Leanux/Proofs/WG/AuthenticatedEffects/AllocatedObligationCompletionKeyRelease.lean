import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionQuiet
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageCreate

/-! Key-reference repayment does not move the completion's TX cells or
their first-terminal ledger. The actual stopped repayment is retained at its
entry cut; key lifetime events do not masquerade as packet settlement. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity HandshakeSecurity.StagedDisposal CompletionCuts

theorem State.key_release (before : State context phase history w) (key : KeypairId)
    (run : (liftWG (keypairPut (some key) false)).run w = .ok ((),v)) :
    State context phase history v := by
  have snapshot : SameView PacketOrigins.snapshot (keypairPut (some key) false) :=
    PacketOrigins.snapshot_pair (PacketOrigins.epoch_ring (TxRing.keypairPut_frame _ _))
      (PacketMaterial.of_packets (TxDisposition.keyPut_packets _ _))
  have lifted : SameView (fun w : World => PacketOrigins.snapshot w.wg)
      (liftWG (keypairPut (some key) false)) :=
    sameView_liftWG (fun w : World => PacketOrigins.snapshot w.wg) PacketOrigins.snapshot _ snapshot
      (fun _ _ _ same => same)
  have same := (ProjectedAction.iff_run _ _ _).mp lifted w () v run
  obtain ⟨epoch,cells⟩ := Prod.mk.inj same
  obtain ⟨ledger,debts,step,support,recorded,remaining,assigned,coverage,inventory⟩ := before
  rw [liftWG_run] at run
  cases native : ((keypairPut (some key) false).run w.wg).run w.ambient with
  | error reason => simp [native,Except.map] at run
  | ok out =>
    rcases out with ⟨⟨value,after⟩,ambient⟩
    cases value
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    have sameWorld := congrArg World.wg run.2
    refine ⟨ledger,debts,step,support.views epoch cells,recorded,remaining,assigned,?_,?_⟩
    · exact sameWorld ▸ coverage.key_put (some key) false _ _ native
    · exact sameWorld ▸ inventory.key_put (some key) false _ _ native

theorem keyRelease_checked (context : Context) (key : KeypairId) (phase : Phase) :
    Holds context phase
      ((TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal).access (keypairPutPrefix (some key) false)) := by
  apply quiet_native_checked (.keyRelease key) rfl (Appends.focus _ _ _)
  · exact focusPrefix_other _ _ _ (fun _ => rfl) _
  · exact focusPrefix_erases _ _ (TxDisposition.nativeAccess_erases (keypairPutPrefix_erases _ _))
  · intro w history value v before run
    cases value
    exact before.key_release key run

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
