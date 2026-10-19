import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseRelease

/-! Exact unchanged-ledger account cuts for native reads and key repayment.
These strengthen phase framing where the later ordered cleanup needs the
specific unpublished alias rather than an existential live phase. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedDisposal CreatePoints
set_option maxHeartbeats 600000

theorem focused_account (body : TxDisposition.Obs α) (native : WG.M α)
    (erases : ErasesPrefix body (liftWG native)) (frame : SameView StagedEntry.view native)
    (before : Accounted h ledger debts active w.wg)
    (performed : runPrefix (QueueHandoff.focused body) w h=(.ok (value,v),last)) :
    Accounted last ledger debts active v.wg ∧ ∃ suffix,last=h++suffix := by
  obtain ⟨suffix,grown,quiet⟩:=QueueHandoff.focused_quiet body w h
  change (runPrefix (QueueHandoff.focused body) w h).2=h++suffix at grown
  rw [performed] at grown
  change last=h++suffix at grown
  have erased:=(focusPrefix_erases CausalJournal.txEvent CausalJournal.txEvent? erases w h).symm.trans
    (congrArg Prod.fst performed)
  rw [liftWG_run] at erased
  cases actual : (native.run w.wg).run w.ambient with
  | error stop=>simp [actual,Except.map] at erased
  | ok out=>
    obtain ⟨⟨returned,g⟩,a⟩:=out
    simp only [actual,Except.map,Except.ok.injEq,Prod.mk.injEq] at erased
    obtain ⟨rfl,rfl⟩:=erased
    have atNative:=(hoare_iff_run_ambient _ _ _).mp (StagedEntry.native frame)
      w.wg w.ambient returned g a before.entry actual
    have atHistory:=atNative.views suffix quiet rfl rfl rfl rfl rfl rfl
    have complete:=CompleteSource.focused_complete body w before.complete
    rw [performed] at complete
    exact ⟨⟨grown ▸ atHistory,complete⟩,suffix,grown⟩

theorem access_account (body : MixedM α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (frame : SameView StagedEntry.view native)
    (before : Accounted h ledger debts active w.wg)
    (performed : runPrefix (Admission.actualOps.access body) w h=(.ok (value,v),last)) :
    Accounted last ledger debts active v.wg ∧ ∃ suffix,last=h++suffix :=
  focused_account (TxDisposition.nativeAccess body) native (TxDisposition.nativeAccess_erases erases) frame before performed

theorem guard_account (decision : Decision) (flag : Bool)
    (before : Accounted h ledger debts active w.wg)
    (performed : runPrefix (Admission.actualOps.step (branch decision flag)) w h=(.ok (value,v),last)) :
    value=flag ∧ last=h ∧ Accounted last ledger debts active v.wg := by
  obtain ⟨u,run,entry⟩:=CreateEntry.guard_entry decision flag before.entry
  rw [run] at performed
  cases performed
  exact ⟨rfl,rfl,entry,before.complete⟩

theorem guard_value (decision : Decision) (flag : Bool)
    (before : Live rootLedger debts locals pid items h w.wg)
    (performed : runPrefix (Admission.actualOps.step (branch decision flag)) w h=(.ok (value,v),last)) : value=flag := by
  obtain ⟨ledger,active,steps,account⟩:=before.accounted
  exact (guard_account decision flag account performed).1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
