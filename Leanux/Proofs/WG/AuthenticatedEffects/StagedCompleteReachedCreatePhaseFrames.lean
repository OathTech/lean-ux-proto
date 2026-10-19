import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseContracts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeyFrames

/-! Actual native and history frames for live creation phases. Native view
transport and emitted-event quietness are proved independently; the rule is
not applicable to queue installation, counted release or a packet free. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedConservation CreatePoints
set_option maxHeartbeats 600000

theorem Live.transport (kept : Live rootLedger debts locals pid items h w)
    (suffix : List CausalJournal.Event)
    (account : ∀ current active,Accounted h current debts active w → Accounted (h++suffix) current debts active v) :
    Live rootLedger debts locals pid items (h++suffix) v := by
  cases kept with
  | unpublished current steps pending before=>exact .unpublished current steps (pending.append suffix) (account _ _ before)
  | queued current steps pending before=>exact .queued current steps (pending.append suffix) (account _ _ before)
  | cleanup current steps reason done remaining ordered settled pending before=>
    exact .cleanup current steps reason done remaining ordered (allDropped_append settled suffix)
      (pending.append suffix) (account _ _ before)
  | disposed current steps reason settled before=>
    exact .disposed current steps reason (allDropped_append settled suffix) (account _ _ before)

theorem focused_normal (body : TxDisposition.Obs α) (native : WG.M α)
    (erases : ErasesPrefix body (liftWG native))
    (frame : ∀ history ledger active,Preserves (StagedEntry.Inv history ledger debts active) native)
    (before : Live rootLedger debts locals pid items h w.wg)
    (performed : runPrefix (QueueHandoff.focused body) w h=(.ok (value,v),last)) :
    Live rootLedger debts locals pid items last v.wg := by
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
    rw [grown]
    apply before.transport suffix
    intro current active account
    have atNative:=(hoare_iff_run_ambient _ _ _).mp (frame h current active)
      w.wg w.ambient returned g a account.entry actual
    have atHistory:=atNative.views suffix quiet rfl rfl rfl rfl rfl rfl
    have complete:=CompleteSource.focused_complete body w account.complete
    rw [performed,grown] at complete
    exact ⟨atHistory,complete⟩

theorem focused_view (body : TxDisposition.Obs α) (native : WG.M α)
    (erases : ErasesPrefix body (liftWG native)) (frame : SameView StagedEntry.view native)
    (before : Live rootLedger debts locals pid items h w.wg)
    (performed : runPrefix (QueueHandoff.focused body) w h=(.ok (value,v),last)) :
    Live rootLedger debts locals pid items last v.wg :=
  focused_normal body native erases (fun _ _ _=>StagedEntry.native frame) before performed

theorem native_normal (native : WG.M α) (frame : SameView StagedEntry.view native)
    (before : Live rootLedger debts locals pid items h w.wg)
    (performed : runPrefix (Admission.actualOps.step native) w h=(.ok (value,v),last)) :
    Live rootLedger debts locals pid items last v.wg :=
  focused_view (liftPrefix (liftWG native)) native (erasesPrefix_lift _) frame before performed

theorem access_normal (body : MixedM α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (frame : SameView StagedEntry.view native)
    (before : Live rootLedger debts locals pid items h w.wg)
    (performed : runPrefix (Admission.actualOps.access body) w h=(.ok (value,v),last)) :
    Live rootLedger debts locals pid items last v.wg :=
  focused_view (TxDisposition.nativeAccess body) native (TxDisposition.nativeAccess_erases erases) frame before performed

theorem mark_normal (id : SkbId) (state : PacketState)
    (before : Live rootLedger debts locals pid items h w.wg)
    (performed : runPrefix (Admission.actualOps.access (setTxSkbPrefix id fun p=>{p with state})) w h=
      (.ok (value,v),last)) : Live rootLedger debts locals pid items last v.wg := by
  apply focused_normal (TxDisposition.nativeAccess (setTxSkbPrefix id fun p=>{p with state}))
    (setTxSkb id fun p=>{p with state}) (TxDisposition.nativeAccess_erases (setTxSkbPrefix_erases _ _)) _ before performed
  intro history ledger active
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a value s b account native
  cases value
  exact publication_mark_native id state account a b native

theorem event_normal (event : TxDisposition.Event)
    (before : Live rootLedger debts locals pid items h w.wg)
    (performed : runPrefix (Admission.actualOps.event event) w h=(.ok (value,v),last)) :
    Live rootLedger debts locals pid items last v.wg := by
  rw [event_run] at performed
  cases performed
  exact before.views [CausalJournal.txEvent event] (by intro e member; cases List.mem_singleton.mp member; rfl)
    (by intro e member; cases List.mem_singleton.mp member; intro position; rfl) rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
