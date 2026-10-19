import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPublicationFrames

/-! History transport is separate from native state transport. These
history-only frames are used below only at source endpoints established by
the actual normal run; they do not themselves establish a reached world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation HandshakeSecurity.StagedDisposal

theorem publication_focused_history (saved : WGWorld) (body : TxDisposition.Obs α) :
    Driver.ProductHistorySafe (fun h => Accounted h ledger debts locals saved) (QueueHandoff.focused body) := by
  intro w history before
  obtain ⟨suffix,extended,entry,_⟩ := CompleteCreate.focused_entry_history saved body w history before.entry
  have complete := CompleteSource.focused_complete body w before.complete
  have paired : Accounted (runPrefix (QueueHandoff.focused body) w history).2 ledger debts locals saved :=
    ⟨entry,complete⟩
  refine ⟨suffix,extended,paired,?_⟩
  cases result : (runPrefix (QueueHandoff.focused body) w history).1 with
  | error reason => trivial
  | ok out => exact paired

theorem publication_borrow_history (saved : WGWorld) (items : List SkbId) :
    Driver.ProductHistorySafe (fun h => Accounted h ledger debts locals saved) (Publication.borrow items) := by
  unfold Publication.borrow Admission.actualOps
  simp only [TxSource.observed,TxSource.Ops.focus]
  cases items.head? with
  | none => exact publication_focused_history saved _
  | some first =>
    repeat' first
      | (driver_history_head focusPrefix; exact publication_focused_history saved _)
      | driver_product_history_step

theorem publication_mark_history (saved : WGWorld) (pid : PeerId) (first : SkbId) (state : PacketState) :
    Driver.ProductHistorySafe (fun h => Accounted h ledger debts locals saved) (publicationMark pid first state) := by
  unfold publicationMark Admission.actualOps
  simp only [TxSource.observed,TxSource.Ops.focus]
  repeat' first
    | (driver_history_head focusPrefix; exact publication_focused_history saved _)
    | driver_product_history_step

theorem publication_normal_accounted {action : PrefixM CausalJournal.Event α} {native : WG.M α}
    (erases : ErasesPrefix action (liftWG native))
    (frame : Preserves (Inv history ledger debts locals) native)
    (histories : ∀ saved, Driver.ProductHistorySafe (fun h => Accounted h ledger debts locals saved) action)
    (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix action w history = (.ok (value,v),last)) :
    Accounted last ledger debts locals v.wg := by
  have full := (erases w history).symm.trans (congrArg Prod.fst performed)
  rw [liftWG_run] at full
  cases original : (native.run w.wg).run w.ambient with
  | error reason => simp only [original,Except.map] at full; cases full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    simp only [original,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    have entry := (hoare_iff_run_ambient _ _ _).mp frame w.wg w.ambient result g ambient before.entry original
    obtain ⟨_,_,paired,_⟩ := histories g w history ⟨entry,before.complete⟩
    rw [performed] at paired
    exact paired

theorem publication_borrow_accounted (items : List SkbId)
    (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (Publication.borrow items) w history = (.ok ((first,pid),v),last)) :
    Accounted last ledger debts locals v.wg :=
  publication_normal_accounted (Publication.borrow_erases items)
    (StagedEntry.native (publication_borrow_view items)) (fun saved => publication_borrow_history saved items) before performed

theorem publication_mark_accounted (pid : PeerId) (first : SkbId) (state : PacketState)
    (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (publicationMark pid first state) w history = (.ok ((),v),last)) :
    Accounted last ledger debts locals v.wg :=
  publication_normal_accounted (publication_mark_erases pid first state)
    (publication_mark_preserves pid first state) (fun saved => publication_mark_history saved pid first state) before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
