import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateDisposal

/-! Batch source claims keep the same tickets through settlement and history
extension. Different still-pending native cells cannot be the settled ticket:
the fixed ledger's unique status fixes its allocation position and ordinal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
variable {id : SkbId}

theorem PendingBatch.append (before : PendingBatch history ledger items)
    (suffix : List CausalJournal.Event) : PendingBatch (history ++ suffix) ledger items := by
  intro id member
  obtain ⟨ticket,position,ordinal,generation,value,pending,origin⟩ := before id member
  exact ⟨ticket,position,ordinal,generation,value,pending,origin.append suffix⟩

theorem PendingBatch.settle_other (before : PendingBatch history ledger items)
    (valid : Valid births ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation selected value)
    (absent : selected ∉ items) (outcome : Staged.Obligations.Terminal) :
    PendingBatch history (settle [ticket] outcome ledger) items := by
  intro id member
  obtain ⟨other,p,o,g,v,otherPending,otherOrigin⟩ := before id member
  have different : other ≠ ticket := by
    intro same
    subst other
    have locations := unique_status (valid.1.symm ▸ valid.2) pending otherPending
    have pairs := Pending.allocated.inj (Status.pending.inj locations)
    obtain ⟨rfl,rfl⟩ := pairs
    have sameId := (origin.unique otherOrigin).2.1
    exact absent (sameId.symm ▸ member)
  refine ⟨other,p,o,g,v,?_,otherOrigin⟩
  exact List.mem_map.mpr ⟨(other,Status.pending (.allocated p o)),otherPending,by simp [different]⟩

theorem Dropped.transport (before : Dropped history ledger reason id)
    (suffix : List CausalJournal.Event) (step : Staged.Obligations.Step ledger after) :
    Dropped (history ++ suffix) after reason id := by
  obtain ⟨ticket,position,ordinal,generation,value,cut,receipt,origin,found,valid,cell,cause,terminal⟩ := before
  have below := (List.getElem?_eq_some_iff.mp found).1
  exact ⟨ticket,position,ordinal,generation,value,cut,receipt,origin.append suffix,
    by simpa [List.getElem?_append_left below] using found,
    valid,cell,cause,step.terminal terminal⟩

theorem AllDropped.transport (before : AllDropped history ledger reason items)
    (suffix : List CausalJournal.Event) (step : Staged.Obligations.Step ledger after) :
    AllDropped (history ++ suffix) after reason items :=
  fun id member => (before id member).transport suffix step

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
