import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSnapshots

/-! Projected accounts transport to the same concrete receipt snapshot;
the fixed ledger, debts and phase-derived active locals are preserved. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.Proofs.Logged CompleteCarrier

theorem Snapshot.append (snapshot : Snapshot history position w)
    (suffix : List CausalJournal.Event) : Snapshot (history ++ suffix) position w := by
  cases snapshot with
  | taken receipt occurrence valid =>
    have bound := (List.getElem?_eq_some_iff.mp occurrence).1
    exact .taken receipt (by simpa [List.getElem?_append_left bound] using occurrence) valid
  | allocated packets receipt occurrence valid =>
    have bound := (List.getElem?_eq_some_iff.mp occurrence).1
    exact .allocated packets receipt (by simpa [List.getElem?_append_left bound] using occurrence) valid
  | socket receipt occurrence valid =>
    have bound := (List.getElem?_eq_some_iff.mp occurrence).1
    exact .socket receipt (by simpa [List.getElem?_append_left bound] using occurrence) valid
  | freed receipt occurrence valid =>
    have bound := (List.getElem?_eq_some_iff.mp occurrence).1
    exact .freed receipt (by simpa [List.getElem?_append_left bound] using occurrence) valid

/-- The same ledger account is realized at a concrete earlier event's
snapshot. The premise explicitly retains the missing silent-interval frame. -/
theorem Cut.Valid.at_snapshot {saved : Cut context} (valid : saved.Valid reason last)
    (anchor : saved.Anchored last) :
    ∃ position w, Snapshot last position w ∧
      Accounted last saved.ledger saved.debts saved.locals w := by
  obtain ⟨⟨suffix,extended⟩,position,w,snapshot,same⟩ := anchor
  refine ⟨position,w,?_,valid.accounted.same_view same⟩
  rw [← extended]
  exact snapshot.append suffix

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
