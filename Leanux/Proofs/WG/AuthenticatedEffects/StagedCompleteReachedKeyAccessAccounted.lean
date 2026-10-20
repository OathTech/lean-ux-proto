import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedKeyAccessAdapter

/-! Key repayment preserves the complete packet account at every original
native access cut, including erasure before its lifetime event. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeyAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open AllocatedObligation CompleteCarrier StagedTerminalComplete

theorem RootPoint.accounted (before : Accounted h ledger debts locals w.wg)
    (point : RootPoint kid now w h u middle) : Accounted middle ledger debts locals u.wg := by
  cases point with
  | source point=>
    obtain ⟨suffix,extended⟩:=point.appends
    rw [extended,List.drop_left]
    apply (before.same_view (point_view point)).append_quiet
    · intro event member
      obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
      exact (encode_quiet source).1
    · intro event member
      obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
      exact (encode_quiet source).2

theorem returned (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix (observed (keypairPutPrefix (some key) false)) w h=(.ok ((),u),middle)) :
    Accounted middle ledger debts locals u.wg := by
  have complete : Complete (runPrefix (observed (keypairPutPrefix (some key) false)) w h).2 ledger :=
    CompletionBatch.Converse.history_preserved before.complete (Appends.focus _ _ _)
      (focusPrefix_other _ _ _ (fun _=>rfl) _) (w:=w)
  rw [performed] at complete
  exact ⟨DeadEntry.key_entry key before.entry performed,complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeyAccess
