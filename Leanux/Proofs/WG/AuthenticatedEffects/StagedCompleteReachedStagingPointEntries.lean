import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointRejected

/-! Fixed selection and guard entry points connect the canonical tree to
its concrete account. Original successful prefixes determine every cached
peer/key and snapshot; neither a fabricated cut nor a callback hypothesis
is supplied in place of those runs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations HandshakeSecurity.StagedConservation CompleteCarrier
set_option maxHeartbeats 600000

noncomputable def Point.cast {action other : WGPrefix Event α} (equal : action=other)
    {shape : Shape other} (point : Point shape w a h leaf u b middle remaining) :
    Point (equal.symm ▸ shape) w a h leaf u b middle remaining := by
  cases equal
  exact point

noncomputable def selectedPoint
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle)) :
    Point (stagingShape pid) w a h (allocationPrefix pid peer key) u b middle
      (allocationPrefix pid peer key >>= allocationTail pid peer) := by
  unfold stagingShape
  apply Point.marked
  apply Point.cast (allocation_factor pid)
  exact .right (selectionShape pid) _ selected (.left _ (.entry (allocationPrefixShape pid peer key)))

noncomputable def callbackPoint
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((decision,v),c),last)) :
    Point (stagingShape pid) w a h (allocationTail pid peer decision) v c last
      (allocationTail pid peer decision) := by
  unfold stagingShape
  apply Point.marked
  apply Point.cast (allocation_factor pid)
  exact .right (selectionShape pid) _ selected
    (.right (allocationPrefixShape pid peer key) (tailShape pid peer) guarded (.entry (tailShape pid peer decision)))

/-- The exact guard entry contains the original ordered ticket cohort and
cached peer. The native selected receipt, including borrowed key, is retained
in Selected; after-guard Ready and Shape come from that very source path. -/
theorem selected_entry (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle)) :
    ∃ after generation,
      Selected h ledger debts locals pid w a peer key middle u b after generation ∧
      CompleteSelected.Ready after debts locals generation pid peer h.length middle u b := by
  rcases Staging.selection_cases before pid a with failed|idle|borrowed|chosen
  · obtain ⟨stop,_,stopped⟩:=failed
    rw [selected] at stopped
    cases stopped
  · obtain ⟨v,c,last,idle,_⟩:=idle
    rw [selected] at idle
    cases idle
  · obtain ⟨r,p,after,generation,stop,_,_,_,_,_,_,_,_,stopped⟩:=borrowed
    rw [selected] at stopped
    cases stopped
  · obtain ⟨p,k,last,v,c,after,generation,performed,path⟩:=chosen
    rw [selected] at performed
    cases performed
    exact ⟨after,generation,path,path.choose_spec.2.2.2.2.2.2.2.2⟩

theorem callback_entry (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((decision,v),c),last)) :
    ∃ after generation,
      CallbackPath h ledger debts locals pid w a peer key middle u b after generation decision last v c := by
  obtain ⟨after,generation,path,ready⟩:=selected_entry before selected
  have checked:=Staging.normal (allocation_checked after debts locals generation pid peer h.length key) ready guarded
  exact ⟨after,generation,path,selected,guarded,checked.1,checked.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
