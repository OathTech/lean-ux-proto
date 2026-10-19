import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointCutFrames

/-! Every residual is constructed from the fixed original source point.
Receipt continuations retain the original capture entry, rather than treating
the intermediate world as a fresh decrypt entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.Proofs.Logged

variable {E F α β : Type}

theorem focus_remainder (encode : E→F) (decode : F→Option E)
    (inverse : ∀event,decode (encode event)=some event)
    (body rest : WGPrefix E α) (w v : WGWorld) (a b : Ambient) (h : List F) (middle : List E)
    (same : runWGPrefix body w a (h.filterMap decode)=runWGPrefix rest v b middle)
    (extended : ∃suffix,middle=h.filterMap decode++suffix)
    (appends : StateAppends rest) :
    runWGPrefix (focusStatePrefix encode decode body) w a h =
      runWGPrefix (focusStatePrefix encode decode rest) v b
        (h++(middle.drop (h.filterMap decode).length).map encode) := by
  obtain ⟨first,rfl⟩:=extended
  have filtered : (h++first.map encode).filterMap decode=h.filterMap decode++first := by
    rw [List.filterMap_append,filterMap_encoded encode decode inverse]
  obtain ⟨last,after⟩:=appends v b (h.filterMap decode++first)
  change (runWGPrefix rest v b (h.filterMap decode++first)).2=_ at after
  change ((runWGPrefix body w a (h.filterMap decode)).1,
    h++((runWGPrefix body w a (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode)=_
  rw [same,after]
  simp only [List.drop_left]
  change (_,h++((h.filterMap decode++first++last).drop (h.filterMap decode).length).map encode)=
    ((runWGPrefix rest v b ((h++first.map encode).filterMap decode)).1,
      (h++first.map encode)++((runWGPrefix rest v b ((h++first.map encode).filterMap decode)).2.drop
        ((h++first.map encode).filterMap decode).length).map encode)
  rw [filtered,after]
  have firstDrop : (h.filterMap decode++first++last).drop (h.filterMap decode).length=first++last := by
    rw [List.append_assoc,List.drop_left]
  have allDrop : (h.filterMap decode++first++last).drop (h.filterMap decode++first).length=last := List.drop_left
  rw [firstDrop,allDrop,List.map_append,List.append_assoc]

theorem Point.run {E α : Type} {action remaining : WGPrefix E α} {shape : Shape action}
    {w v : WGWorld} {a b : Ambient} {h middle : List E} {site : Site}
    (point : Point shape w a h site v b middle remaining) :
    runWGPrefix action w a h=runWGPrefix remaining v b middle := by
  induction point with
  | entry shape => rfl
  | returned shape performed => exact performed.trans (runStatePrefix_pure _ _ _ _).symm
  | native token performed => rw [token.run,performed,emitMany_run]
  | left tail point ih =>
      change runStatePrefix (_ >>= _) _ _ _ = runStatePrefix (_ >>= _) _ _ _
      rw [runStatePrefix_bind,runStatePrefix_bind]
      change runStatePrefix _ _ _ _ = _ at ih
      rw [ih]
      rfl
  | right head tail leading point ih =>
      change runStatePrefix (_ >>= _) _ _ _ = _
      rw [runStatePrefix_bind]
      change runStatePrefix _ _ _ _ = _ at leading
      rw [leading]
      exact ih
  | focus encode decode inverse point ih =>
      exact focus_remainder encode decode inverse _ _ _ _ _ _ _ _ ih point.appends point.remaining_appends
  | receipt record point ih =>
      rw [runWGPrefix_receiptWGObserved,receiptFrom_run,ih]
      split <;> rename_i equation <;> rw [equation]
  | receiptNative shape record performed =>
      rw [runWGPrefix_receiptWGObserved,performed,emitMany_run]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
