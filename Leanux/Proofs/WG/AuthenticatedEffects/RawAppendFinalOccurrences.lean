import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendFinalProjection

/-! A raw append occurrence maps to its exact final-journal occurrence, with
the complete preceding raw history retained. Equal datagram values therefore
cannot be assigned to an earlier convenient authentication receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
open Leanux Leanux.Proofs.Logged

theorem projected_occurrence (decode : E → Option F) (history : List E)
    (before after : List F) (value : F)
    (position : history.filterMap decode = before ++ value :: after) :
    ∃ pre event post, history = pre ++ event :: post ∧
      pre.filterMap decode = before ∧ decode event = some value ∧ post.filterMap decode = after := by
  obtain ⟨first,rest,whole,firstEq,restEq⟩ := List.filterMap_eq_append_iff.mp position
  obtain ⟨quiet,event,post,tail,ignored,selected,last⟩ := List.filterMap_eq_cons_iff.mp restEq
  refine ⟨first ++ quiet,event,post,?_,?_,selected,last⟩
  · rw [whole,tail,List.append_assoc]
  · rw [List.filterMap_append,firstEq,List.filterMap_eq_nil_iff.mpr ignored,List.append_nil]

/-- Every original native append occurrence in the initialized direct observer
has its own final receipt at the same raw ordinal, including stopped prefixes. -/
theorem initialized_occurrence (trace : Runner.Trace) (placeholders : Bool)
    (before after : List RawAppend.Event) (append : RawAppend.Event)
    (position : (runPrefixOuter (RawAppend.execute trace placeholders) []).2 = before ++ append :: after) :
    ∃ pre event post,
      (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 = pre ++ event :: post ∧
      pre.filterMap raw? = before ∧ raw? event = some append ∧ post.filterMap raw? = after := by
  rw [initialized_history] at position
  exact projected_occurrence raw? _ before after append position

theorem selected_delta (before after : List SentDatagram) (append : RawAppend.Event)
    (selected : ofSent before after = some append) :
    append.before = before ∧ after.drop before.length = [append.datagram] := by
  unfold ofSent at selected
  split at selected
  next datagram exactDelta =>
    cases selected
    exact ⟨rfl,exactDelta⟩
  next => contradiction

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
