import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionProduct
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedHooks

/-! Quiet embedded-journal callbacks preserve the ordered emission projection.
The history frame is separate from native result erasure, including on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity

def oldSocket? : Journal.Event → Option Unit
  | .socket _ => some ()
  | _ => none

private theorem old_added_none (event : Journal.Event) (none : oldSocket? event = Option.none) :
    added (.old event) = [] := by
  cases event <;> first | rfl | cases none

theorem old_history_quiet (body : PrefixT Journal.Event State α) (appends : Appends body)
    (frame : HistoryFrame oldSocket? body) (w : State) (h : List Event) :
    emitted (runPrefix (focusPrefix Event.old old? body) w h).2 = emitted h := by
  obtain ⟨suffix,grown⟩ := appends w (h.filterMap old?)
  have retained := frame w (h.filterMap old?)
  rw [grown,List.filterMap_append] at retained
  have absent : suffix.filterMap oldSocket? = [] := by simpa using retained
  have quiet : ∀ event ∈ suffix, added (.old event) = [] := by
    intro event member
    apply old_added_none
    cases selected : oldSocket? event with
    | none => rfl
    | some value =>
      have found : value ∈ suffix.filterMap oldSocket? := List.mem_filterMap.mpr ⟨event,member,selected⟩
      simp [absent] at found
  have empty : emitted (suffix.map Event.old) = [] := by
    clear grown retained absent
    induction suffix with
    | nil => rfl
    | cons first rest ih =>
      change added (.old first) ++ emitted (rest.map Event.old) = []
      rw [quiet first (by simp)]
      exact ih (fun e he => quiet e (by simp [he]))
  rw [focusPrefix_suffix Event.old old? body w h _ suffix (Prod.ext rfl grown)]
  exact (emitted_append h _).trans (by rw [empty,List.append_nil])

theorem old_state (body : WGPrefix Journal.Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (appends : StateAppends body)
    (quiet : StateHistoryFrame oldSocket? body) (frame : SameView WGWorld.sent native) :
    StateSafe (state body) :=
  state_observed _ native (focusStatePrefix_erases _ _ erases) (StateAppends.focus _ _ _)
    (fun w a h => old_history_quiet (body.run w) (appends w) (quiet w) a h) frame

theorem old_product (body : PrefixM Journal.Event α) (native : WG.M α)
    (erases : ErasesPrefix body (liftWG native)) (appends : Appends body)
    (quiet : HistoryFrame oldSocket? body) (frame : SameView WGWorld.sent native) :
    ProductSafe (product body) :=
  product_observed _ native (focusPrefix_erases _ _ erases) (Appends.focus _ _ _)
    (old_history_quiet body appends quiet) frame

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
