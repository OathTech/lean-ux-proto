import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityProductFrames

/-! Focused worker histories retain full-journal staged-selection positions.
The source append contract includes stopped runs. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

theorem product_focused_quiet (encode : E → Event) (decode : Event → Option E)
    (body : PrefixM E α) (appends : Appends body)
    (quiet : HistoryFrame (allocation? ∘ encode) body)
    (native : Leanux.M α) (erase : ErasesPrefix body native)
    (kept : ∀ h, Preserves (fun w : World => Inv h w.wg) native) :
    ProductSafe (focusPrefix encode decode body) := by
  apply product_quiet (Appends.focus _ _ _) ?_ (focusPrefix_erases _ _ erase) kept
  intro w h
  obtain ⟨suffix,grown⟩ := appends w (h.filterMap decode)
  have frame := quiet w (h.filterMap decode)
  rw [grown,List.filterMap_append] at frame
  have empty : suffix.filterMap (allocation? ∘ encode) = [] := by
    have sizes := congrArg List.length frame
    simp only [List.length_append] at sizes
    exact List.eq_nil_of_length_eq_zero (by omega)
  rw [focusPrefix_suffix encode decode body w h _ suffix (Prod.ext rfl grown)]
  simp only [List.filterMap_append,List.filterMap_map,empty,List.append_nil]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
