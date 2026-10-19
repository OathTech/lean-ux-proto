import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionDisposal
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNativeCallbacks

/-! Exact callback history and native sent frames compose independently.
The history projection hides only callbacks with no datagram contribution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem state_callback {body : WGPrefix Event α} (native : WG.M α)
    (quiet : CallbackQuiet.StateQuiet contributing? body)
    (erases : ErasesStatePrefix body native) (frame : SameView WGWorld.sent native) : StateSafe body :=
  state_observed body native erases quiet.1 (state_quiet_of_frame body quiet.1 quiet.2) frame

theorem product_quiet_of_frame (body : PrefixM Event α) (appends : Appends body)
    (frame : HistoryFrame contributing? body) : ProductQuiet body := by
  intro w h
  obtain ⟨suffix,grown⟩ := appends w h
  have unchanged := frame w h
  rw [grown,List.filterMap_append] at unchanged
  have empty : suffix.filterMap contributing? = [] :=
    List.append_cancel_left (as := h.filterMap contributing?) (by simpa only [List.append_nil] using unchanged)
  have none := List.filterMap_eq_nil_iff.mp empty
  have emptyAdded : ∀ event ∈ suffix, added event = [] := by
    intro event member
    have quiet := none event member
    unfold contributing? at quiet
    cases result : added event with
    | nil => rfl
    | cons datum rest => rw [result] at quiet; contradiction
  have emptyEmission : emitted suffix = [] := List.flatMap_eq_nil_iff.mpr emptyAdded
  rw [grown,emitted_append,emptyEmission,List.append_nil]

theorem product_callback {body : PrefixM Event α} (native : WG.M α)
    (quiet : CallbackQuiet.ProductQuiet contributing? body)
    (erases : ErasesPrefix body (liftWG native)) (frame : SameView WGWorld.sent native) : ProductSafe body :=
  product_observed body native erases quiet.1 (product_quiet_of_frame body quiet.1 quiet.2) frame

theorem product_native_callback {body : PrefixM Event α} (native : Leanux.M α)
    (quiet : CallbackQuiet.ProductQuiet contributing? body)
    (erases : ErasesPrefix body native)
    (frame : SameView (fun w : World => w.wg.sent) native) : ProductSafe body := by
  intro w h hi
  obtain ⟨suffix,grown⟩ := quiet.1 w h
  refine ⟨suffix,grown,True.intro,?_⟩
  cases run : (runPrefix body w h).1 with
  | error _ => trivial
  | ok result =>
    have nativeRun := (erases w h).symm.trans run
    have sent := (Lifetimes.ProjectedAction.iff_run _ _ _).mp frame w result.1 result.2 nativeRun
    obtain ⟨earlier,kept⟩ := hi
    refine ⟨earlier,?_⟩
    rw [product_quiet_of_frame body quiet.1 quiet.2 w h,sent]
    exact kept

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
