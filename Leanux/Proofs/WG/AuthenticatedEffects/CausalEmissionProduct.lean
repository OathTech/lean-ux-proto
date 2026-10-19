import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionState

/-! Product-state and quiet-observer rules for the emission carrier. Native
erasure alone is insufficient: an independent exact append-history frame is
required whenever a pre-existing observer is reused. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def StateQuiet (body : WGPrefix Event α) : Prop :=
  ∀ w a h, emitted (runWGPrefix body w a h).2 = emitted h

def ProductQuiet (body : PrefixM Event α) : Prop :=
  ∀ w h, emitted (runPrefix body w h).2 = emitted h

theorem emitted_map_quiet (encode : E → Event) (quiet : ∀ event, added (encode event) = [])
    (events : List E) : emitted (events.map encode) = [] := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    change added (encode event) ++ emitted (rest.map encode) = []
    rw [quiet,ih,List.nil_append]

theorem focus_quiet (encode : E → Event) (decode : Event → Option E)
    (quiet : ∀ event, added (encode event) = []) (body : PrefixM E α) :
    ProductQuiet (focusPrefix encode decode body) := by
  intro w h
  change emitted (h ++ _) = emitted h
  rw [emitted_append,emitted_map_quiet encode quiet,List.append_nil]

theorem focus_state_quiet (encode : E → Event) (decode : Event → Option E)
    (quiet : ∀ event, added (encode event) = []) (body : WGPrefix E α) :
    StateQuiet (focusStatePrefix encode decode body) := by
  intro w a h
  change emitted (h ++ _) = emitted h
  rw [emitted_append,emitted_map_quiet encode quiet,List.append_nil]

theorem state_observed (body : WGPrefix Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (appends : StateAppends body)
    (quiet : StateQuiet body) (frame : SameView WGWorld.sent native) : StateSafe body := by
  intro w a h hi
  obtain ⟨suffix,grown⟩ := appends w a h
  refine ⟨suffix,grown,True.intro,?_⟩
  cases run : (runPrefix (body.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have nativeRun := (erases w a h).symm.trans run
    have sent := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp frame w a value v b nativeRun
    obtain ⟨earlier,historyEq⟩ := hi
    have frameHistory := quiet w a h
    change emitted (runPrefix (body.run w) a h).2 = emitted h at frameHistory
    exact ⟨earlier,by rw [frameHistory,sent]; exact historyEq⟩

theorem product_pure (value : α) : ProductSafe (pure value) :=
  PrefixPreserves.pure (fun _ _ _ => True.intro) value

theorem product_bind {body : PrefixM Event α} {next : α → PrefixM Event β}
    (head : ProductSafe body) (tail : ∀ value, ProductSafe (next value)) : ProductSafe (body >>= next) :=
  PrefixPreserves.bind head tail

theorem product_ite (p : Prop) [Decidable p] {left right : PrefixM Event α}
    (hl : p → ProductSafe left) (hr : ¬p → ProductSafe right) : ProductSafe (if p then left else right) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hl hp
  · exact hr hp

theorem product_state {body : WGPrefix Event α} (safe : StateSafe body) :
    ProductSafe (liftWGObserver body) := safe.liftWGObserver

theorem product_wg (native : WG.M α) (safe : StateSafe (liftWGPrefix native)) :
    ProductSafe (liftPrefix (liftWG native)) := by
  simpa only [liftWGObserver_lift] using product_state safe

theorem product_observed (body : PrefixM Event α) (native : WG.M α)
    (erases : ErasesPrefix body (liftWG native)) (appends : Appends body)
    (quiet : ProductQuiet body) (frame : SameView WGWorld.sent native) : ProductSafe body := by
  intro w h hi
  obtain ⟨suffix,grown⟩ := appends w h
  refine ⟨suffix,grown,True.intro,?_⟩
  cases run : (runPrefix body w h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    have nativeRun := (erases w h).symm.trans run
    obtain ⟨_,_,_,kept⟩ := product_wg native (state_native native frame) w h hi
    have lifted : runPrefix (liftPrefix (liftWG native) : PrefixM Event α) w h =
        (.ok (value,v),h) := by rw [runPrefix_lift,nativeRun]
    rw [lifted] at kept
    obtain ⟨earlier,historyEq⟩ := kept
    exact ⟨earlier,by rw [quiet]; exact historyEq⟩

theorem product_emit (event : Event) (quiet : added event = []) : ProductSafe (emitPrefix event) := by
  intro w h hi
  exact ⟨[event],rfl,True.intro,hi.quiet [event] (by
    simp only [emitted,List.flatMap_cons,List.flatMap_nil,quiet,List.nil_append])⟩

theorem product_forIn {α β : Type} (xs : List α) (initial : β)
    (body : α → β → PrefixM Event (ForInStep β))
    (preserves : ∀ value state, ProductSafe (body value state)) : ProductSafe (forIn xs initial body) :=
  PrefixPreserves.forIn xs initial body (fun _ _ _ => True.intro) preserves

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
