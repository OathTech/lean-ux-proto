import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageHistory

/-! Fixed incoming scope contracts carry positional coverage through the same
execution. Effectful actors require a nonempty stack; native leaves do not. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

abbrev StateAt (frames : List (CausalScope.Token Cause)) (body : WGPrefix Event α) :=
  StatePrefixPreserves (fun h _ _ => Inv frames h) Safe body

abbrev ProductAt (frames : List (CausalScope.Token Cause)) (body : PrefixM Event α) :=
  PrefixEnsures (fun h (_ : World) => Inv frames h) Safe body (fun _ h (_ : World) => Inv frames h)

abbrev StateClosed (body : WGPrefix Event α) := ∀ frames, StateAt frames body
abbrev ProductClosed (body : PrefixM Event α) := ∀ frames, ProductAt frames body
abbrev StateGuarded (body : WGPrefix Event α) := ∀ frames, frames ≠ [] → StateAt frames body
abbrev ProductGuarded (body : PrefixM Event α) := ∀ frames, frames ≠ [] → ProductAt frames body

theorem state_lift (body : WG.M α) : StateAt frames (liftWGPrefix body) :=
  StatePrefixEnsures.lift _ (fun _ _ _ ready => ready.1) (fun _ _ _ _ _ _ ready _ => ready)

theorem state_pure (value : α) : StateAt frames (pure value) :=
  StatePrefixEnsures.pure value (fun _ _ _ ready => ready.1) (fun _ _ _ ready => ready)

theorem state_bind {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (first : StateAt frames body) (tail : ∀ value, StateAt frames (next value)) :
    StateAt frames (body >>= next) := StatePrefixEnsures.bind first tail

theorem state_ite (p : Prop) [Decidable p] {a b : WGPrefix Event α}
    (ha : p → StateAt frames a) (hb : ¬p → StateAt frames b) : StateAt frames (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem state_forIn (xs : List α) (initial : β) (body : α → β → WGPrefix Event (ForInStep β))
    (safe : ∀ value state, StateAt frames (body value state)) : StateAt frames (forIn xs initial body) := by
  induction xs generalizing initial with
  | nil => exact state_pure initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply state_bind (safe x initial)
    intro step
    cases step with
    | done state => exact state_pure state
    | yield state => exact ih state

theorem state_range (range : Std.Legacy.Range) (initial : β)
    (body : Nat → β → WGPrefix Event (ForInStep β))
    (safe : ∀ value state, StateAt frames (body value state)) : StateAt frames (forIn range initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact state_forIn _ initial body safe

theorem state_emit (event : Event) (quiet : scope? event = none)
    (effect : Protected event → frames ≠ []) : StateAt frames (emitStatePrefix event) :=
  StatePrefixEnsures.emit _ (fun _ _ _ ready => (ready.emit quiet effect).1)
    (fun _ _ _ ready => ready.emit quiet effect)

theorem state_capture (body : WGPrefix Event α) (safe : StateAt frames body) :
    StateAt frames (captureWGObserved body) := safe.captureWGObserved

theorem state_receipt (body : WGPrefix Event α) (safe : StateAt frames body)
    (record : WGRunWitness α → Event) (quiet : ∀ r, scope? (record r) = none)
    (effect : ∀ r, Protected (record r) → frames ≠ []) :
    StateAt frames (receiptWGObserved body record) :=
  state_bind (state_capture body safe) (fun r =>
    state_bind (state_emit (record r) (quiet r) (effect r)) (fun _ => state_pure r.value))

theorem state_current (body : Context → WGPrefix Event α) (safe : ∀ context, StateAt frames (body context)) :
    StateAt frames (CausalEffects.atCurrent scope? body) := by
  intro w a history ready
  exact safe (CausalScope.current scope? history) w a history ready

theorem state_focus (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ event, scope? (encode event) = none)
    (effect : ∀ event, Protected (encode event) → frames ≠ []) (body : WGPrefix F α) :
    StateAt frames (focusStatePrefix encode decode body) := by
  intro w a h ready
  let suffix := ((runWGPrefix body w a (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode
  have good : Inv frames (h ++ suffix) := ready.quiet suffix (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact quiet original) (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact effect original)
  refine ⟨suffix,rfl,good.1,?_⟩
  cases (runPrefix (StateT.run (focusStatePrefix encode decode body) w) a h).1 <;> trivial

theorem product_lift (body : Leanux.M α) : ProductAt frames (liftPrefix body) :=
  PrefixEnsures.lift _ (fun _ _ ready => ready.1) (fun _ _ _ _ ready _ => ready)

theorem product_pure (value : α) : ProductAt frames (pure value) :=
  PrefixEnsures.pure (fun _ _ ready => ready.1) (fun _ _ ready => ready)

theorem product_bind {body : PrefixM Event α} {next : α → PrefixM Event β}
    (first : ProductAt frames body) (tail : ∀ value, ProductAt frames (next value)) :
    ProductAt frames (body >>= next) := PrefixEnsures.bind first tail

theorem product_ite (p : Prop) [Decidable p] {a b : PrefixM Event α}
    (ha : p → ProductAt frames a) (hb : ¬p → ProductAt frames b) : ProductAt frames (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem product_forIn (xs : List α) (initial : β) (body : α → β → PrefixM Event (ForInStep β))
    (safe : ∀ value state, ProductAt frames (body value state)) : ProductAt frames (forIn xs initial body) := by
  induction xs generalizing initial with
  | nil => exact product_pure initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply product_bind (safe x initial)
    intro step
    cases step with
    | done state => exact product_pure state
    | yield state => exact ih state

theorem product_range (range : Std.Legacy.Range) (initial : β)
    (body : Nat → β → PrefixM Event (ForInStep β))
    (safe : ∀ value state, ProductAt frames (body value state)) : ProductAt frames (forIn range initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact product_forIn _ initial body safe

theorem product_state (body : WGPrefix Event α) (safe : StateAt frames body) :
    ProductAt frames (liftWGObserver body) := safe.liftWGObserver

theorem product_capture (body : PrefixM Event α) (safe : ProductAt frames body) :
    ProductAt frames (captureObserved body) :=
  safe.captureObserved.consequence (fun _ _ ready => ready) (fun _ _ _ ready => ready.2.1)

theorem product_focus (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ event, scope? (encode event) = none)
    (effect : ∀ event, Protected (encode event) → frames ≠ []) (body : PrefixM F α) :
    ProductAt frames (focusPrefix encode decode body) := by
  intro w h ready
  let suffix := ((runPrefix body w (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode
  have good : Inv frames (h ++ suffix) := ready.quiet suffix (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact quiet original) (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact effect original)
  refine ⟨suffix,rfl,good.1,?_⟩
  cases (runPrefix (focusPrefix encode decode body) w h).1 <;> trivial

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
