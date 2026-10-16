import Leanux.Proofs.Logged.FocusComposition
import Leanux.Proofs.Logged.ProjectsUnder

/-! Observation contracts for an actual outer StateT over a prefix observer.
Both native states and the reached journal pass continuously through bind. -/
namespace Leanux.Proofs.Logged
open Leanux

variable {E F Outer Inner α β γ δ : Type}

abbrev StatePrefixT (E Outer Inner : Type) := StateT Outer (PrefixT E Inner)

def runStatePrefix (g : StatePrefixT E Outer Inner α)
    (s : Outer) (t : Inner) (h : List E) :
    Except Stop ((α × Outer) × Inner) × List E := runPrefix (g.run s) t h

def liftStatePrefix (a : StateT Outer (StateT Inner (Except Stop)) α) :
    StatePrefixT E Outer Inner α := fun s => liftPrefix (a.run s)

def emitStatePrefix (e : E) : StatePrefixT E Outer Inner Unit :=
  StateT.lift (emitPrefix e)

def ErasesStatePrefix (g : StatePrefixT E Outer Inner α)
    (a : StateT Outer (StateT Inner (Except Stop)) α) : Prop :=
  ∀ s, ErasesPrefix (g.run s) (a.run s)

def StatePrefixEnsures (P : List E → Outer → Inner → Prop) (S : List E → Prop)
    (g : StatePrefixT E Outer Inner α)
    (Q : α → List E → Outer → Inner → Prop) : Prop :=
  ∀ s, PrefixEnsures (fun h t => P h s t) S (g.run s)
    (fun out h t => Q out.1 h out.2 t)

abbrev StatePrefixPreserves (I : List E → Outer → Inner → Prop) (S : List E → Prop)
    (g : StatePrefixT E Outer Inner α) : Prop :=
  StatePrefixEnsures I S g (fun _ => I)

def StateAppends (g : StatePrefixT E Outer Inner α) : Prop :=
  ∀ s, Appends (g.run s)

def StateHistoryFrame (ρ : E → Option F) (g : StatePrefixT E Outer Inner α) : Prop :=
  ∀ s, HistoryFrame ρ (g.run s)

def StateProjectsPrefix (ρ : E → Option F) (p : α → β)
    (g : StatePrefixT E Outer Inner α) (a : StatePrefixT F Outer Inner β) : Prop :=
  ∀ s, ProjectsPrefix ρ (Prod.map p id) (g.run s) (a.run s)

def focusStatePrefix (encode : E → F) (decode : F → Option E)
    (g : StatePrefixT E Outer Inner α) : StatePrefixT F Outer Inner α :=
  fun s => focusPrefix encode decode (g.run s)

@[simp] theorem runStatePrefix_pure (x : α) (s : Outer) (t : Inner) (h : List E) :
    runStatePrefix (pure x) s t h = (.ok ((x, s), t), h) := rfl

@[simp] theorem runStatePrefix_lift (a : StateT Outer (StateT Inner (Except Stop)) α)
    (s : Outer) (t : Inner) (h : List E) :
    runStatePrefix (liftStatePrefix a) s t h = ((a.run s).run t, h) := rfl

@[simp] theorem runStatePrefix_emit (e : E) (s : Outer) (t : Inner) (h : List E) :
    runStatePrefix (emitStatePrefix e) s t h = (.ok (((), s), t), h ++ [e]) := rfl

@[simp] theorem runStatePrefix_throw (e : Stop) (s : Outer) (t : Inner) (h : List E) :
    runStatePrefix (throw e : StatePrefixT E Outer Inner α) s t h = (.error e, h) := rfl

theorem runStatePrefix_bind (g : StatePrefixT E Outer Inner α)
    (f : α → StatePrefixT E Outer Inner β) (s : Outer) (t : Inner) (h : List E) :
    runStatePrefix (g >>= f) s t h =
      match runStatePrefix g s t h with
      | (.error e, h') => (.error e, h')
      | (.ok ((x, s'), t'), h') => runStatePrefix (f x) s' t' h' :=
by
  unfold runStatePrefix
  rw [StateT.run_bind, runPrefix_bind]
  cases hr : runPrefix (g.run s) t h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out => rcases out with ⟨⟨x, s'⟩, t'⟩; rfl

theorem erasesStatePrefix_pure (x : α) :
    ErasesStatePrefix (pure x : StatePrefixT E Outer Inner α) (pure x) :=
  fun _ => erasesPrefix_pure _

theorem erasesStatePrefix_lift (a : StateT Outer (StateT Inner (Except Stop)) α) :
    ErasesStatePrefix (liftStatePrefix a : StatePrefixT E Outer Inner α) a :=
  fun s => erasesPrefix_lift (a.run s)

theorem erasesStatePrefix_emit (e : E) :
    ErasesStatePrefix (emitStatePrefix e : StatePrefixT E Outer Inner Unit) (pure ()) := by
  intro s t h
  rfl

theorem erasesStatePrefix_bind {g : StatePrefixT E Outer Inner α}
    {a : StateT Outer (StateT Inner (Except Stop)) α}
    {f : α → StatePrefixT E Outer Inner β}
    {b : α → StateT Outer (StateT Inner (Except Stop)) β}
    (hg : ErasesStatePrefix g a) (hf : ∀ x, ErasesStatePrefix (f x) (b x)) :
    ErasesStatePrefix (g >>= f) (a >>= b) :=
  fun s => erasesPrefix_bind (hg s) (fun out => hf out.1 out.2)

theorem erasesStatePrefix_forIn (xs : List α) (init : β)
    (g : α → β → StatePrefixT E Outer Inner (ForInStep β))
    (a : α → β → StateT Outer (StateT Inner (Except Stop)) (ForInStep β))
    (hg : ∀ x b, ErasesStatePrefix (g x b) (a x b)) :
    ErasesStatePrefix (forIn xs init g) (forIn xs init a) := by
  induction xs generalizing init with
  | nil => exact erasesStatePrefix_pure init
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply erasesStatePrefix_bind (hg x init)
    intro step
    cases step with
    | done b => exact erasesStatePrefix_pure b
    | yield b => exact ih b

variable {P : List E → Outer → Inner → Prop} {S : List E → Prop}
  {Q : α → List E → Outer → Inner → Prop}
  {R : β → List E → Outer → Inner → Prop}
  {g : StatePrefixT E Outer Inner α} {f : α → StatePrefixT E Outer Inner β}

theorem StatePrefixEnsures.pure (x : α) (hs : ∀ h s t, P h s t → S h)
    (hq : ∀ h s t, P h s t → Q x h s t) :
    StatePrefixEnsures P S (pure x) Q :=
  fun s => PrefixEnsures.pure (fun h t => hs h s t) (fun h t => hq h s t)

theorem StatePrefixEnsures.lift (a : StateT Outer (StateT Inner (Except Stop)) α)
    (hs : ∀ h s t, P h s t → S h)
    (hq : ∀ h s t x s' t', P h s t →
      (a.run s).run t = .ok ((x, s'), t') → Q x h s' t') :
    StatePrefixEnsures P S (liftStatePrefix a) Q :=
  fun s => PrefixEnsures.lift (a.run s) (fun h t => hs h s t)
    (fun h t out t' => hq h s t out.1 out.2 t')

theorem StatePrefixEnsures.emit (e : E)
    {Q : Unit → List E → Outer → Inner → Prop}
    (hs : ∀ h s t, P h s t → S (h ++ [e]))
    (hq : ∀ h s t, P h s t → Q () (h ++ [e]) s t) :
    StatePrefixEnsures P S (emitStatePrefix e) Q := by
  intro s t h hp
  exact ⟨[e], rfl, hs h s t hp, hq h s t hp⟩

theorem StatePrefixEnsures.bind (hg : StatePrefixEnsures P S g Q)
    (hf : ∀ x, StatePrefixEnsures (Q x) S (f x) R) :
    StatePrefixEnsures P S (g >>= f) R :=
  fun s => PrefixEnsures.bind (hg s) (fun out => hf out.1 out.2)

theorem StatePrefixEnsures.consequence (hg : StatePrefixEnsures P S g Q)
    {P' : List E → Outer → Inner → Prop}
    {Q' : α → List E → Outer → Inner → Prop}
    (hp : ∀ h s t, P' h s t → P h s t)
    (hq : ∀ x h s t, Q x h s t → Q' x h s t) : StatePrefixEnsures P' S g Q' :=
  fun s => (hg s).consequence (fun h t => hp h s t) (fun out h t => hq out.1 h out.2 t)

theorem StatePrefixEnsures.forInInvariant (xs : List α) (init : β)
    (g : α → β → StatePrefixT E Outer Inner (ForInStep β))
    (I : β → List E → Outer → Inner → Prop) (S : List E → Prop)
    (hs : ∀ b h s t, I b h s t → S h)
    (hg : ∀ x b, StatePrefixEnsures (I b) S (g x b) (fun step => I step.value)) :
    StatePrefixEnsures (I init) S (forIn xs init g) I := by
  induction xs generalizing init with
  | nil => exact StatePrefixEnsures.pure init (hs init) (fun _ _ _ hi => hi)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StatePrefixEnsures.bind (hg x init)
    intro step
    cases step with
    | done b => exact StatePrefixEnsures.pure b (hs b) (fun _ _ _ hi => hi)
    | yield b => exact ih b

theorem StateAppends.pure (x : α) :
    StateAppends (pure x : StatePrefixT E Outer Inner α) := fun _ => Appends.pure _

theorem StateAppends.lift (a : StateT Outer (StateT Inner (Except Stop)) α) :
    StateAppends (liftStatePrefix a : StatePrefixT E Outer Inner α) :=
  fun s => Appends.lift (a.run s)

theorem StateAppends.bind (hg : StateAppends g) (hf : ∀ x, StateAppends (f x)) :
    StateAppends (g >>= f) := fun s => (hg s).bind (fun out => hf out.1 out.2)

theorem StateHistoryFrame.bind {ρ : E → Option F}
    (hg : StateHistoryFrame ρ g) (hf : ∀ x, StateHistoryFrame ρ (f x)) :
    StateHistoryFrame ρ (g >>= f) := fun s => (hg s).bind (fun out => hf out.1 out.2)

theorem StateProjectsPrefix.bind (ρ : E → Option F) (p : α → β) (q : γ → δ)
    {g : StatePrefixT E Outer Inner α} {a : StatePrefixT F Outer Inner β}
    {f : α → StatePrefixT E Outer Inner γ} {b : β → StatePrefixT F Outer Inner δ}
    (hg : StateProjectsPrefix ρ p g a)
    (hf : ∀ x, StateProjectsPrefix ρ q (f x) (b (p x))) :
    StateProjectsPrefix ρ q (g >>= f) (a >>= b) := by
  intro s
  rw [StateT.run_bind, StateT.run_bind]
  apply projectsPrefix_bind ρ (Prod.map p id) (Prod.map q id) (hg s)
  intro out
  exact hf out.1 out.2

theorem focusStatePrefix_erases (encode : E → F) (decode : F → Option E)
    {a : StateT Outer (StateT Inner (Except Stop)) α}
    (hg : ErasesStatePrefix g a) : ErasesStatePrefix (focusStatePrefix encode decode g) a :=
  fun s => focusPrefix_erases encode decode (hg s)

theorem StatePrefixEnsures.focus (encode : E → F) (decode : F → Option E)
    (hd : ∀ e, decode (encode e) = some e) (hg : StatePrefixEnsures P S g Q) :
    StatePrefixEnsures (fun h s t => P (h.filterMap decode) s t)
      (fun h => S (h.filterMap decode)) (focusStatePrefix encode decode g)
      (fun x h s t => Q x (h.filterMap decode) s t) :=
  fun s => (hg s).focus encode decode hd

theorem StateAppends.focus (encode : E → F) (decode : F → Option E)
    (g : StatePrefixT E Outer Inner α) : StateAppends (focusStatePrefix encode decode g) :=
  fun s => Appends.focus encode decode (g.run s)

/-- Projection under an invariant over the two actual state components. -/
def StateProjectsUnder (I : List F → Outer → Inner → Prop) (ρ : E → Option F)
    (g : StatePrefixT E Outer Inner α) (a : StatePrefixT F Outer Inner α) : Prop :=
  ∀ s t h, I (h.filterMap ρ) s t →
    runStatePrefix a s t (h.filterMap ρ) =
      ((runStatePrefix g s t h).1, (runStatePrefix g s t h).2.filterMap ρ)

theorem stateProjectsUnder_pure {I : List F → Outer → Inner → Prop}
    (ρ : E → Option F) (x : α) :
    StateProjectsUnder I ρ (pure x) (pure x) := by intro s t h _; rfl

theorem stateProjectsUnder_lift {I : List F → Outer → Inner → Prop}
    (ρ : E → Option F) (a : StateT Outer (StateT Inner (Except Stop)) α) :
    StateProjectsUnder I ρ (liftStatePrefix a) (liftStatePrefix a) := by
  intro s t h _; rfl

theorem stateProjectsUnder_bind {I : List F → Outer → Inner → Prop} {S : List F → Prop}
    {ρ : E → Option F} {g : StatePrefixT E Outer Inner α}
    {a : StatePrefixT F Outer Inner α} {f : α → StatePrefixT E Outer Inner β}
    {b : α → StatePrefixT F Outer Inner β}
    (hg : StateProjectsUnder I ρ g a) (ha : StatePrefixPreserves I S a)
    (hf : ∀ x, StateProjectsUnder I ρ (f x) (b x)) :
    StateProjectsUnder I ρ (g >>= f) (a >>= b) := by
  intro s t h hi
  have he := hg s t h hi
  obtain ⟨suffix, _, _, hp⟩ := ha s t (h.filterMap ρ) hi
  have he' : runPrefix (a.run s) t (h.filterMap ρ) =
      ((runStatePrefix g s t h).1, (runStatePrefix g s t h).2.filterMap ρ) := he
  rw [he'] at hp
  rw [runStatePrefix_bind, runStatePrefix_bind, he]
  cases hr : runStatePrefix g s t h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out =>
      rcases out with ⟨⟨x, s'⟩, t'⟩
      exact hf x s' t' hist (by simpa only [hr] using hp)

theorem stateProjectsUnder_focus {I : List E → Outer → Inner → Prop} {S : List E → Prop}
    (encode : E → F) (decode : F → Option E) (hd : ∀ e, decode (encode e) = some e)
    {a : StatePrefixT E Outer Inner α} (ha : StatePrefixPreserves I S a) :
    StateProjectsUnder I decode (focusStatePrefix encode decode a) a := by
  intro s
  exact projectsUnder_focus encode decode hd
    (fun t h hi => let ⟨suffix, hs, _, _⟩ := ha s t h hi; ⟨suffix, hs⟩)

end Leanux.Proofs.Logged
