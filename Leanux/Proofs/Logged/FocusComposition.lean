import Leanux.Proofs.Logged.ProjectsUnder

/-! Focus composition uses the lower observer's actual appended history.
No operation is assumed independent of its incoming journal. -/
namespace Leanux.Proofs.Logged
open Leanux

variable {State : Type}

variable {E G α β γ : Type}

/-- Exact focus agreement at an invariant-valid entry, including Stops. -/
def FocusesUnder (I : List E → State → Prop) (encode : E → G)
    (decode : G → Option E) (g : PrefixT G State α) (a : PrefixT E State α) : Prop :=
  ∀ w h, I (h.filterMap decode) w →
    runPrefix g w h = runPrefix (focusPrefix encode decode a) w h

variable {I : List E → State → Prop} {S : List E → Prop}
  {encode : E → G} {decode : G → Option E}

theorem FocusesUnder.focus (a : PrefixT E State α) :
    FocusesUnder I encode decode (focusPrefix encode decode a) a := fun _ _ _ => rfl

theorem FocusesUnder.pure (x : α) :
    FocusesUnder I encode decode (pure x) (pure x) := by
  intro w h _
  change (Except.ok (ε := Stop) (x, w), h) = (Except.ok (x, w), h ++ ((h.filterMap decode).drop (h.filterMap decode).length).map encode)
  simp

theorem FocusesUnder.lift (a : StateT State (Except Stop) α) :
    FocusesUnder I encode decode (liftPrefix a) (liftPrefix a) := by
  intro w h _
  change (a.run w, h) = (a.run w, h ++ ((h.filterMap decode).drop (h.filterMap decode).length).map encode)
  simp

/-- The continuation receives precisely the first call's actual output
history. Its own append contract is needed even on a failed continuation. -/
theorem FocusesUnder.bind
    (hd : ∀ e, decode (encode e) = some e)
    (hg : FocusesUnder I encode decode g a)
    (ha : PrefixPreserves I S a)
    (hf : ∀ x, FocusesUnder I encode decode (f x) (b x))
    (hb : ∀ x, PrefixPreserves I S (b x)) :
    FocusesUnder I encode decode (g >>= f) (a >>= b) := by
  intro w h hi
  obtain ⟨s, hs, _, hp⟩ := ha w (h.filterMap decode) hi
  have ar : runPrefix a w (h.filterMap decode) =
      ((runPrefix a w (h.filterMap decode)).1, h.filterMap decode ++ s) := Prod.ext rfl hs
  have gr := (hg w h hi).trans (focusPrefix_suffix encode decode a w h _ s ar)
  have hh : (h ++ s.map encode).filterMap decode = h.filterMap decode ++ s := by
    rw [List.filterMap_append, filterMap_encoded encode decode hd]
  rw [runPrefix_bind, gr]
  cases hr : (runPrefix a w (h.filterMap decode)).1 with
  | error e =>
    dsimp only
    symm
    apply focusPrefix_suffix
    rw [runPrefix_bind, ar, hr]
  | ok out =>
    rcases out with ⟨x, v⟩
    dsimp only
    have hv : I (h.filterMap decode ++ s) v := by simpa only [hr, hs] using hp
    obtain ⟨t, ht, _, _⟩ := hb x v (h.filterMap decode ++ s) hv
    have br : runPrefix (b x) v ((h ++ s.map encode).filterMap decode) =
        ((runPrefix (b x) v (h.filterMap decode ++ s)).1,
          (h ++ s.map encode).filterMap decode ++ t) := by rw [hh]; exact Prod.ext rfl ht
    rw [hf x v (h ++ s.map encode) (hh ▸ hv),
      focusPrefix_suffix encode decode (b x) v (h ++ s.map encode) _ t br]
    symm
    have abr : runPrefix (a >>= b) w (h.filterMap decode) =
        ((runPrefix (b x) v (h.filterMap decode ++ s)).1,
          h.filterMap decode ++ (s ++ t)) := by
      rw [runPrefix_bind, ar, hr]
      exact Prod.ext rfl (by simpa only [List.append_assoc] using ht)
    rw [focusPrefix_suffix encode decode (a >>= b) w h _ (s ++ t) abr]
    simp only [List.map_append, List.append_assoc]

theorem FocusesUnder.forIn (hd : ∀ e, decode (encode e) = some e)
    (xs : List γ) (init : β)
    (g : γ → β → PrefixT G State (ForInStep β)) (a : γ → β → PrefixT E State (ForInStep β))
    (hs : ∀ h w, I h w → S h)
    (ha : ∀ x z, PrefixPreserves I S (a x z))
    (hg : ∀ x z, FocusesUnder I encode decode (g x z) (a x z)) :
    FocusesUnder I encode decode (forIn xs init g) (forIn xs init a) := by
  induction xs generalizing init with
  | nil => exact FocusesUnder.pure init
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply FocusesUnder.bind hd (hg x init) (ha x init)
    · intro step
      cases step with
      | done z => exact FocusesUnder.pure z
      | yield z => exact ih z
    · intro step
      cases step with
      | done z => exact PrefixPreserves.pure hs z
      | yield z => exact PrefixPreserves.forIn xs z a hs ha

/-- Unconditional append contracts suffice for exact focus/bind distribution;
the conditional interface above also transports an existing state invariant. -/
theorem focusPrefix_bind_appends (encode : E → G) (decode : G → Option E)
    (hd : ∀ e, decode (encode e) = some e)
    (ha : Appends a) (hb : ∀ x, Appends (b x)) (w : State) (h : List G) :
    runPrefix (focusPrefix encode decode a >>= fun x => focusPrefix encode decode (b x)) w h =
      runPrefix (focusPrefix encode decode (a >>= b)) w h := by
  have preserve {δ : Type} (q : PrefixT E State δ) (hq : Appends q) :
      PrefixPreserves (fun _ _ => True) (fun _ => True) q := by
    intro v hist _
    obtain ⟨s, hs⟩ := hq v hist
    refine ⟨s, hs, True.intro, ?_⟩
    cases (runPrefix q v hist).1 <;> trivial
  exact FocusesUnder.bind hd (FocusesUnder.focus a) (preserve a ha)
    (fun x => FocusesUnder.focus (b x)) (fun x => preserve (b x) (hb x)) w h True.intro

end Leanux.Proofs.Logged
