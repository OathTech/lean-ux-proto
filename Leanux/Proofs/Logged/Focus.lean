import Leanux.Proofs.Logged.Prefix
import Leanux.Proofs.Framing.Projection

/-! Reuse a local failure-retaining observer inside a tagged event stream.
Only its new suffix is injected, preserving the prior global interleaving. -/
namespace Leanux.Proofs.Logged
open Leanux Leanux.Proofs.Framing

def focusPrefix (encode : E → G) (decode : G → Option E)
    (g : PrefixM E α) : PrefixM G α :=
  fun w => ExceptT.mk fun h =>
    let initial := h.filterMap decode
    let out := runPrefix g w initial
    (out.1, h ++ (out.2.drop initial.length).map encode)

theorem focusPrefix_erases (encode : E → G) (decode : G → Option E)
    (hg : ErasesPrefix g a) : ErasesPrefix (focusPrefix encode decode g) a :=
  fun w h => hg w (h.filterMap decode)

theorem focusPrefix_suffix (encode : E → G) (decode : G → Option E)
    (g : PrefixM E α) (w : World) (h : List G) (out : Except Stop (α × World))
    (suffix : List E)
    (hr : runPrefix g w (h.filterMap decode) = (out, h.filterMap decode ++ suffix)) :
    runPrefix (focusPrefix encode decode g) w h = (out, h ++ suffix.map encode) := by
  change ((runPrefix g w _).1, h ++ ((runPrefix g w _).2.drop _).map _) = _
  rw [hr]
  simp

theorem filterMap_encoded (encode : E → G) (decode : G → Option E)
    (hd : ∀ e, decode (encode e) = some e) (es : List E) :
    (es.map encode).filterMap decode = es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [hd, ih]

theorem filterMap_disjoint (encode : E → G) (decode : G → Option F)
    (hd : ∀ e, decode (encode e) = none) (es : List E) :
    (es.map encode).filterMap decode = [] := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [hd, ih]

theorem focusPrefix_other (encode : E → G) (decode : G → Option E)
    (other : G → Option F) (hd : ∀ e, other (encode e) = none)
    (g : PrefixM E α) (w : World) (h : List G) :
    (runPrefix (focusPrefix encode decode g) w h).2.filterMap other = h.filterMap other := by
  change (h ++ _).filterMap other = _
  rw [List.filterMap_append, filterMap_disjoint encode other hd]
  simp

theorem PrefixEnsures.focus (encode : E → G) (decode : G → Option E)
    (hd : ∀ e, decode (encode e) = some e) (hg : PrefixEnsures P S g Q) :
    PrefixEnsures (fun h w => P (h.filterMap decode) w)
      (fun h => S (h.filterMap decode)) (focusPrefix encode decode g)
      (fun x h w => Q x (h.filterMap decode) w) := by
  intro w h hi
  obtain ⟨suffix, he, hs, hq⟩ := hg w (h.filterMap decode) hi
  have hr : runPrefix g w (h.filterMap decode) =
      ((runPrefix g w (h.filterMap decode)).1, h.filterMap decode ++ suffix) :=
    Prod.ext rfl he
  rw [focusPrefix_suffix encode decode g w h _ suffix hr]
  have hp : (h ++ suffix.map encode).filterMap decode = h.filterMap decode ++ suffix := by
    rw [List.filterMap_append, filterMap_encoded encode decode hd]
  refine ⟨suffix.map encode, rfl, ?_, ?_⟩
  · simpa only [hp, he] using hs
  · simpa only [hp, he] using hq

/-- Keep an arbitrary cached predicate through an observed action whose
original execution preserves its view. The existing error-prefix condition
is retained; the extra predicate is required only on successful outcomes. -/
theorem PrefixEnsures.frameView (hg : PrefixEnsures P S g Q)
    (he : ErasesPrefix g a) (view : World → σ) (hv : SameView view a) (R : σ → Prop) :
    PrefixEnsures (fun h w => P h w ∧ R (view w)) S g
      (fun x h w => Q x h w ∧ R (view w)) := by
  intro w h hi
  obtain ⟨suffix, hsuf, hs, hq⟩ := hg w h hi.1
  refine ⟨suffix, hsuf, hs, ?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    have ho : a.run w = .ok out := (he w h).symm.trans hr
    exact ⟨by simpa only [hr] using hq, (hv w out.1 out.2 ho) ▸ hi.2⟩

end Leanux.Proofs.Logged
