import Leanux.Proofs.WG.Origins.CurrentHistory

/-! Current-identity composition on the unchanged focused observers. These
rules constrain actual appended constructors and normal native effects; they
do not substitute endpoint erasure for equality of observation journals. -/
namespace Leanux.Proofs.WG.CurrentHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
open Origins.HistorySupport (sessions sessionEvent)

theorem congr (hg : Preserves g)
    (he : ∀ w h, runPrefix g w h = runPrefix f w h) : Preserves f := by
  intro w h hi
  simpa only [← he w h] using hg w h hi

theorem focused_life (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E)
    (inj : LifetimeEvent → E) (proj : E → Option LifetimeEvent)
    (quiet : ∀ e, sessionEvent (enc (inj e)) = none)
    (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (state : ∀ history, Framing.Preserves
      (fun w : World => CurrentLifecycle.Inv history w.wg) a) :
    Preserves (focusPrefix enc dec (focusPrefix inj proj g)) := by
  apply erased _ a (Appends.focus _ _ _) (focusPrefix_erases _ _
    (focusPrefix_erases _ _ erases)) _ state
  intro w h
  unfold sessions
  rw [Origins.HistorySupport.focus_compose]
  exact focusPrefix_other _ _ sessionEvent quiet _ w h

theorem origin_life (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (state : ∀ history, Framing.Preserves
      (fun w : World => CurrentLifecycle.Inv history w.wg) a) :
    Preserves (Origins.HistoryAdapters.focus (Origins.HistoryAdapters.life g)) :=
  focused_life _ _ _ _ (fun _ => rfl) g a erases state

theorem rx_life (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (state : ∀ history, Framing.Preserves
      (fun w : World => CurrentLifecycle.Inv history w.wg) a) :
    Preserves (focusPrefix Origins.HistorySupport.rxEncode Origins.HistorySupport.rxDecode
      (MaterialOrigin.access g)) :=
  focused_life _ _ _ _ (fun _ => rfl) g a erases state

def Focused (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E)
    (g : PrefixM E α) : Prop := Appends g ∧ Preserves (focusPrefix enc dec g)

theorem focused_bind (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E)
    (inverse : ∀ e, dec (enc e) = some e) (g : PrefixM E α) (f : α → PrefixM E β)
    (hg : Focused enc dec g) (hf : ∀ x, Focused enc dec (f x)) :
    Focused enc dec (g >>= f) :=
  ⟨hg.1.bind (fun x => (hf x).1),
    congr (hg.2.bind (fun x => (hf x).2))
      (focusPrefix_bind_appends enc dec inverse hg.1 (fun x => (hf x).1))⟩

theorem focused_pure (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E) (x : α) :
    Focused enc dec (pure x) := by
  refine ⟨Appends.pure x,?_⟩
  apply congr (PrefixPreserves.pure (I := StateInv) (fun _ _ _ => True.intro) x)
  intro w h
  change (Except.ok (ε := Stop) (x,w),h) =
    (.ok (x,w),h ++ ((h.filterMap dec).drop (h.filterMap dec).length).map enc)
  simp

theorem focused_lift (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E)
    (a : Leanux.M α)
    (state : ∀ history, Framing.Preserves
      (fun w : World => CurrentLifecycle.Inv history w.wg) a) :
    Focused enc dec (liftPrefix a) := by
  refine ⟨Appends.lift a,?_⟩
  apply congr (lift a state)
  intro w h
  change (a.run w,h) =
    (a.run w,h ++ ((h.filterMap dec).drop (h.filterMap dec).length).map enc)
  simp

theorem focused_ite (enc : E → RxHistory.Event) (dec : RxHistory.Event → Option E)
    (p : Prop) [Decidable p]
    (ha : p → Focused enc dec a) (hb : ¬p → Focused enc dec b) :
    Focused enc dec (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

end Leanux.Proofs.WG.CurrentHistory
