import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsExecution
import Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffectsFocus

/-! Exact event embeddings needed to preserve the existing lifetime and socket
journal while observing completion effects in the joint driver. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

theorem focus_matching (ρ : E → Option F)
    (eg : L → E) (dg : E → Option L) (et : L → F) (dt : F → Option L)
    (enc : ∀ e, ρ (eg e) = some (et e))
    (dec : ∀ e, dg e = (ρ e).bind dt) (action : PrefixT L State α) :
    ProjectsPrefix ρ id (focusPrefix eg dg action) (focusPrefix et dt action) := by
  intro w h
  have histories : (h.filterMap ρ).filterMap dt = h.filterMap dg := by
    rw [List.filterMap_filterMap]
    congr 1
    funext e
    exact (dec e).symm
  change ((runPrefix action w ((h.filterMap ρ).filterMap dt)).1,
      h.filterMap ρ ++ ((runPrefix action w ((h.filterMap ρ).filterMap dt)).2.drop
        ((h.filterMap ρ).filterMap dt).length).map et) =
    ((runPrefix action w (h.filterMap dg)).1.map (fun (x,v) => (id x,v)),
      (h ++ ((runPrefix action w (h.filterMap dg)).2.drop (h.filterMap dg).length).map eg).filterMap ρ)
  rw [histories,List.filterMap_append,List.filterMap_map]
  have events (xs : List L) : xs.filterMap (ρ ∘ eg) = xs.map et := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.filterMap_cons,Function.comp_apply,enc,List.map_cons,ih]
  rw [events]
  cases (runPrefix action w (h.filterMap dg)).1 <;> rfl

theorem focus_composed (e₁ : L → E) (d₁ : E → Option L)
    (e₂ : E → F) (d₂ : F → Option E) (action : PrefixT L State α) :
    focusPrefix e₂ d₂ (focusPrefix e₁ d₁ action) =
      focusPrefix (e₂ ∘ e₁) (fun e => (d₂ e).bind d₁) action := by
  funext w h
  change ((runPrefix action w ((h.filterMap d₂).filterMap d₁)).1,
    h ++ (((h.filterMap d₂) ++ ((runPrefix action w ((h.filterMap d₂).filterMap d₁)).2.drop
      ((h.filterMap d₂).filterMap d₁).length).map e₁).drop (h.filterMap d₂).length).map e₂) = _
  simp only [List.drop_left,List.map_map,List.filterMap_filterMap]
  rfl

theorem state_focus_matching (ρ : E → Option F)
    (eg : L → E) (dg : E → Option L) (et : L → F) (dt : F → Option L)
    (enc : ∀ e, ρ (eg e) = some (et e))
    (dec : ∀ e, dg e = (ρ e).bind dt) (action : WGPrefix L α) :
    StateProjectsPrefix ρ id (focusStatePrefix eg dg action) (focusStatePrefix et dt action) := by
  intro w a h
  simpa only [focusStatePrefix,StateT.run,Prod.map,id,Prod.eta] using
    focus_matching ρ eg dg et dt enc dec (action.run w) a h

theorem lift_focus (encode : L → E) (decode : E → Option L) (action : WGPrefix L α) :
    liftWGObserver (focusStatePrefix encode decode action) =
      focusPrefix encode decode (liftWGObserver action) := by
  funext w h
  rfl

def lifetimeEvent : LifetimeEvent → Completion.Event :=
  Completion.Event.disposition ∘ TxDisposition.Event.access

def lifetime? (event : Completion.Event) : Option LifetimeEvent :=
  (Completion.disposition? event).bind TxDisposition.accessEvent

theorem access_factor (action : MixedM α) :
    Completion.access action =
      liftWGObserver (focusStatePrefix lifetimeEvent lifetime? action) := by
  unfold Completion.access TxDisposition.nativeAccess TxDisposition.access
  rw [focus_composed,← lift_focus]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
