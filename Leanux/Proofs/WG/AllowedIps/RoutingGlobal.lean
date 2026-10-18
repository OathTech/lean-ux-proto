import Leanux.Proofs.WG.AllowedIps.RoutingCompletions

/-! Routing state across device absence. Absence denotes empty flat tables;
the existing completion event validity and present-device contracts are retained.
This does not extend the direct allowed-IP primitive to absent devices. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def GlobalRoutedView (view : Option RoutingState) (xs : FlatTable × FlatTable) : Prop :=
  match view with
  | none => xs = ([], [])
  | some _ => RoutedView view xs

def GlobalCompletionState (initial : FlatTable × FlatTable)
    (h : List RoutingCompletion) (w : WGWorld) : Prop :=
  CompletionSafe initial h ∧ GlobalRoutedView (routingView w) (completionFold h initial)

theorem RoutedView.global (hi : RoutedView view xs) : GlobalRoutedView view xs := by
  obtain ⟨d, t4, t6, rfl, hi⟩ := hi
  exact ⟨d, t4, t6, rfl, hi⟩

theorem GlobalRoutedView.present (hi : GlobalRoutedView view xs) (hn : view ≠ none) :
    RoutedView view xs := by
  cases view <;> simp_all [GlobalRoutedView]

theorem GlobalRoutedView.retains (hi : GlobalRoutedView a xs)
    (hr : RetainsRouting a (routingView w)) : GlobalRoutedView (routingView w) xs := by
  cases ha : a with
  | none =>
    cases hv : routingView w with
    | none => simpa [GlobalRoutedView, ha, hv] using hi
    | some s => simp [ha, hv, RetainsRouting] at hr
  | some s =>
    exact (RoutedView.retains (by simpa [GlobalRoutedView, ha] using hi) hr).global

theorem CompletionState.global (hi : CompletionState initial h w) :
    GlobalCompletionState initial h w := ⟨hi.1, hi.2.global⟩

theorem GlobalCompletionState.present (hi : GlobalCompletionState initial h w)
    (hn : routingView w ≠ none) : CompletionState initial h w :=
  ⟨hi.1, hi.2.present hn⟩

/-- Generic whole-call lifts retain the original arbitrary product-action domain.
The projection supplies the routing observation without constraining the rest of the state. -/
theorem global_completion_lift {S : Type} (project : S → WGWorld)
    (initial : FlatTable × FlatTable) (a : StateT S (Except Stop) α)
    (ha : ProjectedRetainsRoutingCall project a) :
    PrefixPreserves (fun h w => GlobalCompletionState initial h (project w))
      (CompletionSafe initial) (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  exact ⟨hi.1, hi.2.retains ((Lifetimes.ProjectedAction.iff_run _ _ _).mp ha w x v hr)⟩

theorem global_completion_same {S : Type} (project : S → WGWorld)
    (initial : FlatTable × FlatTable) (a : StateT S (Except Stop) α)
    (ha : SameView (fun w => routingView (project w)) a) :
    PrefixPreserves (fun h w => GlobalCompletionState initial h (project w))
      (CompletionSafe initial) (liftPrefix a) :=
  global_completion_lift project initial a (ProjectedRetainsRoutingCall.of_same ha)

/-- Native timer, device and receive callers use the actual WG/Ambient stack. -/
theorem global_completion_lift_wg (initial : FlatTable × FlatTable) (a : WG.M α)
    (ha : RetainsRoutingCall a) :
    StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w)
      (CompletionSafe initial) (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w ambient x v ambient' hi hr
  exact ⟨hi.1, hi.2.retains ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp ha
    w ambient x v ambient' hr)⟩

theorem global_completion_same_wg (initial : FlatTable × FlatTable) (a : WG.M α)
    (ha : SameView routingView a) :
    StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w)
      (CompletionSafe initial) (liftWGPrefix a) :=
  global_completion_lift_wg initial a (ProjectedRetainsRoutingCall.of_same ha)

theorem global_completion_drop (initial : FlatTable × FlatTable) :
    StatePrefixEnsures (fun h w _ => CompletionEmpty initial h w) (CompletionSafe initial)
      (liftWGPrefix (modify fun w => {w with dev := none}))
      (fun _ h w _ => GlobalCompletionState initial h w ∧ routingView w = none ∧
        completionFold h initial = ([], [])) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.1)
  intro h w ambient x v ambient' hi hr
  cases hr
  exact ⟨⟨hi.1.1, hi.2⟩, rfl, hi.2⟩

end Leanux.Proofs.WG.AllowedIps
