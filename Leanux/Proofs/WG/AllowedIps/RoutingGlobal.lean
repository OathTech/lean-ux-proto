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
    (h : List RoutingCompletion) (w : World) : Prop :=
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

theorem global_completion_lift (initial : FlatTable × FlatTable) (a : M α)
    (ha : RetainsRoutingCall a) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  exact ⟨hi.1, hi.2.retains (ha w x v hr)⟩

theorem global_completion_same (initial : FlatTable × FlatTable) (a : M α)
    (ha : SameView routingView a) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (liftPrefix a) :=
  global_completion_lift initial a (.of_same ha)

theorem global_completion_drop (initial : FlatTable × FlatTable) :
    PrefixEnsures (CompletionEmpty initial) (CompletionSafe initial)
      (liftPrefix (modifyK fun k => {k with wg := none}))
      (fun _ h w => GlobalCompletionState initial h w ∧ routingView w = none ∧
        completionFold h initial = ([], [])) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.1)
  intro h w x v hi hr
  cases hr
  exact ⟨⟨hi.1.1, hi.2⟩, rfl, hi.2⟩

end Leanux.Proofs.WG.AllowedIps
