import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalAllModeSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalClaims
import Leanux.Proofs.WG.TimerDiscipline.ResponseTraversalClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The original outgoing initiation retains its creation/early-exit and hook
presence facts. Any reached traversal has its exact all-mode immediate effect,
before authenticated-sent deletion, send and retransmit rearming. -/
theorem observedInitiationTraversal_all_modes (pid : PeerId) :
    Campaign2.Product.Ensures (observedInitiationTraversal pid) (fun _ => True)
      (fun cut _ => InitiationTraversalFacts pid cut ∧
        ∀ hook, cut.traversal = some hook →
          TraversalAllModeEffect pid hook.before.toSnapshot hook.after.toSnapshot) := by
  intro entry cut final pre run
  refine ⟨observedInitiationTraversal_facts pid entry cut final pre run, ?_⟩
  have keep {α : Type} (action : Leanux.M α) (P : Prop) :
      Noise.Product.Ensures action (fun _ => P) (fun _ _ => P) := by
    intro initial result final pre run
    exact pre
  have carried : Noise.Product.Ensures (observedInitiationTraversal pid) (fun _ => True)
      (fun cut _ => ∀ hook, cut.traversal = some hook →
        TraversalAllModeEffect pid hook.before.toSnapshot hook.after.toSnapshot) := by
    unfold observedInitiationTraversal
    refine Noise.Product.ensures_bind _ _ (keep _ True) ?_
    intro message
    cases message with
    | none =>
      intro initial cut final pre run hook impossible
      cases run
      cases impossible
    | some msg =>
      refine Noise.Product.ensures_bind _ _ (dataDoneTraversal_all_modes pid) ?_
      intro hook
      refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
      intro ignored initial cut final facts run other same
      cases run
      cases same
      exact facts.2
  exact carried entry cut final pre run

/-- Actual response traversal remains conditional on session success. This
retains that original certificate and adds the reached hook's all-mode effect,
without inferring a final expiry after the unchanged response-send suffix. -/
theorem observedResponseTraversal_all_modes (pid : PeerId) :
    Campaign2.Product.Ensures (observedResponseTraversal pid) (fun _ => True)
      (fun cut _ => ResponseTraversalFacts pid cut ∧
        ∀ hook, cut.traversal = some hook →
          TraversalAllModeEffect pid hook.before.toSnapshot hook.after.toSnapshot) := by
  intro entry cut final pre run
  refine ⟨observedResponseTraversal_facts pid entry cut final pre run, ?_⟩
  have keep {α : Type} (action : Leanux.M α) (P : Prop) :
      Noise.Product.Ensures action (fun _ => P) (fun _ _ => P) := by
    intro initial result final pre run
    exact pre
  have prefixFacts : Noise.Product.Ensures (responseTraversalPrefix pid) (fun _ => True)
      (fun cut _ => ∀ hook, cut.traversal = some hook →
        TraversalAllModeEffect pid hook.before.toSnapshot hook.after.toSnapshot) := by
    unfold responseTraversalPrefix
    refine Noise.Product.ensures_bind _ _ (keep _ True) ?_
    intro response
    refine Noise.Product.ensures_bind _ _ (keep _ True) ?_
    intro before
    cases chosen : (response.map (·.session.begun)).getD false with
    | false =>
      simp only [Bool.false_eq_true, ite_false, pure_bind]
      intro initial cut final pre run hook impossible
      cases run
      cases impossible
    | true =>
      simp only [ite_true, pure_bind]
      refine Noise.Product.ensures_bind _ _ (dataDoneTraversal_all_modes pid) ?_
      intro hook initial cut final facts run other same
      cases run
      cases same
      exact facts.2
  have carried : Noise.Product.Ensures (observedResponseTraversal pid) (fun _ => True)
      (fun cut _ => ∀ hook, cut.traversal = some hook →
        TraversalAllModeEffect pid hook.before.toSnapshot hook.after.toSnapshot) := by
    unfold observedResponseTraversal
    refine Noise.Product.ensures_bind _ _ prefixFacts ?_
    intro cut
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro ignored initial out final facts run
    cases run
    exact facts
  exact carried entry cut final pre run

end Leanux.Proofs.WG.TimerDiscipline
