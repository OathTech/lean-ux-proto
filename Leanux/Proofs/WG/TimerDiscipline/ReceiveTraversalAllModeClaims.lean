import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalAllModeSource
import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The same full initiation receiver retains its authentication and recorded
hook facts, strengthened with all-mode effects at the actual traversal cut. -/
theorem observedInitiationReceiveTraversal_all_modes (msg : List UInt8) (src : SkbSource) :
    Campaign2.Product.Ensures (observedInitiationReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → InitiationReceiveTraversalFacts msg cut ∧
        TraversalAllModeEffect cut.authentication.consumed.pid
          cut.traversal.before.toSnapshot cut.traversal.after.toSnapshot) := by
  have keep {α : Type} (action : Leanux.M α) (P : Prop) :
      Noise.Product.Ensures action (fun _ => P) (fun _ _ => P) := by
    intro initial result final pre run
    exact pre
  change Noise.Product.Ensures _ _ _
  unfold observedInitiationReceiveTraversal
  refine Noise.Product.ensures_bind
    (Q := fun candidate _ => ∀ cut, candidate = some cut → Roaming.Product.InitiationCallFacts msg cut)
    _ _ (fun initial candidate final pre run cut same =>
      (Roaming.Product.initiationCallPrefix_facts msg src initial candidate final pre run cut same).2) ?_
  intro candidate
  cases candidate with
  | none =>
    intro initial out final h run cut impossible
    cases run
    cases impossible
  | some cut =>
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro ignored
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro ignored
    refine Noise.Product.ensures_bind
      (Q := fun hook _ => Roaming.Product.InitiationCallFacts msg cut ∧ DataDoneTraversalFacts cut.consumed.pid hook ∧
        TraversalAllModeEffect cut.consumed.pid hook.before.toSnapshot hook.after.toSnapshot)
      _ _ (fun initial hook final h run =>
        ⟨h cut rfl, observedReceiveTraversalCommon_all_modes msg cut.consumed.pid initial hook final trivial run⟩) ?_
    intro hook initial out final facts run other same
    cases run
    cases same
    exact ⟨⟨facts.1, facts.2.1⟩, facts.2.2⟩

/-- The same full response receiver retains its original authentication facts
and actual traversal cut, without requiring session success or recorded mode. -/
theorem observedResponseReceiveTraversal_all_modes (msg : List UInt8) (src : SkbSource) :
    Campaign2.Product.Ensures (observedResponseReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → ResponseReceiveTraversalFacts msg cut ∧
        TraversalAllModeEffect cut.authentication.consumed.input.pid
          cut.traversal.before.toSnapshot cut.traversal.after.toSnapshot) := by
  have keep {α : Type} (action : Leanux.M α) (P : Prop) :
      Noise.Product.Ensures action (fun _ => P) (fun _ _ => P) := by
    intro initial result final pre run
    exact pre
  change Noise.Product.Ensures _ _ _
  unfold observedResponseReceiveTraversal
  refine Noise.Product.ensures_bind
    (Q := fun candidate _ => ∀ cut, candidate = some cut → Roaming.Product.ResponseCallFacts msg cut)
    _ _ (fun initial candidate final pre run cut same =>
      (Roaming.Product.responseCallPrefix_facts msg src initial candidate final pre run cut same).2) ?_
  intro candidate
  cases candidate with
  | none =>
    intro initial out final h run cut impossible
    cases run
    cases impossible
  | some cut =>
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro ignored
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro ignored
    refine Noise.Product.ensures_bind
      (Q := fun hook _ => Roaming.Product.ResponseCallFacts msg cut ∧ DataDoneTraversalFacts cut.consumed.input.pid hook ∧
        TraversalAllModeEffect cut.consumed.input.pid hook.before.toSnapshot hook.after.toSnapshot)
      _ _ (fun initial hook final h run =>
        ⟨h cut rfl, observedReceiveTraversalCommon_all_modes msg cut.consumed.input.pid initial hook final trivial run⟩) ?_
    intro hook initial out final facts run other same
    cases run
    cases same
    exact ⟨⟨facts.1, facts.2.1⟩, facts.2.2⟩



end Leanux.Proofs.WG.TimerDiscipline
