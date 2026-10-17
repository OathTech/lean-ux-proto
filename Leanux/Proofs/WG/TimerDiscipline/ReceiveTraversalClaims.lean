import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalSource
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims
import Leanux.Proofs.WG.Roaming.InitiationCallProductClaims
import Leanux.Proofs.WG.Roaming.ResponseCallProductClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

theorem observedReceiveTraversalCommon_facts (msg : List UInt8) (pid : PeerId) :
    Noise.Product.Ensures (observedReceiveTraversalCommon msg pid) (fun _ => True)
      (fun hook _ => DataDoneTraversalFacts pid hook) := by
  unfold observedReceiveTraversalCommon
  refine Noise.Product.ensures_bind _ _ (fun _ _ _ h _ => h) ?_
  intro ignored
  refine Noise.Product.ensures_bind _ _ (dataDoneTraversal_facts pid) ?_
  intro hook
  refine Noise.Product.ensures_bind (Q := fun _ _ => DataDoneTraversalFacts pid hook) _ _
    (fun _ _ _ h _ => h) ?_
  intro ignored initial out final facts run
  cases run
  exact facts

theorem observedInitiationReceiveTraversal_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Product.Ensures (observedInitiationReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → InitiationReceiveTraversalFacts msg cut) := by
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
      (Q := fun hook _ => Roaming.Product.InitiationCallFacts msg cut ∧ DataDoneTraversalFacts cut.consumed.pid hook)
      _ _ (fun initial hook final h run =>
        ⟨h cut rfl, observedReceiveTraversalCommon_facts msg cut.consumed.pid initial hook final trivial run⟩) ?_
    intro hook initial out final facts run other same
    cases run
    cases same
    exact facts

theorem observedResponseReceiveTraversal_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Product.Ensures (observedResponseReceiveTraversal msg src) (fun _ => True)
      (fun result _ => ∀ cut, result = some cut → ResponseReceiveTraversalFacts msg cut) := by
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
      (Q := fun hook _ => Roaming.Product.ResponseCallFacts msg cut ∧ DataDoneTraversalFacts cut.consumed.input.pid hook)
      _ _ (fun initial hook final h run =>
        ⟨h cut rfl, observedReceiveTraversalCommon_facts msg cut.consumed.input.pid initial hook final trivial run⟩) ?_
    intro hook initial out final facts run other same
    cases run
    cases same
    exact facts



end Leanux.Proofs.WG.TimerDiscipline
