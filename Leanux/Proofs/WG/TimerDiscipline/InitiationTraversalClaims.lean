import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalSource
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

theorem observedInitiationTraversal_facts (pid : PeerId) :
    Campaign2.Product.Ensures (observedInitiationTraversal pid) (fun _ => True)
      (fun cut _ => InitiationTraversalFacts pid cut) := by
  have keep {α : Type} (action : Leanux.M α) (P : Prop) :
      Noise.Product.Ensures action (fun _ => P) (fun _ _ => P) := by
    intro initial result final pre run
    exact pre
  change Noise.Product.Ensures _ _ _
  unfold observedInitiationTraversal
  refine Noise.Product.ensures_bind _ _ (keep _ True) ?_
  intro message
  cases message with
  | none =>
    intro initial cut final pre run
    cases run
    exact ⟨rfl, by intro hook impossible; cases impossible⟩
  | some msg =>
    refine Noise.Product.ensures_bind _ _ (dataDoneTraversal_facts pid) ?_
    intro hook
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro ignored initial cut final facts run
    cases run
    exact ⟨rfl, by intro other same; cases same; exact facts⟩


end Leanux.Proofs.WG.TimerDiscipline
