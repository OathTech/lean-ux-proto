import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalSource
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Std.Do

theorem observedInitiationTraversal_facts (pid : PeerId) :
    Campaign2.Ensures (observedInitiationTraversal pid) (fun _ => True)
      (fun cut _ => InitiationTraversalFacts pid cut) := by
  have trivial_call {α : Type} (a : M α) :
      ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry ret final pre run
    trivial
  have hp := trivial_call (initiationTraversalPrelude pid)
  have ht := (ensures_iff _ _ _).mp (dataDoneTraversal_facts pid)
  have hs := fun msg => trivial_call (initiationTraversalFinish pid msg)
  change Noise.Ensures _ _ _
  rw [ensures_iff]
  mvcgen [observedInitiationTraversal, hp, ht, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [InitiationTraversalFacts]

end Leanux.Proofs.WG.TimerDiscipline
