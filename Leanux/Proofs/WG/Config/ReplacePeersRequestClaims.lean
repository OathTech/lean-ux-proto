import Leanux.Proofs.WG.Config.ReplacePeersRequestSource
import Leanux.Proofs.WG.Config.DeviceScalars
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem observedReplacePeers_facts (selector : DeviceRef) :
    Campaign2.Ensures (observedReplacePeers selector) (fun _ => True)
      (fun result _ => ∀ cut, result.1 = some cut → result.2 = 0 ∧ RemoveAllFacts cut) := by
  have trivial_call {α : Type} (a : M α) :
      ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry ret final pre run
    trivial
  have hl := trivial_call (lookupInterface selector)
  have hg := trivial_call (modifyDev fun d => { d with deviceUpdateGen := d.deviceUpdateGen + 1 })
  have hm := (ensures_iff _ _ _).mp (show Ensures observedRemoveAll (fun _ => True)
    (fun cut _ => RemoveAllFacts cut) from observedRemoveAll_facts)
  change Ensures _ _ _
  rw [ensures_iff]
  mvcgen [observedReplacePeers, replacePeersWith, branch, invariant, hl, hg, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

/-- Successful selection ensures that every normal full return exposes the
actual removal cut; it does not assert that cleanup returns. -/
theorem observedReplacePeers_selected (d : Device) :
    Campaign2.Ensures (observedReplacePeers (byIndex d))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d)
      (fun result _ => ∃ cut, result = (some cut, 0) ∧ RemoveAllFacts cut) := by
  have trivial_call {α : Type} (a : M α) :
      ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry ret final pre run
    trivial
  have hl := lookupInterface_index d
  have hg := trivial_call (modifyDev fun d => { d with deviceUpdateGen := d.deviceUpdateGen + 1 })
  have hm := (ensures_iff _ _ _).mp (show Ensures observedRemoveAll (fun _ => True)
    (fun cut _ => RemoveAllFacts cut) from observedRemoveAll_facts)
  change Ensures _ (fun w => w.k.wg = some d ∧ selectsDevice w d) _
  rw [ensures_iff]
  mvcgen [observedReplacePeers, replacePeersWith, branch, invariant, hl, hg, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.WG.Config
