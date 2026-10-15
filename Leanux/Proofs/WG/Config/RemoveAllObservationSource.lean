import Leanux.Proofs.WG.Config.RemoveAllSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def observedRemoveAllMark (d : Device) : M Campaign2.Snapshot := do
  removeAllMark d.peerList
  Campaign2.read

def observedRemoveAll : M RemoveAllCall := do
  free
  let d ← getDev
  let afterMark ← observedRemoveAllMark d
  removeAllCleanup d.peerList
  return ⟨d, afterMark⟩

theorem observedRemoveAll_erase :
    (do let _ ← observedRemoveAll; pure ()) = peerRemoveAll := by
  have read_drop {α : Type} (a : M α) : (do let _ ← Campaign2.read; a) = a := rfl
  have unit_drop (a : M Unit) : (do a; pure ()) = a := by
    funext entry
    change (a.run entry >>= fun out => Except.ok ((), out.2)) = a.run entry
    cases h : a.run entry with
    | error err => rfl
    | ok pair => rcases pair with ⟨u, final⟩; cases u; rfl
  rw [peerRemoveAll_phases]
  simp only [observedRemoveAll, observedRemoveAllMark, bind_assoc, pure_bind, read_drop, unit_drop]

theorem observedRemoveAllMark_facts (d : Device) :
    Ensures (observedRemoveAllMark d) (fun w => w.k.wg = some d)
      (fun after _ => RemoveAllFacts ⟨d, after⟩) := by
  intro entry after final pre run pairs listed
  change ((removeAllMark d.peerList).run entry >>= fun out =>
    Except.ok (Campaign2.snapshot out.2, out.2)) = .ok (after, final) at run
  cases hm : (removeAllMark d.peerList).run entry with
  | error err => rw [hm] at run; cases run
  | ok pair =>
    rcases pair with ⟨u, markedWorld⟩
    rw [hm] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    obtain ⟨marked, device, effect⟩ := removeAllMark_effect d.peerList d pairs listed
      entry u markedWorld pre hm
    exact ⟨marked, device, effect, deadPass_all_selected effect listed⟩

theorem observedRemoveAll_facts :
    Campaign2.Ensures observedRemoveAll (fun _ => True) (fun cut _ => RemoveAllFacts cut) := by
  have trivial_call {α : Type} (a : M α) :
      ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry ret final pre run
    trivial
  have hf := trivial_call free
  have hc := fun ids => trivial_call (removeAllCleanup ids)
  have hm := fun d => (ensures_iff _ _ _).mp (observedRemoveAllMark_facts d)
  change Ensures _ _ _
  rw [ensures_iff]
  mvcgen [observedRemoveAll, getDev, getK, invariant, hf, hm, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.WG.Config
