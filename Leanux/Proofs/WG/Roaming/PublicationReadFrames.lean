import Leanux.Proofs.WG.Roaming.PublicationModel
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Noise.Execution

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Internal source/frame contract: the original getter preserves the entire
actual product state, including components outside the publication snapshot.
The entry type is inferred from the actual liftWG action. This is stronger
support than snapshot preservation and is not a projected public claim. -/
theorem getRxSkb_read (id : SkbId) : ∀ entry,
    Noise.Product.Ensures (liftWG (getRxSkb id)) (fun w => w = entry)
      (fun p w => w = entry ∧ packetAt (Campaign2.Product.snapshot entry) id = some p) := by
  intro entry w result final pre run
  subst w
  change (((getRxSkb id).run entry.wg).run entry.ambient >>= fun ((value, g), ambient) =>
    Except.ok (value, {entry with wg := g, ambient})) = _ at run
  cases hd : entry.wg.dev with
  | none =>
    simp [getRxSkb, liftSkb, getDev, hd, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases hp : d.rxSkbs[id]? with
    | none =>
      simp [getRxSkb, liftSkb, getDev, hd, SkbStore.getRx, hp, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      simp [getRxSkb, liftSkb, getDev, hd, SkbStore.getRx, hp, modifyDev] at run
      rcases run with ⟨rfl, rfl⟩
      have same : {entry.wg with dev := some d} = entry.wg := by rw [← hd]
      refine ⟨?_, by simpa [packetAt, Campaign2.Product.snapshot,
        Campaign2.snapshot, Campaign2.core, hd] using hp⟩
      change {entry with wg := {entry.wg with dev := some d}} = entry
      rw [same]

end Leanux.Proofs.WG.Roaming
