import Leanux.Proofs.WG.Index.OwnerCoherenceAllocationFrames
import Leanux.Proofs.WG.Index.Allocation
import Leanux.Proofs.WG.Index.LifecycleModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Native allocation preserves the joint optional-device table and hashed-owner
invariants. The fresh object is not yet hashed, so its supplied peer word may be
NULL or arbitrary. Completion and eventual publication are not asserted. -/
theorem keypairCreate_coherent_tables (peer : Option PeerId) :
    Campaign2.Ensures (keypairCreate peer)
      (fun s => View.TablesSafe s ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.TablesSafe s ∧ View.OwnerCoherentSafe s) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    have absent : Ensures (keypairCreate peer) (fun g => g.dev = none)
        (fun _ g => g.dev = none) := by
      unfold keypairCreate
      have allocation : Ensures (hiddenAlloc .kzallocKeypair : WG.M Bool)
          (fun g => g.dev = none) (fun _ g => g.dev = none) :=
        (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
          (AmbientM.hiddenAlloc .kzallocKeypair) (fun g : WGWorld => g.dev = none))
      refine ensures_bind (Q := fun _ (g : WGWorld) => g.dev = none) _ _ allocation ?_
      intro allocated state inputs value finish output initial executed
      cases allocated <;>
        simp [branch, AmbientM.branch, getDev, initial,
          invariant, AmbientM.invariant] at executed
      · rcases executed with ⟨⟨rfl, rfl⟩, rfl⟩
        exact initial
      · cases executed
    have none := absent g ambient result final after device run
    constructor <;> intro d present <;> change final.dev = some d at present <;> simp [none] at present
  | some d =>
    have safe := pre.1 d device
    have coherent := pre.2 d device
    have effect := keypairCreate_exact peer d g.keypairCounter
      g ambient result final after ⟨device, rfl⟩ run
    have output : ∃ out, final.dev = some out ∧
        DeviceTablesSafe out ∧ HashedOwnersCoherent out := by
      cases result with
      | none => exact ⟨d, effect.1, safe, coherent⟩
      | some id =>
        exact ⟨createdDevice d g.keypairCounter peer, effect.2.1,
          ⟨safe.1, safe.2.1, created_bounded d g.keypairCounter peer safe.2.2⟩,
          created_owner_coherent d g.keypairCounter peer safe.2.2 coherent⟩
    obtain ⟨out, stored, safe, coherent⟩ := output
    constructor
    · intro d present
      change final.dev = some d at present
      rw [stored] at present
      cases present
      exact safe
    · intro d present
      change final.dev = some d at present
      rw [stored] at present
      cases present
      exact coherent

end Leanux.Proofs.WG.Index
