import Leanux.Proofs.WG.Index.AllocationModel
import Leanux.Proofs.WG.Index.PeerWords
import Leanux.Proofs.WG.Noise.CryptoFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem keypairCreate_exact (peer : Option PeerId) (d : Device) (counter : Nat) :
    Ensures (keypairCreate peer) (fun w => w.dev = some d ∧ w.keypairCounter = counter)
      (fun result w => match result with
        | none => w.dev = some d ∧ w.keypairCounter = counter
        | some id => id = d.nextKeypairId ∧
          w.dev = some (createdDevice d counter peer) ∧ w.keypairCounter = counter + 1) := by
  unfold keypairCreate
  refine ensures_bind (Q := fun _ w => w.dev = some d ∧ w.keypairCounter = counter) _ _ ?_ ?_
  · exact (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.hiddenAlloc .kzallocKeypair)
        (fun w : WGWorld => w.dev = some d ∧ w.keypairCounter = counter))
  · intro allocated g ambient result final after pre run
    rcases pre with ⟨device, counted⟩
    cases allocated <;>
      simp [branch, AmbientM.branch, getDev, setKeypair, modifyDev,
        device, counted] at run
    all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    · exact ⟨device, counted⟩
    · simp [createdDevice]

end Leanux.Proofs.WG.Index
