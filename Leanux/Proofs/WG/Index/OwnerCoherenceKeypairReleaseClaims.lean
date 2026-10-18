import Leanux.Proofs.WG.Index.OwnerCoherenceKeypairReleaseFrames
import Leanux.Proofs.WG.Index.KeypairReleaseSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Legacy owner-coherence contract, preserved unchanged, now sharing the
normal-outcome source certificate with hashed-slot coverage. -/
theorem keypairPut_owner_coherent (key : Option KeypairId) (now : Bool) :
    Campaign2.Ensures (keypairPut key now) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient result out after pre run
  rcases keypairPut_normal_effect key now g out ambient after result run with
    ⟨_,same⟩ | ⟨id,d,k,_,device,resident,live,present⟩
  · intro actual found
    change out.dev = some actual at found
    rw [same] at found
    exact pre actual found
  · intro actual found
    change out.dev = some actual at found
    rw [present] at found
    cases found
    exact releasedDevice_owner_coherent d id k now resident live (pre d device)

end Leanux.Proofs.WG.Index
