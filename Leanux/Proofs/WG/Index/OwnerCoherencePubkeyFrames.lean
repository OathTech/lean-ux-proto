import Leanux.Proofs.WG.Index.IncomingConsumeSource
import Leanux.Proofs.WG.Index.OwnerCoherenceHeldFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Actual public-key lookup preserves hashed owners on misses and zero-count
returns, and supplies the held reference on every successful lookup. -/
theorem pubkeyLookup_owner_held (key : Key) :
    Ensures (pubkeyLookup key)
      (fun g => ∀d, g.dev = some d → HashedOwnersCoherent d)
      (fun result g => (∀d, g.dev = some d → HashedOwnersCoherent d) ∧
        ∀pid, result = some pid → OwnerPeerHeldWG pid g) := by
  intro g a result out b pre run
  have post := pubkeyLookup_preserves_acquire_source key HashedOwnersCoherent
    (fun d pid p resident coherent entry member =>
      ownerCoherent_acquire d pid p resident entry.owner (coherent entry member))
    g a result out b pre run
  exact ⟨post.1,fun pid returned => ⟨post.1,post.2 pid returned⟩⟩

end Leanux.Proofs.WG.Index
