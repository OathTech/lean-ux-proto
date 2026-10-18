import Leanux.Proofs.WG.Index.IncomingConsumeSource
import Leanux.Proofs.WG.Index.OwnerCoherenceHeldFrames
import Leanux.Proofs.WG.Index.OwnerCoherencePeerLookupClaims
import Leanux.Proofs.WG.Roaming.ResponseConsumeSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Every normal response-consumption return preserves hashed-owner coherence.
Actual lookup supplies the held reference for every rejected-response put;
there is no readiness, residency, reference-budget or successful-result premise. -/
theorem consumeResponse_owner_coherent (msg : List UInt8) :
    Campaign2.Ensures (consumeResponse msg) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  apply consumeResponse_preserves_held_source msg
    (fun g => ∀d, g.dev = some d → HashedOwnersCoherent d) OwnerPeerHeldWG
    (fun _ _ h => h.1) ?_ peerPut_ownerHeld
    (fun pid f word count _ _ _ => modifyPeer_ownerHeld pid pid f word count)
  intro index g a result out b pre run
  have post := indexLookup_peer_held [.handshake] index g a result out b pre run
  exact ⟨post.1,fun owner pid returned => ⟨post.1,post.2 owner pid returned⟩⟩

end Leanux.Proofs.WG.Index
