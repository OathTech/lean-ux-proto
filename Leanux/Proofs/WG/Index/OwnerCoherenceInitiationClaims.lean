import Leanux.Proofs.WG.Index.IncomingConsumeSource
import Leanux.Proofs.WG.Index.OwnerCoherencePubkeyFrames
import Leanux.Proofs.WG.Roaming.InitiationConsumeErasureSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- All normal initiation-consumption returns preserve hashed-owner coherence.
The actual public-key lookup supplies the extra reference used by every
post-lookup rejection; no successful-prefix or hidden-input premise is needed. -/
theorem consumeInitiation_owner_coherent (msg : List UInt8) :
    Campaign2.Ensures (consumeInitiation msg) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) :=
  consumeInitiation_preserves_held_source msg
    (fun g => ∀d, g.dev = some d → HashedOwnersCoherent d) OwnerPeerHeldWG
    (fun _ _ h => h.1) pubkeyLookup_owner_held peerPut_ownerHeld
    (fun pid f word count _ _ _ => modifyPeer_ownerHeld pid pid f word count)

end Leanux.Proofs.WG.Index
