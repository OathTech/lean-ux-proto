import Leanux.Proofs.WG.Index.CookieHeldSource
import Leanux.WG.Receive
import Leanux.Proofs.WG.Index.OwnerCoherencePeerLookupClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceHeldFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- The actual cookie-reply consumer preserves hashed-owner coherence. Its
lookup supplies the reference released on every normal exit; cookie writes
retain owner metadata. No crypto, clock or reference-readiness is assumed. -/
theorem cookieMessageConsume_owner_coherent (msg : List UInt8) :
    Campaign2.Ensures (cookieMessageConsume msg) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  change Ensures (cookieMessageConsume msg)
    (fun g => ∀ d,g.dev=some d → HashedOwnersCoherent d)
    (fun _ g => ∀ d,g.dev=some d → HashedOwnersCoherent d)
  apply cookieMessageConsume_preserves_held_source msg _ OwnerPeerHeldWG
  · intro g a result out b pre run
    have post := indexLookup_peer_held [.handshake,.keypair] (u32le msg 4) g a result out b pre run
    exact ⟨post.1,fun owner pid returned => ⟨post.1,post.2 owner pid returned⟩⟩
  · intro pid bytes birthdate
    exact modifyPeer_ownerHeld pid pid _ (fun _ => rfl) (fun _ => rfl)
  · exact peerPut_ownerHeld

end Leanux.Proofs.WG.Index
