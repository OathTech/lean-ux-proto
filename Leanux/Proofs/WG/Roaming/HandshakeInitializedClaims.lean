import Leanux.Proofs.WG.Roaming.HandshakeInitializedSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux

/-- Every actual committed handshake attempt is authenticated, even on a
prefix before the original initialized runner returns an indexed Stop. -/
theorem initialized_authentication (trace : Runner.Trace) (placeholders : Bool) :
    ∀ q ∈ (initializedInspection trace placeholders).attempts, Authenticated q.attempt :=
  fun q member => initialized_occurrence_authenticated trace placeholders q
    ((initialized_occurs_iff trace placeholders q).mp member)

/-- Exactly the emitted occurrences of the concrete initialized observer,
with no supplied callback, invariant or completion premise. -/
theorem initialized_coverage (trace : Runner.Trace) (placeholders : Bool) :
    (initializedInspection trace placeholders).outcome = Runner.executeTrace trace placeholders ∧
    ∀ q, q ∈ (initializedInspection trace placeholders).attempts ↔ q.Occurs trace placeholders :=
  ⟨initialized_original trace placeholders,initialized_occurs_iff trace placeholders⟩

end Leanux.Proofs.WG.Roaming.HandshakeOverlay
