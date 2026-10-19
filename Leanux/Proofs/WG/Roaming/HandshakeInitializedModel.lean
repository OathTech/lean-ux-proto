import Leanux.Proofs.WG.Roaming.HandshakeOverlayModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux

/-- Exact position of an authenticated setter attempt in the committed journal. -/
structure Occurrence where
  position : Nat
  attempt : Attempt

/-- Original initialized result and all projected committed handshake attempts. -/
structure InitializedInspection where
  outcome : Except (Nat × Stop) Lean.Json
  attempts : List Occurrence

end Leanux.Proofs.WG.Roaming.HandshakeOverlay
