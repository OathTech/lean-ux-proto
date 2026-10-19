import Leanux.Proofs.WG.Progress.ReceptionFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- Every original handshake reception has exactly its finite counterpart's
outcome, including early cookie handling and failures in later callbacks. -/
theorem original_reception_finite (msg : List UInt8) (src : SkbSource) :
    Campaign2.AgreesOn (fun _ => True) (WG.receiveHandshakePacket msg src) (reception msg src) := by
  rw [reception_source]
  intro g ambient pre
  rfl

/-- The complete native receive queue step agrees with its finite evaluation,
without assuming a nonempty ring, successful callback, or a supplied stream. -/
theorem original_receiveStep_finite :
    Campaign2.AgreesOn (fun _ => True) WG.receiveStep receiveStep := by
  rw [receiveStep_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.HandshakeFinite
