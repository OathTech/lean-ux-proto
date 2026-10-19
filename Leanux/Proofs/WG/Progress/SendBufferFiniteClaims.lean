import Leanux.Proofs.WG.Progress.SendBufferFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- Exact finite evaluation of the complete buffer sender on every input and
allocation mode. Original errors and endpoint/routing effects are retained;
this is not a successful-transmission or practical cost claim. -/
theorem original_sendBuffer_finite (pid : PeerId) (bytes : List UInt8) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendBufferToPeer pid bytes) (sendBuffer pid bytes) := by
  rw [sendBuffer_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.HandshakeFinite
