import Leanux.Proofs.WG.Progress.HandshakeFiniteSource
import Leanux.Proofs.WG.Roaming.InitiationConsumeErasureSource
import Leanux.Proofs.WG.Roaming.ResponseConsumeSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.ConsumerFinite
open Leanux Leanux.WG
open Roaming
/-- The existing consumer observer with its only nonstructural primitive
replaced by the exact finite DH helper. Successful decoration is erased. -/
def initiation (msg : List UInt8) : WG.M (Option PeerId) := do
  let out ← initiationConsumeWithDh HandshakeFinite.mixDh msg
  pure (initiationPeer out)

/-- The original response lookup/guard factor and its existing tail, using
finite evaluation for both DH calls. Rejection payment remains actual. -/
def response (msg : List UInt8) : WG.M (Option PeerId) := do
  let out ← responseConsumeWithTail
    (responseConsumeTailWithDh HandshakeFinite.mixDh) msg
  pure (responsePeer out)

theorem initiation_source (msg : List UInt8) :
    consumeInitiation msg = initiation msg := by
  have same : HandshakeFinite.mixDh = WG.mixDh :=
    funext fun key => funext fun ck => funext fun priv => funext fun pub =>
      (HandshakeFinite.mixDh_source key ck priv pub).symm
  unfold initiation
  rw [same, initiationConsumeWithDh_original]
  exact (initiationConsume_erase msg).symm

theorem response_source (msg : List UInt8) :
    consumeResponse msg = response msg := by
  have same : HandshakeFinite.mixDh = WG.mixDh :=
    funext fun key => funext fun ck => funext fun priv => funext fun pub =>
      (HandshakeFinite.mixDh_source key ck priv pub).symm
  unfold response
  rw [same]
  have tail : responseConsumeTailWithDh WG.mixDh = responseConsumeTail :=
    funext fun bytes => funext fun input => responseConsumeTailWithDh_original bytes input
  rw [tail, responseConsumeWithTail_original]
  exact (responseConsume_erase msg).symm
end Leanux.Proofs.WG.Progress.ConsumerFinite
