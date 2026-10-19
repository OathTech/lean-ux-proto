import Leanux.Proofs.WG.Roaming.InitiationModel
import Leanux.Proofs.WG.Roaming.Model
import Leanux.Proofs.WG.Roaming.ResponseModel
import Leanux.Proofs.WG.Campaign2.ProductView

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG

structure Attempt where
  message : List UInt8
  source : SkbSource
  peer : PeerId
  endpoint : Endpoint
  atSetter : Campaign2.Snapshot
def Authenticated (r : Attempt) : Prop :=
  r.endpoint = sourceEndpoint r.source ∧
  (r.source.family = 4 ∨ r.source.family = 6) ∧
  ((messageType r.message = MESSAGE_HANDSHAKE_INITIATION ∧
      ∃ cut, InitiationCallFacts r.message cut ∧ r.peer = cut.consumed.pid ∧
        r.atSetter.wg.device = cut.beforeSetter.wg.device) ∨
   (messageType r.message = MESSAGE_HANDSHAKE_RESPONSE ∧
      ∃ cut, ResponseCallFacts r.message cut ∧ r.peer = cut.consumed.input.pid ∧
        r.atSetter.wg.device = cut.beforeSetter.wg.device))

/-- Exact original outcome and the authenticated setter attempts reached on
that execution, including attempts before a later Stop. -/
structure Inspection (α : Type) where
  outcome : Campaign2.Product.Outcome α
  attempts : List Attempt

end Leanux.Proofs.WG.Roaming.HandshakeOverlay
