import Leanux.Proofs.WG.Roaming.HandshakeAuditSource
import Leanux.Proofs.WG.Roaming.ResponseCallProductClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

def responseHandshakeAudit (msg : List UInt8) (src : SkbSource) :=
  handshakeAudit (responseCallPrefix msg src) (responseCallSuffix msg src)

theorem responseHandshakeAudit_original (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (do let audited ← responseHandshakeAudit msg src; pure audited.2) =
      Campaign2.inspect (receiveHandshakePacket msg src) := by
  rw [responseHandshakeAudit, handshakeAudit_complete,
    receiveHandshakePacket_response msg src kind]

theorem responseHandshakeAudit_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Observes (responseHandshakeAudit msg src) (fun _ => True)
      (fun entry observed => ∃ audited, observed = .ok (audited, entry) ∧
        HandshakeAuditFacts
          (fun cut atCut => cut.beforeSetter = atCut ∧ ResponseCallFacts msg cut) audited) :=
  handshakeAudit_observes _ _ _ rfl (responseCallPrefix_facts msg src)

namespace Product

def responseHandshakeAudit (msg : List UInt8) (src : SkbSource) :=
  handshakeAudit (responseCallPrefix msg src) (responseCallSuffix msg src)

theorem responseHandshakeAudit_original (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (do let audited ← responseHandshakeAudit msg src; pure audited.2) =
      Campaign2.Product.inspect (liftWG (receiveHandshakePacket msg src)) := by
  rw [responseHandshakeAudit, handshakeAudit_complete,
    receiveHandshakePacket_response msg src kind]

theorem responseHandshakeAudit_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Product.Observes (responseHandshakeAudit msg src) (fun _ => True)
      (fun entry observed => ∃ audited, observed = .ok (audited, entry) ∧
        HandshakeAuditFacts
          (fun cut atCut => cut.beforeSetter = atCut ∧ ResponseCallFacts msg cut) audited) :=
  handshakeAudit_observes _ _ _ rfl (responseCallPrefix_facts msg src)

end Product
end Leanux.Proofs.WG.Roaming
