import Leanux.Proofs.WG.Roaming.HandshakeAuditSource
import Leanux.Proofs.WG.Roaming.InitiationCallClaims
import Leanux.Proofs.WG.Roaming.ResponseAuditClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

def initiationHandshakeAudit (msg : List UInt8) (src : SkbSource) :=
  handshakeAudit (initiationCallPrefix msg src) (initiationCallSuffix msg src)

theorem initiationHandshakeAudit_original (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (do let audited ← initiationHandshakeAudit msg src; pure audited.2) =
      Campaign2.inspect (receiveHandshakePacket msg src) := by
  rw [initiationHandshakeAudit, handshakeAudit_complete,
    receiveHandshakePacket_initiation msg src kind]

theorem initiationHandshakeAudit_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Observes (initiationHandshakeAudit msg src) (fun _ => True)
      (fun entry observed => ∃ audited, observed = .ok (audited, entry) ∧
        HandshakeAuditFacts
          (fun cut atCut => cut.beforeSetter = atCut ∧ InitiationCallFacts msg cut) audited) :=
  handshakeAudit_observes _ _ _ rfl (initiationCallPrefix_facts msg src)

end Leanux.Proofs.WG.Roaming
