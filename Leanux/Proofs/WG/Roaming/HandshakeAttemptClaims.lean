import Leanux.Proofs.WG.Roaming.HandshakeAttemptBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeAttempts
open Leanux Leanux.WG

theorem initiation_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Observes (observeInitiation msg src) (fun _ => True)
      (fun entry result => ∃ audit, result = .ok (audit,entry) ∧
        ∀ attempt ∈ audit.attempts, InitiationFacts msg src attempt) :=
  inspect_facts _ _ (HandshakeAttemptAuth.initiation_valid msg src _ _
    (fun _ _ _ _ authenticated endpoint family => ⟨authenticated,endpoint,family⟩))

theorem initiation_original (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (do let audited ← observeInitiation msg src; pure audited.outcome) =
      Campaign2.inspect (receiveHandshakePacket msg src) :=
  inspect_original _ _ (HandshakeAttemptAuth.initiation_erases msg src kind _)

theorem response_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Observes (observeResponse msg src) (fun _ => True)
      (fun entry result => ∃ audit, result = .ok (audit,entry) ∧
        ∀ attempt ∈ audit.attempts, ResponseFacts msg src attempt) :=
  inspect_facts _ _ (HandshakeAttemptAuth.response_valid msg src _ _
    (fun _ _ _ _ authenticated endpoint family => ⟨authenticated,endpoint,family⟩))

theorem response_original (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (do let audited ← observeResponse msg src; pure audited.outcome) =
      Campaign2.inspect (receiveHandshakePacket msg src) :=
  inspect_original _ _ (HandshakeAttemptAuth.response_erases msg src kind _)

end Leanux.Proofs.WG.Roaming.HandshakeAttempts
