import Leanux.Proofs.WG.HandshakeSecurity.Projection

/-! Local campaign-2 contracts over original native runs. Their inhabitants are
constructed from landed H1 in LandedH1Exchange; this definition module keeps
that import separate. These are native effects, not cipher assumptions. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG

def handshakeTagAt (w : WGWorld) (pid : PeerId) : Option Nat :=
  (w.dev.bind fun d => d.peers[pid]?).map (·.handshakeState)

/-- Native projection required from H1's
`Noise.consumeResponse_tagMap_projected`: successful consumption requires a
created initiation and changes only that peer's tag to consumed response;
normal refusal preserves the complete optional tag map. The native
contract is constructed by `LandedH1.consumeResponse` from landed campaign 2. -/
def H1ResponseEdges : Prop :=
  ∀ (msg : List UInt8) (w v : WGWorld) (a b : Ambient) (result : Option PeerId),
    ((consumeResponse msg).run w).run a = .ok ((result, v), b) →
      (∀ pid, result = some pid → handshakeTagAt w pid = some HANDSHAKE_CREATED_INITIATION) ∧
      (∀ pid, handshakeTagAt v pid = if result = some pid then
        some HANDSHAKE_CONSUMED_RESPONSE else handshakeTagAt w pid)

/-- Native projections required from H1's `original_begin_session_tag_map`
and `original_begin_session_ordered`: a normally completed session clears its
accepted response tag and increments the key allocation counter once; a
normal false return preserves both. Slot coherence and allocation-ID freshness
are deliberately not smuggled into this source-effect contract. -/
def H1SessionEffects : Prop :=
  ∀ (pid : PeerId) (w v : WGWorld) (a b : Ambient) (result : Bool),
    ((beginSession pid).run w).run a = .ok ((result, v), b) →
      (result = true →
        (handshakeTagAt w pid = some HANDSHAKE_CREATED_RESPONSE ∨
          handshakeTagAt w pid = some HANDSHAKE_CONSUMED_RESPONSE)) ∧
      (∀ target, handshakeTagAt v target = if result = true ∧ target = pid then
        some HANDSHAKE_ZEROED else handshakeTagAt w target) ∧
      v.keypairCounter = w.keypairCounter + (if result then 1 else 0)

end Leanux.Proofs.WG.HandshakeSecurity
