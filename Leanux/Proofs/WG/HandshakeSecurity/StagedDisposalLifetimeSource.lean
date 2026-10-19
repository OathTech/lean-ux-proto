import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalPeerFocus
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsMatching

/-! Completion rekey maintenance retains its original lifetime accesses and
records the counted peer release before its retirement suffix can stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.LifetimeSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues AuthenticatedEffects TransmitSecurity

def peerEncode (encode : Completion.Event → E) : Peers.PeerEvent → E :=
  encode ∘ CompletionEffects.lifetimeEvent ∘ LifetimeEvent.peer

def peerDecode (decode : E → Option Completion.Event) (event : E) : Option Peers.PeerEvent :=
  ((decode event).bind CompletionEffects.lifetime?).bind LifetimeEvent.peer?

def putObserved (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (record : Event → E) (peer : Option PeerId) : WGPrefix E Unit :=
  PeerSource.observed
    (PeerSource.Ops.focus (peerEncode encode) (peerDecode decode) PeerSource.peers) record peer

def decorate (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (scope : E → Option (CausalScope.Event Cause))
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (record : Event → E) : LifetimeEffects.Ops (WGPrefix E) :=
  {LifetimeEffects.decorate (CompletionEffects.lifetimeBase encode decode) scope arm queue with
    put := putObserved encode decode record}

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.LifetimeSource
