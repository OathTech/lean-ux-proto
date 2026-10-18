import Leanux.Proofs.WG.Roaming.RemoteSessionClaims
import Leanux.Proofs.WG.Roaming.ResponseCallProductClaims
import Leanux.Proofs.WG.Roaming.InitiationCallProductClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Framing TimerDiscipline Std.Do

def ResponseFinalRemotes (entry : Campaign2.Snapshot) (src : SkbSource)
    (observed : Campaign2.Outcome (Option ResponseCallCut)) (final : Campaign2.Snapshot) : Prop :=
  ∃ candidate atCut, observed = .ok (candidate,atCut) ∧
    remoteMap atCut = remoteMap entry ∧
    (match candidate with
      | none => remoteMap final = remoteMap entry
      | some cut => RemoteRetained (updateRemote (remoteMap entry) cut.consumed.input.pid
          (destination (sourceEndpoint src))) (remoteMap final))

def InitiationFinalRemotes (entry : Campaign2.Snapshot) (src : SkbSource)
    (observed : Campaign2.Outcome (Option InitiationCallCut)) (final : Campaign2.Snapshot) : Prop :=
  ∃ candidate atCut, observed = .ok (candidate,atCut) ∧
    remoteMap atCut = remoteMap entry ∧
    (match candidate with
      | none => remoteMap final = remoteMap entry
      | some cut => RemoteRetained (updateRemote (remoteMap entry) cut.consumed.pid
          (destination (sourceEndpoint src))) (remoteMap final))

namespace Product

def ResponseFinalRemotes (entry : Campaign2.Product.Snapshot) (src : SkbSource)
    (observed : Campaign2.Product.Outcome (Option ResponseCallCut))
    (final : Campaign2.Product.Snapshot) : Prop :=
  ∃ candidate atCut, observed = .ok (candidate,atCut) ∧
    remoteMap atCut.toSnapshot = remoteMap entry.toSnapshot ∧
    (match candidate with
      | none => remoteMap final.toSnapshot = remoteMap entry.toSnapshot
      | some cut => RemoteRetained (updateRemote (remoteMap entry.toSnapshot)
          cut.consumed.input.pid (destination (sourceEndpoint src)))
          (remoteMap final.toSnapshot))

def InitiationFinalRemotes (entry : Campaign2.Product.Snapshot) (src : SkbSource)
    (observed : Campaign2.Product.Outcome (Option InitiationCallCut))
    (final : Campaign2.Product.Snapshot) : Prop :=
  ∃ candidate atCut, observed = .ok (candidate,atCut) ∧
    remoteMap atCut.toSnapshot = remoteMap entry.toSnapshot ∧
    (match candidate with
      | none => remoteMap final.toSnapshot = remoteMap entry.toSnapshot
      | some cut => RemoteRetained (updateRemote (remoteMap entry.toSnapshot)
          cut.consumed.pid (destination (sourceEndpoint src)))
          (remoteMap final.toSnapshot))

inductive HandshakeRemoteReceipt where
  | initiation : Campaign2.Product.Outcome (Option InitiationCallCut) → HandshakeRemoteReceipt
  | response : Campaign2.Product.Outcome (Option ResponseCallCut) → HandshakeRemoteReceipt
  | other : HandshakeRemoteReceipt

def HandshakeFinalRemotes (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Product.Snapshot) (receipt : HandshakeRemoteReceipt)
    (final : Campaign2.Product.Snapshot) : Prop :=
  match receipt with
  | .initiation observed =>
    messageType msg = MESSAGE_HANDSHAKE_INITIATION ∧
    InitiationCallObservation msg observed ∧ InitiationFinalRemotes entry src observed final
  | .response observed =>
    messageType msg = MESSAGE_HANDSHAKE_RESPONSE ∧
    ResponseCallObservation msg observed ∧ ResponseFinalRemotes entry src observed final
  | .other =>
    messageType msg ≠ MESSAGE_HANDSHAKE_INITIATION ∧
    messageType msg ≠ MESSAGE_HANDSHAKE_RESPONSE ∧
    remoteMap final.toSnapshot = remoteMap entry.toSnapshot


end Product

end Leanux.Proofs.WG.Roaming
