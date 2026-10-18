import Leanux.Proofs.WG.Roaming.HandshakeRemoteModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ReceiveStepRemote
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Noise Lifetimes Queues Std.Do

structure Call where
  message : List UInt8
  source : SkbSource
  entry : Campaign2.Product.Snapshot
  finish : Campaign2.Product.Snapshot
  receipt : Product.HandshakeRemoteReceipt

structure Observation where
  entry : Campaign2.Product.Snapshot
  finish : Campaign2.Product.Snapshot
  value : Bool
  call : Option Call

def Observation.Facts (q : Observation) : Prop :=
  ∃ d, q.entry.wg.device = some d ∧
    match q.call with
    | none =>
      q.value = false ∧ d.handshakeQueue.consume.1 = none ∧
      remoteMap q.finish.toSnapshot = remoteMap q.entry.toSnapshot
    | some call =>
      q.value = true ∧ d.handshakeQueue.consume.1 = some (call.message,call.source) ∧
      remoteMap call.entry.toSnapshot = remoteMap q.entry.toSnapshot ∧
      remoteMap q.finish.toSnapshot = remoteMap call.finish.toSnapshot ∧
      Product.HandshakeFinalRemotes call.message call.source call.entry call.receipt call.finish

def Call.Authenticated (call : Call) (pid : PeerId) (remote : Nat × Nat × Nat × Nat) : Prop :=
  match call.receipt with
  | .initiation observed =>
    messageType call.message = MESSAGE_HANDSHAKE_INITIATION ∧
    ∃ cut atCut, observed = .ok (some cut,atCut) ∧
      cut.beforeSetter = atCut ∧ Product.InitiationCallFacts call.message cut ∧
      pid = cut.consumed.pid ∧ remote = destination (sourceEndpoint call.source)
  | .response observed =>
    messageType call.message = MESSAGE_HANDSHAKE_RESPONSE ∧
    ∃ cut atCut, observed = .ok (some cut,atCut) ∧
      cut.beforeSetter = atCut ∧ Product.ResponseCallFacts call.message cut ∧
      pid = cut.consumed.input.pid ∧ remote = destination (sourceEndpoint call.source)
  | .other => False

def Observation.Cause (q : Observation) (pid : PeerId) (remote : Nat × Nat × Nat × Nat) : Prop :=
  ∃ call, q.call = some call ∧ call.Authenticated pid remote

end Leanux.Proofs.WG.Roaming.ReceiveStepRemote
