import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteModel
import Leanux.Proofs.WG.Roaming.HandshakeRemoteSource
import Leanux.Proofs.WG.Noise.ReceiveStepCoverageSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ReceiveStepRemote
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Noise Lifetimes Queues Std.Do

def dequeued (w : World) (ring : PtrRing (List UInt8 × SkbSource)) : World :=
  {w with
    wg := Noise.ReceiveStepCaller.dequeueWorld w.wg ring
    ambient := Noise.ReceiveStepCaller.pollAmbient w.ambient true}

def decremented (w : World) : World :=
  {w with wg := Noise.ReceiveStepCaller.decrementWorld w.wg}

def emptyReturn (w : World) : World :=
  {w with ambient := Noise.ReceiveStepCaller.pollAmbient w.ambient false}

def Matches (r : RunWitness Bool) (q : Observation) : Prop :=
  q.entry = Campaign2.Product.snapshot r.before ∧
  q.finish = Campaign2.Product.snapshot r.after ∧
  q.value = r.value ∧
  ∃ d ring, r.before.wg.dev = some d ∧
    match q.call with
    | none =>
      d.handshakeQueue.consume = (none,ring) ∧
      r.value = false ∧ r.after = emptyReturn r.before
    | some call =>
      d.handshakeQueue.consume = (some (call.message,call.source),ring) ∧
      r.value = true ∧
      ∃ callFinish,
        (Product.observedHandshakeRemotes call.message call.source).run (dequeued r.before ring) =
          .ok (call.receipt,callFinish) ∧
        call.entry = Campaign2.Product.snapshot (dequeued r.before ring) ∧
        call.finish = Campaign2.Product.snapshot callFinish ∧
        r.after = decremented callFinish

def Observation.Valid (q : Observation) : Prop :=
  ∃ r : RunWitness Bool, r.Valid (liftWG receiveStep) ∧ Matches r q

end Leanux.Proofs.WG.Roaming.ReceiveStepRemote
