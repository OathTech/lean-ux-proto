import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ReceiveStepRemote
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Noise Lifetimes Queues Std.Do

theorem dequeue_remotes (w : World) (ring : PtrRing (List UInt8 × SkbSource)) :
    remoteMap (Campaign2.Product.snapshot (dequeued w ring)).toSnapshot =
      remoteMap (Campaign2.Product.snapshot w).toSnapshot := by
  change destinationAt (Noise.ReceiveStepCaller.dequeueWorld w.wg ring) = destinationAt w.wg
  funext pid
  cases device : w.wg.dev <;>
    simp [destinationAt,peerAt,Noise.ReceiveStepCaller.dequeueWorld,device]

theorem decrement_remotes (w : World) :
    remoteMap (Campaign2.Product.snapshot (decremented w)).toSnapshot =
      remoteMap (Campaign2.Product.snapshot w).toSnapshot := by
  change destinationAt (Noise.ReceiveStepCaller.decrementWorld w.wg) = destinationAt w.wg
  funext pid
  cases device : w.wg.dev <;>
    simp [destinationAt,peerAt,Noise.ReceiveStepCaller.decrementWorld,device]

end Leanux.Proofs.WG.Roaming.ReceiveStepRemote
