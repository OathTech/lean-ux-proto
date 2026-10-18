import Leanux.Proofs.WG.Noise.ReceptionCoverageClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ReceiveStepCaller

open Leanux Leanux.WG Leanux.Proofs.WG.Origins
open ReceptionCaller

def PollResult.receipts : PollResult → List TagReceipt
  | .empty => []
  | .consumed _ _ call => call.receipts

theorem dequeueWorld_tags (g : WGWorld) (ring : PtrRing (List UInt8 × SkbSource)) :
    responseTagMap (dequeueWorld g ring).dev = responseTagMap g.dev := by
  change responseTagMap (g.dev.map fun d => {d with handshakeQueue := ring}) =
    responseTagMap g.dev
  cases g.dev <;> rfl

theorem decrementWorld_tags (g : WGWorld) :
    responseTagMap (decrementWorld g).dev = responseTagMap g.dev := by
  change responseTagMap (g.dev.map fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1}) =
    responseTagMap g.dev
  cases g.dev <;> rfl

end Leanux.Proofs.WG.Noise.ReceiveStepCaller
