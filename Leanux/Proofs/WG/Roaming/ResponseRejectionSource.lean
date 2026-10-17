import Leanux.Proofs.WG.Roaming.ResponseRejectionModel
import Leanux.Proofs.WG.Roaming.RateLimitSource
import Leanux.Proofs.WG.Roaming.ResponseCallProductSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- Both inspectors run on the same entry, and neither changes it. -/
def responseRejectionInspect (msg : List UInt8) (src : SkbSource) :
    Leanux.M (Campaign2.Product.Outcome (Bool × MacState) ×
      Campaign2.Product.Outcome (Option Product.ResponseCallCut)) := do
  let admission ← Campaign2.Product.inspect (liftWG (rateLimitPrefix msg src))
  let consumer ← Campaign2.Product.inspect (Product.responseCallPrefix msg src)
  return (admission,consumer)

def observedResponseRejection (msg : List UInt8) (src : SkbSource) :
    Leanux.M (Campaign2.Product.Outcome (Bool × MacState) ×
      Campaign2.Product.Outcome (Option Product.ResponseCallCut)) := do
  let receipt ← responseRejectionInspect msg src
  liftWG (receiveHandshakePacket msg src)
  return receipt

/-- Erasing both inspections retains all original normal results and Stops. -/
theorem observedResponseRejection_erase (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observedResponseRejection msg src; pure ()) =
      liftWG (receiveHandshakePacket msg src) := by
  funext w
  change (((liftWG (receiveHandshakePacket msg src)).run w >>= fun out =>
    Except.ok ((Campaign2.Product.observeResult ((liftWG (rateLimitPrefix msg src)).run w),
      Campaign2.Product.observeResult ((Product.responseCallPrefix msg src).run w)),out.2)) >>=
        fun out => Except.ok ((),out.2)) = (liftWG (receiveHandshakePacket msg src)).run w
  cases run : (liftWG (receiveHandshakePacket msg src)).run w with
  | error stop => rfl
  | ok pair => obtain ⟨value,final⟩ := pair; cases value; rfl

end Leanux.Proofs.WG.Roaming
