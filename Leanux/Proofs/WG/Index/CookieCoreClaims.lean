import Leanux.Proofs.WG.Index.CookieCoreFrames
import Leanux.Proofs.WG.Index.CookieHeldSource
import Leanux.Proofs.WG.Index.LookupRetirementClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem cookieMessageConsume_indexCore (msg : List UInt8) :
    Campaign2.Ensures (cookieMessageConsume msg) View.IndexCore (fun _ => View.IndexCore) := by
  change Ensures (cookieMessageConsume msg) Reached.Core (fun _ => Reached.Core)
  apply cookieMessageConsume_preserves_held_source msg _ IncomingCoreHeld
  · exact indexLookup_indexCore_held [.handshake,.keypair] (u32le msg 4)
  · intro pid bytes birthdate
    exact modifyPeer_indexCoreHeld pid _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  · exact peerPut_indexCore_held


end Leanux.Proofs.WG.Index
