import Leanux.Proofs.WG.Roaming.PollAuthenticationQuietBridge
import Leanux.Proofs.WG.Packets.PublicationOuter

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes
variable {α : Type}

theorem reached_store (h : List RxHistory.Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : Reached h w) : Reached h v :=
  ⟨PublicationJoint.store h w v same hi.1,hi.2⟩

theorem reached_wgStore (h : List RxHistory.Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : Reached h w) : Reached h v :=
  ⟨PublicationOuter.store h w v same hi.1,hi.2⟩

end Leanux.Proofs.WG.Roaming.PollAuthentication
