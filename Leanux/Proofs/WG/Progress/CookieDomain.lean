import Leanux.WG.Receive

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG

/-- Original logical-items domain, without a physical-slot coherence premise. -/
def CookieOnly (d : Device) : Prop :=
  ∀ msg src, (msg, src) ∈ d.handshakeQueue.items →
    messageType msg = MESSAGE_HANDSHAKE_COOKIE

end Leanux.Proofs.WG.Progress
