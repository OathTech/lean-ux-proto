import Leanux.WG.Data
import Leanux.Env.IpStack

/-! Access-free padding and checksum completion, framed over the complete
Kernel. The concrete checksum helper examines only its supplied packet value;
its rejected inputs retain the original Stops. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem calculateSkbPadding_sameKernel (len mtu : Nat) :
    SameKernel (calculateSkbPadding len mtu) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [calculateSkbPadding, branch]

theorem checksumHelp_sameKernel (pkt : Packet) :
    SameKernel (Leanux.Env.checksumHelp pkt) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Leanux.Env.checksumHelp, invariant, unsupported]

end Leanux.Proofs.Framing
