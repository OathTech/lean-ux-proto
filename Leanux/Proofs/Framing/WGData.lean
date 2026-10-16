import Leanux.Proofs.Framing.Tools
import Leanux.WG.Data
import Leanux.Env.IpStack

/-! Padding preserves its native WG world. The concrete checksum helper remains
an actual product action; it reads its packet argument and preserves that world
on normal return. Both retain the original rejected-input Stops. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem calculateSkbPadding_sameWGWorld (len mtu : Nat) :
    SameView (id : WGWorld → WGWorld) (calculateSkbPadding len mtu) := by
  apply SameView.of_wp
  intro initial
  mvcgen [calculateSkbPadding, branch, AmbientM.branch, branchCmp, AmbientM.branchCmp]

theorem checksumHelp_sameWorld (pkt : Packet) :
    SameView (id : World → World) (Leanux.Env.checksumHelp pkt) := by
  apply SameView.of_wp
  intro initial
  mvcgen [Leanux.Env.checksumHelp, invariant, AmbientM.invariant,
    unsupported, AmbientM.unsupported]
  all_goals
    intro s _
    change True
    trivial

end Leanux.Proofs.Framing
