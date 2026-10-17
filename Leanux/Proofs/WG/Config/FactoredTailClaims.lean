import Leanux.Proofs.WG.Config.FactoredTailReturns
import Leanux.Proofs.WG.Config.MultipartLeaves
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- A resident peer with a fresh allowed-IP cursor and no stored entries returns
its exact full or cancelled serializer result for every room and ambient input. -/
theorem getPeerDump_fixed_room (pid : PeerId) (d : Device) (p : Peer)
    (ctx : DumpCtx) (skb : NlSkb) (resident : d.peers[pid]? = some p)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = []) :
    Campaign2.Returns (getPeerDump pid ctx skb) (fun s => s.wg.device = some d)
      (fun result s => s.wg.device = some d ∧ result = fixedPeerResult p ctx skb) := by
  exact multipart_getter_returns pid d p ctx skb (fixedPeerResult p ctx skb) resident
    (dumpTail_fixed_room p ctx skb fresh empty (fun g => g.dev = some d))

end Leanux.Proofs.WG.Config
