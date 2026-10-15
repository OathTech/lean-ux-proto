import Leanux.WG.Handshake

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

/-- The remote destination, excluding cached local source information and
IPv6 flowinfo, which endpoint_eq intentionally does not compare. -/
def destination (e : Endpoint) : Nat × Nat × Nat × Nat :=
  (e.family, e.addr, e.port, if e.family = AF_INET6 then e.scope else 0)

def sourceEndpoint (src : SkbSource) : Endpoint :=
  if src.family = 4 then
    { family := AF_INET, addr := src.saddr, port := src.sport, src := src.daddr, srcIf := src.iif }
  else
    { family := AF_INET6, addr := src.saddr, port := src.sport, src := src.daddr,
      scope := if src.saddr / 2 ^ 118 = 0x3fa then src.iif else 0 }


end Leanux.Proofs.WG.Roaming
