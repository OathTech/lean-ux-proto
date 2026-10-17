import Leanux.Proofs.WG.Config.MultiPeerCoalesceModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Raw peer page data with one canonical allowed-IP array appended to the
supplied fixed attributes. This is not a producer or address-family model. -/
def coalesceAipPart (key : String) (fixed : List (String × Json))
    (ips : Array Json) (split : Bool) : PeerDumpAttrs :=
  {publicKey := key, attrs := fixed ++ [("allowed_ips",Json.arr ips)], split}

end Leanux.Proofs.WG.Config
