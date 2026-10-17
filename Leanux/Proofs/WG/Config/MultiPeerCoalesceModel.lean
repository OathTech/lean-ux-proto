import Leanux.Proofs.WG.Config.DumpCoalesce

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Preserve supplied peer attributes, adding exactly an empty allowed_ips
array only when that attribute is absent. Existing values are retained. -/
def peerDumpWithIps (p : PeerDumpAttrs) : PeerDumpAttrs :=
  {p with attrs := if p.attrs.any (·.1 == "allowed_ips") then p.attrs
    else p.attrs ++ [("allowed_ips",Json.arr #[])]}


end Leanux.Proofs.WG.Config
