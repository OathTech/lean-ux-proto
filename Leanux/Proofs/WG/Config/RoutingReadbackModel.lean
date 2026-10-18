import Leanux.Proofs.WG.AllowedIps.InsertionRouting
import Leanux.Proofs.WG.Config.MixedPeerSerializerModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Data-only total lookup for serialization. Readability proves the fallback
is unused on the actual peer list; original getNode failures are not replaced. -/
def routingReadNode (d : Device) (id : NodeId) : AipNode :=
  (d.nodes[id]?).getD (newNode 0 0 32 none)

/-- Guard refusal or the exact represented insertion outcome. Normal ENOMEM
retains its sequence/frontier effects; this does not describe an aborted Stop. -/
def AllowedipRoutingEffect (d out : Device) (t4 t6 : AllowedIps.Tree)
    (pid : PeerId) (attrs : AllowedIpAttrs) (ret : Int) : Prop :=
  (ret = -EINVAL ∧ out = d) ∨
    ∃ v4 : Bool,
      attrs.family.getD 0 = (if v4 then AF_INET else AF_INET6) ∧
      attrs.addr.getD 0 < 2 ^ AllowedIps.rootWidth v4 ∧
      attrs.cidr.getD 0 ≤ AllowedIps.rootWidth v4 ∧
      AllowedIps.InsertRoutingOutcome d out v4 t4 t6
        (attrs.addr.getD 0) (attrs.cidr.getD 0) pid ret

/-- Normalized successful ownership transfer in the actual peer-list order. -/
def AllowedipMoved (d out : Device) (t4 t6 : AllowedIps.Tree)
    (pid : PeerId) (attrs : AllowedIpAttrs) : Prop :=
  ∃ v4 : Bool,
    attrs.family.getD 0 = (if v4 then AF_INET else AF_INET6) ∧
    let inserted := (AllowedIps.selectedTree v4 t4 t6).insertFresh
      (AllowedIps.rootWidth v4) d.nextNode (attrs.addr.getD 0) (attrs.cidr.getD 0) pid
    ∀ q : PeerId, out.peers[q]? =
      (d.peers[q]?).map (AllowedIps.insertionPeer 0 inserted.binding.id pid q)

/-- Actual setter followed by the actual single-peer serializer, including
normal negative setter returns, cancellation, splitting and all Stops. -/
def setAllowedipThenGetPeerDump (pid : PeerId) (attrs : AllowedIpAttrs)
    (ctx : DumpCtx) (skb : NlSkb) : WG.M (Int × PeerDumpResult) := do
  let ret ← setAllowedip pid attrs
  let dump ← getPeerDump pid ctx skb
  pure (ret, dump)

end Leanux.Proofs.WG.Config
