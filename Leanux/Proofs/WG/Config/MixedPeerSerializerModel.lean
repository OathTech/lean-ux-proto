import Leanux.Proofs.WG.Config.FactoredTailModel
import Leanux.Proofs.WG.Config.WeightedPaginationModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The actual allowed-IP suffix at arbitrary remaining room. Nest failure
retains sequence initialization but restores the original peer skb. -/
def weightedAllowedResult (d : Device) (nodes : NodeId → AipNode)
    (ctx : DumpCtx) (skb0 skb : NlSkb) (pubkey : String)
    (attrs : List (String × Json)) (ids : List NodeId) : PeerDumpResult :=
  match ids with
  | [] => (skb,{ctx with nextAllowedip := none,allowedipsSeq := 0},.complete {publicKey := pubkey,attrs})
  | _::_ =>
    if skb.room < 4 then (skb0,{ctx with allowedipsSeq := d.peerAllowedips.seq},.cancelled)
    else
      let result := weightedPrefix nodes (skb.room-4) ids
      let out := {skb with room := skb.room-(4+dumpNodesSpace nodes result.1)}
      let attrs := attrs ++ [("allowed_ips",Json.arr (dumpNodeJsons nodes result.1))]
      match result.2 with
      | [] => (out,{ctx with nextAllowedip := none,allowedipsSeq := 0},.complete {publicKey := pubkey,attrs})
      | next::_ => (out,{ctx with nextAllowedip := some next,allowedipsSeq := d.peerAllowedips.seq},
          .split {publicKey := pubkey,attrs,split := true})

/-- Endpoint reservation before the unchanged weighted allowed-IP suffix. -/
def weightedEndpointResult (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb) (ids : List NodeId) : PeerDumpResult :=
  let family := (p.endpoint.map (·.family)).getD 0
  let cost := if family = AF_INET then 20 else if family = AF_INET6 then 32 else 0
  if cost ≤ skb.room then
    weightedAllowedResult d nodes ctx skb0 {skb with room := skb.room-cost}
      (hexKey p.remoteStatic) (peerFixedAttrs p) ids
  else (skb0,ctx,.cancelled)

/-- Static serializer result. A resumed peer emits only its public-key prefix;
a fresh peer emits its fixed fields and actual endpoint before the AIP suffix. -/
def weightedPeerResult (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId) : PeerDumpResult :=
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  let attrs := if ctx.nextAllowedip.isNone then peerFixedAttrs p
    else [("public_key",toJson (hexKey p.remoteStatic))]
  if cost ≤ skb.room then
    weightedAllowedResult d nodes ctx skb {skb with room := skb.room-cost}
      (hexKey p.remoteStatic) attrs ids
  else (skb,ctx,.cancelled)


end Leanux.Proofs.WG.Config
