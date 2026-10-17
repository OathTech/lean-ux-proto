import Leanux.Proofs.WG.Config.MultipartModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Endpoint output includes the original behavior for every family. -/
def endpointDumpResult (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) : PeerDumpResult :=
  let family := (p.endpoint.map (·.family)).getD 0
  let cost := if family = AF_INET then 20 else if family = AF_INET6 then 32 else 0
  if cost ≤ skb.room then
    ({skb with room := skb.room-cost}, {ctx with nextAllowedip := none,allowedipsSeq := 0},
      .complete {publicKey := pubkey,attrs := attrs ++ match p.endpoint with
        | some e =>
          let v4 := e.family == AF_INET
          [("endpoint", Json.mkObj ([("family",toJson (if v4 then 4 else 6)),
            ("addr",toJson (hexBE e.addr (if v4 then 4 else 16))),("port",toJson e.port)] ++
            (if v4 then [] else [("flowinfo",toJson e.flowinfo),("scope_id",toJson e.scope)])))]
        | none => []})
  else (skb0,ctx,.cancelled)

def fixedPeerResult (p : Peer) (ctx : DumpCtx) (skb : NlSkb) : PeerDumpResult :=
  if peerFixedSpace p ≤ skb.room then
    ({skb with room := skb.room-peerFixedSpace p},
     {ctx with nextAllowedip := none,allowedipsSeq := 0},
     .complete {publicKey := hexKey p.remoteStatic,attrs := peerFixedAttrs p})
  else (skb,ctx,.cancelled)


end Leanux.Proofs.WG.Config
