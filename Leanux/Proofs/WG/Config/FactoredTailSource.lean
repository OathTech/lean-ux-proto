import Leanux.Proofs.WG.Config.FactoredTailModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- The fixed put chain retains its first failing branch and cancellation value. -/
def peerDumpPuts : List (Decision × Nat) → NlSkb → PeerDumpResult →
    (NlSkb → WG.M PeerDumpResult) → WG.M PeerDumpResult
  | [], skb, _, next => next skb
  | (site, cost) :: rest, skb, cancel, next => do
    let (fail, after) := skb.put cost
    if ← branch site fail then return cancel
    peerDumpPuts rest after cancel next

/-- Original endpoint branch and unchanged allowed-IP continuation. -/
def peerDumpEndpointTail (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) : WG.M PeerDumpResult := do
  let family := p.endpoint.map (·.family) |>.getD 0
  let mut skb := skb
  let mut epFail := false
  if ← branch .getPeerEp4 (family == AF_INET) then
    let (fail, s) := skb.put (nlaTotal 16); skb := s; epFail := fail
  else if ← branch .getPeerEp6 (family == AF_INET6) then
    let (fail, s) := skb.put (nlaTotal 28); skb := s; epFail := fail
  if ← branch .getPeerEpFail epFail then return (skb0, ctx, .cancelled)
  let attrs := attrs ++ match p.endpoint with
    | some e =>
      let v4 := e.family == AF_INET
      [("endpoint", Json.mkObj ([("family", toJson (if v4 then 4 else 6)),
        ("addr", toJson (hexBE e.addr (if v4 then 4 else 16))), ("port", toJson e.port)] ++
        (if v4 then [] else [("flowinfo", toJson e.flowinfo), ("scope_id", toJson e.scope)])))]
    | none => []
  getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs p.allowedipsList.head?

/-- The first-visit branch remains between the public key and the remaining puts. -/
def peerDumpFactoredTail (p : Peer) (ctx : DumpCtx) (skb0 : NlSkb) : WG.M PeerDumpResult :=
  peerDumpPuts [(.getPeerNoNest,nlaTotal 0),(.getPeerPubkeyFail,nlaTotal 32)] skb0
    (skb0,ctx,.cancelled) fun skb => do
      let pubkey := hexKey p.remoteStatic
      let attrs := [("public_key",toJson pubkey)]
      if ← branch .getPeerFirst ctx.nextAllowedip.isNone then
        peerDumpPuts [(.getPeerPskFail,nlaTotal 32),(.getPeerPutHandshake,nlaTotal 16),
          (.getPeerPutKeepalive,nlaTotal 2),(.getPeerPutTx,nlaTotal 8),
          (.getPeerPutRx,nlaTotal 8),(.getPeerPutProto,nlaTotal 4)] skb
          (skb0,ctx,.cancelled) fun skb =>
            peerDumpEndpointTail p ctx skb0 skb pubkey (attrs ++
              [("preshared_key", toJson (hexKey p.presharedKey)),
               ("last_handshake", toJson (timespec p.walltimeLastHandshake)),
               ("keepalive", toJson p.persistentKeepaliveInterval),
               ("tx_bytes", toJson p.txBytes), ("rx_bytes", toJson p.rxBytes),
               ("protocol_version", toJson 1)])
      else getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs ctx.nextAllowedip

/-- Exact computation equality for every cursor, endpoint, room and original error. -/
theorem peerDumpTail_factored (p : Peer) (ctx : DumpCtx) (skb : NlSkb) :
    getPeerDumpTailSource p ctx skb = peerDumpFactoredTail p ctx skb := by
  simp only [getPeerDumpTailSource,peerDumpFactoredTail,peerDumpPuts,peerDumpEndpointTail]
  rfl

end Leanux.Proofs.WG.Config
