import Leanux.WG.NetlinkDump

/-! Local source-factor variant from campaign 1 at c4ef635; no shared file is edited.

The original dump after its first peer getter. The saved record is consumed
only by serialization, branch records and node reads, with no resident-object
mutation or release. All source returns and failure paths remain in this factor. -/
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean
set_option maxHeartbeats 1000000

def getPeerDumpAllowedSource (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) (node : Option NodeId) :
    M (NlSkb × DumpCtx × PeerDump) := do
  let mut ctx := ctx
  let mut skb := skb
  let done (ctx : DumpCtx) (attrs : List (String × Json)) : DumpCtx × PeerDump :=
    ({ ctx with nextAllowedip := none, allowedipsSeq := 0 }, .complete { publicKey := pubkey, attrs })
  if ← branch .getPeerNoAips node.isNone then
    -- no_allowedips: nla_nest_end(peer_nest), both cursors reset
    let (c, r) := done ctx attrs
    return (skb, c, r)
  let seq := (← getDev).peerAllowedips.seq
  if ← branch .getPeerSeqUnset (ctx.allowedipsSeq == 0) then
    ctx := { ctx with allowedipsSeq := seq }
  else if ← branch .getPeerSeqChanged (ctx.allowedipsSeq != seq) then
    let (c, r) := done ctx attrs
    return (skb, c, r)
  let (fail, s) := skb.put (nlaTotal 0); skb := s
  if ← branch .getPeerAipsNestFail fail then return (skb0, ctx, .cancelled)
  -- list_for_each_entry_from(allowedips_node, &peer->allowedips_list): the
  -- node is dereferenced here, after the seq test (:175); an unchanged seq
  -- means it is still on the list
  let some start := node | invariant "unreachable"
  let rest := p.allowedipsList.dropWhile (· != start)
  if rest.isEmpty then invariant "a stale allowed-IPs cursor with an unchanged sequence (2.4)"
  let mut ips : Array Json := #[]
  for id in rest do
    _ ← branch .getPeerAipIter true
    let (family, masked, cidr) ← readNode (← getNode id)
    let (s, ip) ← getAllowedips skb family masked cidr
    skb := s
    if ← branch .getPeerAipFail ip.isNone then
      -- nla_nest_end both; ctx->next_allowedip = node; return -EMSGSIZE
      return (skb, { ctx with nextAllowedip := some id },
        .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr ips)], split := true })
    ips := ips.push ip.get!
  _ ← branch .getPeerAipIter false
  let (c, r) := done ctx (attrs ++ [("allowed_ips", Json.arr ips)])
  return (skb, c, r)

def getPeerDumpTailSource (p : Peer) (ctx0 : DumpCtx) (skb0 : NlSkb) :
    M (NlSkb × DumpCtx × PeerDump) := do
  let mut ctx := ctx0
  -- peer_nest = nla_nest_start(skb, 0); allowedips_node = ctx->next_allowedip
  let (fail, skb) := skb0.put (nlaTotal 0)
  if ← branch .getPeerNoNest fail then return (skb0, ctx, .cancelled)
  let mut node := ctx.nextAllowedip
  let mut skb := skb
  let pubkey := hexKey p.remoteStatic
  let mut attrs : List (String × Json) := [("public_key", toJson pubkey)]
  let (fail, s) := skb.put (nlaTotal 32); skb := s
  if ← branch .getPeerPubkeyFail fail then return (skb0, ctx, .cancelled)
  if ← branch .getPeerFirst node.isNone then
    let (fail, s) := skb.put (nlaTotal 32); skb := s
    if ← branch .getPeerPskFail fail then return (skb0, ctx, .cancelled)
    -- the `||` chain of :137-146: each put runs only if the earlier ones succeeded
    let (fail, s) := skb.put (nlaTotal 16); skb := s
    if ← branch .getPeerPutHandshake fail then return (skb0, ctx, .cancelled)
    let (fail, s) := skb.put (nlaTotal 2); skb := s
    if ← branch .getPeerPutKeepalive fail then return (skb0, ctx, .cancelled)
    let (fail, s) := skb.put (nlaTotal 8); skb := s
    if ← branch .getPeerPutTx fail then return (skb0, ctx, .cancelled)
    let (fail, s) := skb.put (nlaTotal 8); skb := s
    if ← branch .getPeerPutRx fail then return (skb0, ctx, .cancelled)
    let (fail, s) := skb.put (nlaTotal 4); skb := s
    if ← branch .getPeerPutProto fail then return (skb0, ctx, .cancelled)
    attrs := attrs ++ [("preshared_key", toJson (hexKey p.presharedKey)),
      ("last_handshake", toJson (timespec p.walltimeLastHandshake)), ("keepalive", toJson p.persistentKeepaliveInterval),
      ("tx_bytes", toJson p.txBytes), ("rx_bytes", toJson p.rxBytes), ("protocol_version", toJson 1)]
    -- the whole sockaddr is put (:150-156): for IPv6 its flowinfo and
    -- scope_id too (W1 3.2)
    let family := p.endpoint.map (·.family) |>.getD 0
    let mut epFail := false
    if ← branch .getPeerEp4 (family == AF_INET) then
      let (fail, s) := skb.put (nlaTotal 16); skb := s; epFail := fail
    else if ← branch .getPeerEp6 (family == AF_INET6) then
      let (fail, s) := skb.put (nlaTotal 28); skb := s; epFail := fail
    if ← branch .getPeerEpFail epFail then return (skb0, ctx, .cancelled)
    attrs := attrs ++ match p.endpoint with
      | some e =>
        let v4 := e.family == AF_INET
        [("endpoint", Json.mkObj ([("family", toJson (if v4 then 4 else 6)),
          ("addr", toJson (hexBE e.addr (if v4 then 4 else 16))), ("port", toJson e.port)] ++
          (if v4 then [] else [("flowinfo", toJson e.flowinfo), ("scope_id", toJson e.scope)])))]
      | none => []
    node := p.allowedipsList.head?   -- list_first_entry_or_null
  getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs node

theorem getPeerDump_source (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) :
    getPeerDump pid ctx skb = (do
      let p ← getPeer pid
      getPeerDumpTailSource p ctx skb) := by rfl

end Leanux.Proofs.WG.Config
