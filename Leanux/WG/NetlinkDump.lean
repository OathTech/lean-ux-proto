import Leanux.WG.Netlink

/-!
# drivers/net/wireguard/netlink.c — WG_CMD_GET_DEVICE

The dump half of `Leanux/WG/Netlink.lean` (W1+W2 execution plan, step 0:
moved verbatim). The set path and the device lookup stay in Netlink.lean.
-/

namespace Leanux.WG
open Leanux Lean

/-! ## WG_CMD_GET_DEVICE -/

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

def hexKey (k : Key) : String :=
  String.ofList (k.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit b.toNat])

/-- `len` bytes of `n`, big-endian, as lowercase hex. -/
def hexBE (n len : Nat) : String :=
  String.ofList ((List.range len).reverse.flatMap fun i =>
    let b := n / 256 ^ i % 256
    [hexDigit (b / 16), hexDigit b])

/-- A conservative bound on the dump's single message: every netlink skb the
    dump can get holds at least `NLMSG_GOODSIZE` (about 3.7 KiB) bytes. -/
def DUMP_BOUND : Nat := 3000

/-- The dump message's size: netlink and genetlink headers, then the
    attributes `wg_get_device_dump` and `get_peer` put. -/
def dumpSize (d : Device) : M Nat := do
  let mut size := 16 + 4 + 8 + 8 + 8 + 8 + 4   -- headers, port, fwmark, ifindex, "wg0", peers nest
  if d.staticIdentity.hasIdentity then size := size + 72
  for pid in d.peerList do
    let p ← getPeer pid
    size := size + 4 + 36 + 36 + 20 + 8 + 12 + 12 + 8
    size := size + match p.endpoint with
      | some e => if e.family == AF_INET then 20 else 32
      | none => 0
    if !p.allowedipsList.isEmpty then size := size + 4
    for id in p.allowedipsList do
      size := size + 4 + 8 + 8 + (if (← getNode id).bitlen == 32 then 8 else 20)
  return size

/-- get_allowedips (netlink.c:75-94), after wg_allowedips_read_node. -/
def getAllowedips (family masked cidr : Nat) : M Json := do
  _ ← branch .getAipNoNest false
  _ ← branch .getAipPutCidr false
  _ ← branch .getAipPutFamily false
  let inet6 ← branch .getAipFamily6 (family == 6)   -- sizeof(in6_addr) or sizeof(in_addr)
  _ ← branch .getAipPutAddr false
  return Json.mkObj [("family", toJson family), ("addr", toJson (hexBE masked (if inet6 then 16 else 4))),
    ("cidr", toJson cidr)]

/-- A `struct timespec64` (16 bytes: `tv_sec`, `tv_nsec`, little-endian
    s64) as the `__kernel_timespec` the dump puts (netlink.c:124-138). -/
def timespec (ts : List UInt8) : List Int :=
  let s64 (bs : List UInt8) : Int :=
    let u : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0
    if u ≥ 2 ^ 63 then (u : Int) - (2 ^ 64 : Int) else (u : Int)
  [s64 (ts.take 8), s64 ((ts.drop 8).take 8)]

/-- get_peer (netlink.c:105-197) on a fresh cursor. -/
def getPeerDump (pid : PeerId) : M Json := do
  let p ← getPeer pid
  _ ← branch .getPeerNoNest false
  _ ← branch .getPeerPubkeyFail false
  _ ← branch .getPeerFirst true   -- ctx->next_allowedip is NULL
  _ ← branch .getPeerPskFail false
  _ ← branch .getPeerPutHandshake false
  _ ← branch .getPeerPutKeepalive false
  _ ← branch .getPeerPutTx false
  _ ← branch .getPeerPutRx false
  _ ← branch .getPeerPutProto false
  let family := p.endpoint.map (·.family) |>.getD 0
  if !(← branch .getPeerEp4 (family == AF_INET)) then _ ← branch .getPeerEp6 (family == AF_INET6)
  _ ← branch .getPeerEpFail false
  let mut ips : Array Json := #[]
  if !(← branch .getPeerNoAips p.allowedipsList.isEmpty) then
    _ ← branch .getPeerSeqUnset true   -- ctx->allowedips_seq is 0 on a fresh peer
    _ ← branch .getPeerAipsNestFail false
    for id in p.allowedipsList do
      _ ← branch .getPeerAipIter true
      let (family, masked, cidr) ← readNode (← getNode id)
      ips := ips.push (← getAllowedips family masked cidr)
      _ ← branch .getPeerAipFail false
    _ ← branch .getPeerAipIter false
  -- the whole sockaddr is returned (netlink.c:150-156): for IPv6 its
  -- flowinfo and scope_id too (W1 3.2)
  let endpoint := match p.endpoint with
    | some e =>
      let v4 := e.family == AF_INET
      [("endpoint", Json.mkObj ([("family", toJson (if v4 then 4 else 6)),
        ("addr", toJson (hexBE e.addr (if v4 then 4 else 16))), ("port", toJson e.port)] ++
        (if v4 then [] else [("flowinfo", toJson e.flowinfo), ("scope_id", toJson e.scope)])))]
    | none => []
  return Json.mkObj ([("public_key", toJson (hexKey p.remoteStatic)),
    ("preshared_key", toJson (hexKey p.presharedKey)),
    ("last_handshake", toJson (timespec p.walltimeLastHandshake)), ("keepalive", toJson p.persistentKeepaliveInterval),
    ("tx_bytes", toJson p.txBytes), ("rx_bytes", toJson p.rxBytes), ("protocol_version", toJson 1)] ++ endpoint ++
    [("allowed_ips", Json.arr ips)])

/-- A WG_CMD_GET_DEVICE dump: wg_get_device_start (199-208), one
    wg_get_device_dump (210-302) that completes the dump, and
    wg_get_device_done (304-312). Returns the canonical device state. -/
def wgGetDevice (ref : DeviceRef) : M (Except Int Json) := do
  let wg ← lookupInterface ref
  if ← branch .getStartErr (wg matches .error _) then
    let .error e := wg | invariant "unreachable"
    return .error e
  let d ← getDev
  -- the handshake worker updates tx_bytes
  for pid in d.peerList do requireNotPending pid "dumping the peer"
  if (← dumpSize d) > DUMP_BOUND then unsupported "dump larger than one message"
  _ ← branch .dumpNoHdr false
  _ ← branch .dumpFirst true   -- ctx->next_peer is NULL
  _ ← branch .dumpPutPort false
  _ ← branch .dumpPutFwmark false
  _ ← branch .dumpPutIfindex false
  _ ← branch .dumpPutIfname false
  let identity := d.staticIdentity
  if ← branch .dumpHasIdentity identity.hasIdentity then
    _ ← branch .dumpPutPrivate false
    _ ← branch .dumpPutPublic false
  _ ← branch .dumpNoPeersNest false
  let mut peers : Array Json := #[]
  if !(← orM (branch .dumpPeerListEmpty d.peerList.isEmpty)
      (andM (branch .dumpCursorSet false) (branch .dumpCursorDead false))) then
    for pid in d.peerList do
      _ ← branch .dumpPeerIter true
      peers := peers.push (← getPeerDump pid)
      _ ← branch .dumpGetPeerFail false
    _ ← branch .dumpPeerIter false
  -- out: `!ret && !done && next_peer_cursor`
  _ ← andM (branch .dumpOutRetZero true) (andM (branch .dumpOutNotDone false) (branch .dumpOutHasCursor false))
  peerPut none   -- wg_peer_put(ctx->next_peer)
  _ ← branch .dumpRetErr false
  _ ← branch .dumpDone true
  -- wg_get_device_done
  _ ← branch .getDoneHasWg true
  peerPut none
  let keys := if identity.hasIdentity then
      [("private_key", toJson (hexKey identity.staticPrivate)),
       ("public_key", toJson (hexKey identity.staticPublic))]
    else []
  return .ok (Json.mkObj ([("ifindex", toJson d.ifindex), ("ifname", toJson d.ifname),
    ("listen_port", toJson d.incomingPort), ("fwmark", toJson d.fwmark)] ++ keys ++
    [("peers", Json.arr peers)]))

end Leanux.WG
