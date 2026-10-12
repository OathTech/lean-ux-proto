import Leanux.WG.PeerRemove
import Lean.Data.Json

/-!
# drivers/net/wireguard/netlink.c — WG_CMD_SET_DEVICE and WG_CMD_GET_DEVICE

The generic-netlink core (message parsing, `device_policy` validation, the
`GENL_UNS_ADMIN_PERM` check, the dump machinery) is a cut point: the mirror
enters at `wg_set_device` and at the `start`/`dumpit`/`done` callbacks with the
attributes the harness encoded (harness/wg.py). That encoding always names the
device by `WGDEVICE_A_IFNAME` = "wg0", sends `NLA_F_NESTED` lists that
`nla_parse_nested` accepts, never sends a peer's protocol version, and sends
all three attributes of each allowed IP.

A running device's port change rebinds its sockets (`set_port`'s
`wg_socket_init`, L). A dump fits
in one message (`unsupported` above a conservative size), so every `nla_put`
succeeds and the dump completes in its first callback.
-/

namespace Leanux.WG
open Leanux Lean

def WGDEVICE_F_REPLACE_PEERS : UInt32 := 1
def WGDEVICE_F_ALL : UInt32 := 1
def WGPEER_F_REMOVE_ME : UInt32 := 1
def WGPEER_F_REPLACE_ALLOWEDIPS : UInt32 := 2
def WGPEER_F_UPDATE_ONLY : UInt32 := 4
def WGPEER_F_ALL : UInt32 := 7

/-- One nested `WGALLOWEDIP_A_*` list. -/
structure AllowedIpAttrs where
  family : Nat    -- WGALLOWEDIP_A_FAMILY
  addr : Nat      -- WGALLOWEDIP_A_IPADDR, as the big-endian integer of its bytes
  addrLen : Nat   -- nla_len(WGALLOWEDIP_A_IPADDR)
  cidr : Nat      -- WGALLOWEDIP_A_CIDR_MASK (u8)
  deriving Repr

/-- `WGPEER_A_ENDPOINT`: a `sockaddr_in` or `sockaddr_in6` with zero flow
    information and scope. -/
structure EndpointAttr where
  len : Nat
  family : Nat
  addr : Nat
  port : Nat
  deriving Repr

/-- One nested `WGPEER_A_*` list. -/
structure PeerAttrs where
  publicKey : Key
  presharedKey : Option Key := none
  flags : Option UInt32 := none
  endpoint : Option EndpointAttr := none
  keepalive : Option Nat := none
  allowedIps : Option (List AllowedIpAttrs) := none
  deriving Repr

/-- The `WGDEVICE_A_*` attributes after `WGDEVICE_A_IFNAME`. -/
structure DeviceAttrs where
  flags : Option UInt32 := none
  privateKey : Option Key := none
  listenPort : Option Nat := none
  fwmark : Option Nat := none
  peers : Option (List PeerAttrs) := none
  deriving Repr

/-- lookup_interface (netlink.c:52-73) for the harness's `WGDEVICE_A_IFNAME`
    of the fixture's device. -/
def lookupInterface : M (Except Int Unit) := do
  -- `!attrs[WGDEVICE_A_IFINDEX] == !attrs[WGDEVICE_A_IFNAME]`
  if ← branch .lookupBothOrNeither false then return .error (-EBADR)
  if ← branch .lookupHasIfindex false then unsupported "lookup by ifindex"
  _ ← branch .lookupHasIfname true
  -- dev_get_by_name finds wg0 unless the trace's fixture has none (L: a bare
  -- fixture, or after wg_delete); its rtnl_link_ops kind is "wireguard"
  if ← branch .lookupNoDev (← getK).wg.isNone then return .error (-ENODEV)
  if ← orM (branch .lookupNoLinkOps false) (orM (branch .lookupNoKind false)
      (branch .lookupKindMismatch false)) then
    return .error (-EOPNOTSUPP)
  return .ok ()

/-- set_port (netlink.c:314-327). -/
def setPort (port : Nat) : M Int := do
  let d ← getDev
  if ← branch .setPortSame (d.incomingPort == port) then return 0
  for pid in d.peerList do
    _ ← branch .setPortPeerIter true
    clearPeerEndpointSrc pid
  _ ← branch .setPortPeerIter false
  if ← branch .setPortNotRunning !d.running then
    modifyDev fun d => { d with incomingPort := port }
    return 0
  socketInit port

/-- set_allowedip (netlink.c:329-355). -/
def setAllowedip (pid : PeerId) (ip : AllowedIpAttrs) : M Int := do
  if ← orM (branch .aipNoFamily false) (orM (branch .aipNoAddr false) (branch .aipNoCidr false)) then
    return -EINVAL
  if ← andM (branch .aipV4Family (ip.family == AF_INET))
      (andM (branch .aipV4Cidr (ip.cidr ≤ 32)) (branch .aipV4Len (ip.addrLen == 4))) then
    return ← insert 4 ip.addr ip.cidr pid
  if ← andM (branch .aipV6Family (ip.family == AF_INET6))
      (andM (branch .aipV6Cidr (ip.cidr ≤ 128)) (branch .aipV6Len (ip.addrLen == 16))) then
    return ← insert 6 ip.addr ip.cidr pid
  return -EINVAL

/-- set_peer (netlink.c:357-491). -/
def setPeerCmd (a : PeerAttrs) : M Int := do
  let out (peer : Option PeerId) (ret : Int) : M Int := do
    peerPut peer
    _ ← branch .peerZeroPsk a.presharedKey.isSome   -- memzero_explicit
    return ret
  -- the policy guarantees the exact key lengths
  if !(← andM (branch .peerHasPubkey true) (branch .peerPubkeyLen true)) then return ← out none (-EINVAL)
  let psk ← do
    if ← andM (branch .peerHasPsk a.presharedKey.isSome) (branch .peerPskLen true) then pure a.presharedKey
    else pure none
  let mut flags : UInt32 := 0
  if ← branch .peerHasFlags a.flags.isSome then flags := a.flags.getD 0
  if ← branch .peerBadFlags (flags &&& ~~~WGPEER_F_ALL != 0) then return ← out none (-EOPNOTSUPP)
  if ← branch .peerHasProtocol false then unsupported "WGPEER_A_PROTOCOL_VERSION"
  let mut peer ← pubkeyLookup a.publicKey
  if ← branch .peerNotFound peer.isNone then
    if ← branch .peerNewRemoveOrUpdate (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0) then
      return ← out none 0
    flags := flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS
    let id := (← getDev).staticIdentity
    if ← andM (branch .peerSelfHasIdentity id.hasIdentity) (branch .peerSelfKeyMatch (a.publicKey == id.staticPublic)) then
      return ← out none 0
    match ← peerCreate a.publicKey psk with
    | .error e =>
      _ ← branch .peerCreateErr true
      return ← out none e
    | .ok pid =>
      _ ← branch .peerCreateErr false
      peerGet pid   -- as though just looked up
      peer := some pid
  let some pid := peer | invariant "set_peer without a peer"
  if ← branch .peerRemoveMe (flags &&& WGPEER_F_REMOVE_ME != 0) then
    peerRemove peer
    return ← out peer 0
  if ← branch .peerSetPsk psk.isSome then
    setPeer pid { (← getPeer pid) with presharedKey := psk.getD [] }
  if ← branch .peerHasEndpoint a.endpoint.isSome then
    let some e := a.endpoint | invariant "unreachable"
    if ← andM (branch .peerEndpointV4Len (e.len == 16)) (branch .peerEndpointV4Family (e.family == AF_INET)) then
      setPeerEndpoint pid { family := e.family, addr := e.addr, port := e.port }
    else if ← andM (branch .peerEndpointV6Len (e.len == 28)) (branch .peerEndpointV6Family (e.family == AF_INET6)) then
      setPeerEndpoint pid { family := e.family, addr := e.addr, port := e.port }
  if ← branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) then removeByPeer pid
  let mut ret : Int := 0
  if ← branch .peerHasAips a.allowedIps.isSome then
    for ip in a.allowedIps.getD [] do
      _ ← branch .peerAipsIter true
      if ← branch .peerAipParseErr false then unsupported "unreachable"
      ret ← setAllowedip pid ip
      if ← branch .peerAipErr (ret < 0) then return ← out peer ret
    _ ← branch .peerAipsIter false
  let running := (← getDev).running
  if ← branch .peerHasKeepalive a.keepalive.isSome then
    let interval := a.keepalive.getD 0
    let p ← getPeer pid
    let send ← andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))
    setPeer pid { p with persistentKeepaliveInterval := interval }
    if ← branch .peerSendKeepalive send then sendKeepalive pid
  if ← branch .peerRunning running then sendStagedPackets pid
  out peer ret

/-- wg_set_device (netlink.c:493-608). The harness's process is root in the
    initial user namespace, so `ns_capable(creating_net->user_ns, ...)` holds. -/
def wgSetDevice (a : DeviceAttrs) : M Int := do
  let zero (ret : Int) : M Int := do
    _ ← branch .setDevZeroKey a.privateKey.isSome   -- memzero_explicit
    return ret
  let wg ← lookupInterface
  if ← branch .setDevLookupErr (wg matches .error _) then
    let .error e := wg | invariant "unreachable"
    return ← zero e
  let mut flags : UInt32 := 0
  if ← branch .setDevHasFlags a.flags.isSome then flags := a.flags.getD 0
  if ← branch .setDevBadFlags (flags &&& ~~~WGDEVICE_F_ALL != 0) then return ← zero (-EOPNOTSUPP)
  if ← orM (branch .setDevHasPort a.listenPort.isSome) (branch .setDevHasFwmark a.fwmark.isSome) then
    let denied ← orM (branch .setDevNoNet false) (branch .setDevNotCapable false)
    if ← branch .setDevPermErr denied then return ← zero (-EPERM)
  modifyDev fun d => { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  if ← branch .setDevFwmark a.fwmark.isSome then
    modifyDev fun d => { d with fwmark := a.fwmark.getD 0 }
    for pid in (← getDev).peerList do
      _ ← branch .setDevFwmarkPeerIter true
      clearPeerEndpointSrc pid
    _ ← branch .setDevFwmarkPeerIter false
  if ← branch .setDevPort a.listenPort.isSome then
    let ret ← setPort (a.listenPort.getD 0)
    if ← branch .setDevPortErr (ret != 0) then return ← zero ret
  if ← branch .setDevReplacePeers (flags &&& WGDEVICE_F_REPLACE_PEERS != 0) then peerRemoveAll
  if ← andM (branch .setDevHasPrivateKey a.privateKey.isSome) (branch .setDevPrivateKeyLen true) then
    let some key := a.privateKey | invariant "unreachable"
    -- `!crypto_memneq(static_private, private_key)`: the stored key is clamped
    if !(← branch .setDevKeyUnchanged ((← getDev).staticIdentity.staticPrivate == key)) then
      -- remove the peer whose public key the device is about to take
      let (pub, ok) ← generatePublic key
      if ← branch .setDevGenPublic ok then
        let some pub := pub | invariant "a generated public key without a write"
        let peer ← pubkeyLookup pub
        if ← branch .setDevOldPeer peer.isSome then
          peerPut peer
          peerRemove peer
      let d ← getDev
      let sendStaged ← andM (branch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
        (branch .setDevSendStagedRunning d.running)
      setStaticIdentityPrivateKey key
      let hasIdentity := (← getDev).staticIdentity.hasIdentity
      let sendStaged ← andM (branch .setDevSendStagedKept sendStaged) (branch .setDevSendStagedHasIdentity hasIdentity)
      cookiePrecomputeDeviceKeys
      for pid in (← getDev).peerList do
        _ ← branch .setDevKeyPeerIter true
        precomputeStaticStatic pid
        expireCurrentPeerKeypairs pid
        if ← branch .setDevSendStagedPeer sendStaged then sendStagedPackets pid
      _ ← branch .setDevKeyPeerIter false
  if ← branch .setDevHasPeers a.peers.isSome then
    for p in a.peers.getD [] do
      _ ← branch .setDevPeersIter true
      if ← branch .setDevParseErr false then unsupported "unreachable"
      let ret ← setPeerCmd p
      if ← branch .setDevSetPeerErr (ret < 0) then return ← zero ret
    _ ← branch .setDevPeersIter false
  zero 0

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
  let endpoint := match p.endpoint with
    | some e =>
      let v4 := e.family == AF_INET
      [("endpoint", Json.mkObj ([("family", toJson (if v4 then 4 else 6)),
        ("addr", toJson (hexBE e.addr (if v4 then 4 else 16))), ("port", toJson e.port)]
        -- W5 (2.5): `sin6_scope_id` of an IPv6 endpoint (the dump's sockaddr_in6)
        ++ (if v4 then [] else [("scope", toJson e.scope)])))]
    | none => []
  return Json.mkObj ([("public_key", toJson (hexKey p.remoteStatic)),
    ("preshared_key", toJson (hexKey p.presharedKey)),
    ("last_handshake", toJson (timespec p.walltimeLastHandshake)), ("keepalive", toJson p.persistentKeepaliveInterval),
    ("tx_bytes", toJson p.txBytes), ("rx_bytes", toJson p.rxBytes), ("protocol_version", toJson 1)] ++ endpoint ++
    [("allowed_ips", Json.arr ips)])

/-- A WG_CMD_GET_DEVICE dump: wg_get_device_start (199-208), one
    wg_get_device_dump (210-302) that completes the dump, and
    wg_get_device_done (304-312). Returns the canonical device state. -/
def wgGetDevice : M (Except Int Json) := do
  let wg ← lookupInterface
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
