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

/-- One nested `WGALLOWEDIP_A_*` list (W1: any subset of the three). -/
structure AllowedIpAttrs where
  family : Option Nat    -- WGALLOWEDIP_A_FAMILY (u16, the wire value)
  addr : Option Nat      -- WGALLOWEDIP_A_IPADDR, as the big-endian integer of its bytes
  addrLen : Nat          -- nla_len(WGALLOWEDIP_A_IPADDR); 0 without the attribute
  cidr : Option Nat      -- WGALLOWEDIP_A_CIDR_MASK (u8)
  deriving Repr

/-- An entry of `WGPEER_A_ALLOWEDIPS`: parsed, or without `NLA_F_NESTED`,
    which `nla_parse_nested` rejects with `-EINVAL` before any attribute is
    read (include/net/netlink.h:1315-1318; the one sanctioned malformation,
    W1 2.2). -/
inductive AllowedIpEntry
  | malformed
  | attrs (a : AllowedIpAttrs)
  deriving Repr

/-- `WGPEER_A_ENDPOINT`: `len` bytes whose `sa_family` is `family`; a
    `sockaddr_in` (`len` 16) or a `sockaddr_in6` (`len` 28) with its
    `sin6_flowinfo` and `sin6_scope_id`. Any other length or family is
    ignored by `set_peer` (netlink.c:441-447). -/
structure EndpointAttr where
  len : Nat
  family : Nat
  addr : Nat
  port : Nat
  flowinfo : Nat := 0
  scope : Nat := 0
  deriving Repr

/-- One nested `WGPEER_A_*` list. -/
structure PeerAttrs where
  publicKey : Option Key := none
  presharedKey : Option Key := none
  flags : Option UInt32 := none
  protocolVersion : Option Nat := none
  endpoint : Option EndpointAttr := none
  keepalive : Option Nat := none
  allowedIps : Option (List AllowedIpEntry) := none
  deriving Repr

/-- An entry of `WGDEVICE_A_PEERS`: parsed, or without `NLA_F_NESTED`. -/
inductive PeerEntry
  | malformed
  | attrs (a : PeerAttrs)
  deriving Repr

/-- The device selector (`WGDEVICE_A_IFNAME`, `WGDEVICE_A_IFINDEX`): the
    harness sends wg0 by name unless the trace says otherwise. -/
structure DeviceRef where
  ifname : Option String := some "wg0"
  ifindex : Option Nat := none
  deriving Repr

/-- The `WGDEVICE_A_*` attributes. -/
structure DeviceAttrs where
  device : DeviceRef := {}
  flags : Option UInt32 := none
  privateKey : Option Key := none
  listenPort : Option Nat := none
  fwmark : Option Nat := none
  peers : Option (List PeerEntry) := none
  deriving Repr

/-- The socket's namespace's device table as `lookup_interface` reads it:
    the fixture's devices (`World.fixtureNetDevices`, from `Env`) and wg0 at
    its current ifindex with kind "wireguard" when it exists (`Kernel.wg`:
    L's bare fixture and `wg_delete` leave none). -/
def netDevices : M (List (String × Nat × Option String)) := do
  let fixture := (← get).fixtureNetDevices
  match (← getK).wg with
  | some d => return fixture ++ [(d.ifname, d.ifindex, some "wireguard")]
  | none => return fixture

/-- lookup_interface (netlink.c:52-73). `dev_get_by_index` and
    `dev_get_by_name` are cut points over the device table. -/
def lookupInterface (ref : DeviceRef) : M (Except Int Unit) := do
  -- `!attrs[WGDEVICE_A_IFINDEX] == !attrs[WGDEVICE_A_IFNAME]`
  if ← branch .lookupBothOrNeither (ref.ifindex.isSome == ref.ifname.isSome) then return .error (-EBADR)
  let devs ← netDevices
  let row ← do
    if ← branch .lookupHasIfindex ref.ifindex.isSome then
      pure (devs.find? fun r => some r.2.1 == ref.ifindex)
    else
      _ ← branch .lookupHasIfname true
      pure (devs.find? fun r => some r.1 == ref.ifname)
  if ← branch .lookupNoDev row.isNone then return .error (-ENODEV)
  let some (_, _, kind) := row | invariant "unreachable"
  -- `!dev->rtnl_link_ops || !dev->rtnl_link_ops->kind || strcmp(kind, "wireguard")`:
  -- `lo` has no link ops; `!kind` is structurally false (every registered
  -- rtnl_link_ops sets .kind, rtnetlink.c:499-522; W1 2.1); `sit0` is "sit"
  let notWireguard ← orM (branch .lookupNoLinkOps kind.isNone) (orM (branch .lookupNoKind false)
      (branch .lookupKindMismatch (kind != some "wireguard")))
  if ← branch .lookupNotWireguard notWireguard then return .error (-EOPNOTSUPP)
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
  if ← orM (branch .aipNoFamily ip.family.isNone) (orM (branch .aipNoAddr ip.addr.isNone) (branch .aipNoCidr ip.cidr.isNone)) then
    return -EINVAL
  let family := ip.family.getD 0
  let addr := ip.addr.getD 0
  let cidr := ip.cidr.getD 0
  if ← andM (branch .aipV4Family (family == AF_INET))
      (andM (branch .aipV4Cidr (cidr ≤ 32)) (branch .aipV4Len (ip.addrLen == 4))) then
    return ← insert 4 addr cidr pid
  if ← andM (branch .aipV6Family (family == AF_INET6))
      (andM (branch .aipV6Cidr (cidr ≤ 128)) (branch .aipV6Len (ip.addrLen == 16))) then
    return ← insert 6 addr cidr pid
  return -EINVAL

/-- set_peer (netlink.c:357-491). -/
def setPeerCmd (a : PeerAttrs) : M Int := do
  let out (peer : Option PeerId) (ret : Int) : M Int := do
    peerPut peer
    _ ← branch .peerZeroPsk a.presharedKey.isSome   -- memzero_explicit
    return ret
  -- the policy guarantees the exact key length (P8); the attribute may be absent
  if !(← andM (branch .peerHasPubkey a.publicKey.isSome) (branch .peerPubkeyLen true)) then return ← out none (-EINVAL)
  let some publicKey := a.publicKey | invariant "unreachable"
  let psk ← do
    if ← andM (branch .peerHasPsk a.presharedKey.isSome) (branch .peerPskLen true) then pure a.presharedKey
    else pure none
  let mut flags : UInt32 := 0
  if ← branch .peerHasFlags a.flags.isSome then flags := a.flags.getD 0
  if ← branch .peerBadFlags (flags &&& ~~~WGPEER_F_ALL != 0) then return ← out none (-EOPNOTSUPP)
  if ← branch .peerHasProtocol a.protocolVersion.isSome then
    if ← branch .peerBadProtocol (a.protocolVersion != some 1) then return ← out none (-EPFNOSUPPORT)
  let mut peer ← pubkeyLookup publicKey
  if ← branch .peerNotFound peer.isNone then
    if ← branch .peerNewRemoveOrUpdate (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0) then
      return ← out none 0
    flags := flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS
    let id := (← getDev).staticIdentity
    if ← andM (branch .peerSelfHasIdentity id.hasIdentity) (branch .peerSelfKeyMatch (publicKey == id.staticPublic)) then
      return ← out none 0
    match ← peerCreate publicKey psk with
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
    -- `endpoint.addr4 = *(struct sockaddr_in *)addr` (sin_zero is zero, W1 5);
    -- `endpoint.addr6 = *(struct sockaddr_in6 *)addr` copies flowinfo and scope
    if ← andM (branch .peerEndpointV4Len (e.len == 16)) (branch .peerEndpointV4Family (e.family == AF_INET)) then
      setPeerEndpoint pid { family := e.family, addr := e.addr, port := e.port }
    else if ← andM (branch .peerEndpointV6Len (e.len == 28)) (branch .peerEndpointV6Family (e.family == AF_INET6)) then
      setPeerEndpoint pid { family := e.family, addr := e.addr, port := e.port, scope := e.scope, flowinfo := e.flowinfo }
  if ← branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0) then removeByPeer pid
  let mut ret : Int := 0
  if ← branch .peerHasAips a.allowedIps.isSome then
    for entry in a.allowedIps.getD [] do
      _ ← branch .peerAipsIter true
      match entry with
      | .malformed =>   -- nla_parse_nested: NLA_F_NESTED missing, -EINVAL
        _ ← branch .peerAipParseErr true
        return ← out peer (-EINVAL)
      | .attrs ip =>
        _ ← branch .peerAipParseErr false
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
  let wg ← lookupInterface a.device
  if ← branch .setDevLookupErr (wg matches .error _) then
    let .error e := wg | invariant "unreachable"
    return ← zero e
  let mut flags : UInt32 := 0
  if ← branch .setDevHasFlags a.flags.isSome then flags := a.flags.getD 0
  if ← branch .setDevBadFlags (flags &&& ~~~WGDEVICE_F_ALL != 0) then return ← zero (-EOPNOTSUPP)
  if ← orM (branch .setDevHasPort a.listenPort.isSome) (branch .setDevHasFwmark a.fwmark.isSome) then
    -- W8: `!net` once the creating namespace exited (netlink.c:517); the
    -- capability half is constant true on this config (section 2.2)
    let denied ← orM (branch .setDevNoNet !(← getDev).creatingNet) (branch .setDevNotCapable false)
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
    for entry in a.peers.getD [] do
      _ ← branch .setDevPeersIter true
      match entry with
      | .malformed =>   -- nla_parse_nested: NLA_F_NESTED missing, -EINVAL
        _ ← branch .setDevParseErr true
        return ← zero (-EINVAL)
      | .attrs p =>
        _ ← branch .setDevParseErr false
        let ret ← setPeerCmd p
        if ← branch .setDevSetPeerErr (ret < 0) then return ← zero ret
    _ ← branch .setDevPeersIter false
  zero 0

end Leanux.WG
