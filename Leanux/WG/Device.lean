import Leanux.WG.Netlink

/-!
# drivers/net/wireguard/device.c — bringing wg0 up and transmitting

`wg_up` is `dev_change_flags(wg0, flags | IFF_UP)`, which sets
`__LINK_STATE_START` and calls `wg_open`. `wg_socket_init` (the UDP sockets on
`incoming_port`) is a cut point that succeeds on a fixed, free port; a zero
port (a random one) is `unsupported`. The fixture's own ports are excluded by
the environment (`Leanux/Env.lean`).

`wg_xmit` receives the fixture sender's UDP datagrams, routed into wg0 by the
default routes added at `wg_up`: never GSO, not shared, with a dst, and with
`skb->protocol` matching the IP version (so `wg_check_packet_protocol`
holds). `ip_tunnel_parse_protocol` (include/net/ip_tunnels.h) is a cut point.
-/

namespace Leanux.WG
open Leanux

/-- lookup (allowedips.c:127-147): a strong reference to the peer of the
    longest matching prefix. -/
def lookup (root : Option NodeId) (bits key : Nat) : M (Option PeerId) := do
  swapEndian bits   -- swap_endian(ip, be_ip, bits): `bits` is a runtime value here
  let node ← findNode root bits key
  if ← branch .lookupFound node.isSome then
    let some id := node | invariant "unreachable"
    let peer ← peerGetMaybeZero (← getNode id).peer
    -- a node's peer is alive while it is in the trie
    if ← branch .lookupPeerGone peer.isNone then unsupported "lookup retry after a dying peer"
    return peer
  return none

/-- wg_allowedips_lookup_dst (allowedips.c:356-364). -/
def lookupDst (family addr : Nat) : M (Option PeerId) := do
  let t := (← getDev).peerAllowedips
  if ← branch .lookupDstV4 (family == 4) then return ← lookup t.root4 32 addr
  if ← branch .lookupDstV6 (family == 6) then return ← lookup t.root6 128 addr
  return none

/-- wg_open (device.c:31-62). The fixture's wg0 has an IPv4 and an IPv6
    device (its MTU of 1420 admits both at registration). -/
def wgOpen : M Int := do
  _ ← branch .openHasInet true    -- IN_DEV_CONF_SET(SEND_REDIRECTS, false)
  _ ← branch .openHasInet6 true   -- addr_gen_mode = IN6_ADDR_GEN_MODE_NONE
  let d ← getDev
  -- wg_socket_init on incoming_port: a random port for 0 (outside the domain)
  if d.incomingPort == 0 then unsupported "wg_socket_init on a random port"
  if ← branch .openSocketError false then unsupported "unreachable"
  for pid in d.peerList do
    _ ← branch .openPeersIter true
    sendStagedPackets pid
    if ← branch .openKeepalive ((← getPeer pid).persistentKeepaliveInterval != 0) then sendKeepalive pid
  _ ← branch .openPeersIter false
  return 0

/-- `dev_change_flags` to IFF_UP: `__dev_open` sets `__LINK_STATE_START`
    before `ndo_open`. The routes added after it are fixture. -/
def wgUp : M Int := do
  modifyDev fun d => { d with running := true }
  wgOpen

/-- wg_xmit (device.c:137-233) for a datagram to `addr` (family 4 or 6),
    an IP packet of `len` bytes. -/
def wgXmit (family addr len : Nat) : M Int := do
  -- `real_protocol && skb->protocol == real_protocol`
  let ok ← andM (branch .checkProtoParsed true) (branch .checkProtoMatches true)
  if ← branch .xmitBadProtocol !ok then unsupported "unreachable"
  let err (ret : Int) : M Int := do
    -- err_icmp: icmp_ndo_send / icmpv6_ndo_send (cut points, whose rate limit
    -- and IP output draw cut-site choices), then err:
    if !(← branch .xmitErrorInet (family == 4)) then _ ← branch .xmitErrorInet6 (family == 6)
    skipCut [.icmpCredit, .ipIdentKey, .ipIdentReserve, .flowHashSecret]
    modifyDev fun d => { d with txErrors := d.txErrors + 1 }   -- DEV_STATS_INC(dev, tx_errors)
    return ret
  let peer ← lookupDst family addr
  if ← branch .xmitNoPeer peer.isNone then
    if !(← branch .xmitNoPeerInet (family == 4)) then _ ← branch .xmitNoPeerInet6 (family == 6)
    return ← err (-ENOKEY)
  let some pid := peer | invariant "unreachable"
  let epFamily := (← getPeer pid).endpoint.map (·.family) |>.getD 0
  if ← andM (branch .xmitEndpointNotInet (epFamily != AF_INET)) (branch .xmitEndpointNotInet6 (epFamily != AF_INET6)) then
    peerPut peer   -- err_peer
    return ← err (-EDESTADDRREQ)
  _ ← branch .xmitValidDst true   -- mtu = dst_mtu(skb_dst(skb))
  _ ← branch .xmitNotGso true     -- skb_mark_not_on_list
  _ ← branch .xmitWalk true
  _ ← branch .xmitShareFailed false
  _ ← branch .xmitWalk false
  -- `while (skb_queue_len(&peer->staged_packet_queue) > MAX_STAGED_PACKETS)`
  if ← branch .xmitStagedOverflow ((← getPeer pid).staged.length > MAX_STAGED_PACKETS) then
    unsupported "more than MAX_STAGED_PACKETS staged packets"
  setPeer pid { (← getPeer pid) with staged := (← getPeer pid).staged ++ [len] }   -- skb_queue_splice_tail
  sendStagedPackets pid
  peerPut peer
  return 0   -- NETDEV_TX_OK

end Leanux.WG
