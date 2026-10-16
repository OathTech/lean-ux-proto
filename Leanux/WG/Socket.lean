import Leanux.WG.State
import Leanux.Net.Route

/-!
# drivers/net/wireguard/socket.c — wg0's UDP sockets (L)

`wg_socket_init` (socket.c:349-417) and `wg_socket_reinit` (419-437),
docs/2026-10-05-l-lifecycle.md, section 2.3.

`wg_socket_init` is a cut point: `udp_sock_create` binds a wildcard IPv4
socket, then a `v6only` wildcard IPv6 socket at the port the first got. Its
outcome is decided by the fixture's bound ports (`World.portBound`, the
environment's `Env.portBound`): `-EADDRINUSE` exactly at a port a conflicting
socket holds. The function stays unlisted in `correspondence/kcov.json`: its
inlined `maybe_get_net`/`put_net` compare the namespace's reference count,
a value the mirror does not hold, at `include/linux/refcount.h` lines the
refcount decisions own, so its own decisions (`-ENONET`, the two binds, the
IPv6 retry) are not reported [AGENT, a deviation from the design's 4.3].
`wg_socket_reinit` is mirrored with its decisions.
-/

namespace Leanux.WG
open Leanux

/-- sock_free (socket.c:334-340), inlined into wg_socket_reinit:
    `sk_clear_memalloc` and `udp_tunnel_sock_release` are cut points. -/
def sockFree (sock : Option Nat) : M Unit := do
  if ← branch .sockFreeNull sock.isNone then return
  -- udp_tunnel_sock_release -> sock_release (net/socket.c, a cut) ->
  -- iput(SOCK_INODE(sock)): a kernel socket's inode holds its only reference
  iputReport true

/-- wg_socket_reinit (socket.c:419-437): swap the socket pointers, take
    `incoming_port` from the new IPv4 socket, free the old ones.
    `synchronize_net()` (434) does not sleep on this kernel (Tiny RCU,
    `CONFIG_PREEMPT_NONE`; design section 2.2), so it is no `mayHaveSlept`. -/
def socketReinit (new4 new6 : Option Nat) : M Unit := do
  let d ← getDev
  let (old4, old6) := (d.sock4, d.sock6)
  modifyDev fun d => { d with sock4 := new4, sock6 := new6 }
  if ← branch .reinitHasNew4 new4.isSome then
    let some port := new4 | invariant "unreachable"
    modifyDev fun d => { d with incomingPort := port }   -- ntohs(inet_sk(new4)->inet_sport)
  sockFree old4
  sockFree old6

/-- `inet_sk_get_local_port_range` for a kernel socket (no
    `IP_LOCAL_PORT_RANGE`): the netns default `32768..60999`
    (af_inet.c:1803). -/
def LOCAL_PORT_LOW : Nat := 32768
def LOCAL_PORT_HIGH : Nat := 60999

/-- `udp_lib_get_port`'s first candidate for a random port (udp.c:254-258):
    `reciprocal_scale(rand, remaining) + low`. -/
def randomPortFirst (rand : Nat) : Nat :=
  LOCAL_PORT_LOW + (rand * (LOCAL_PORT_HIGH - LOCAL_PORT_LOW + 1)) / 2 ^ 32

/-- wg_socket_init (socket.c:349-417), a cut point (see the module note).
    For port 0 the IPv4 bind draws one `get_random_u32` (udp.c:257, the
    `.udpPortDraw` record) and binds its first candidate; a candidate that a
    conflicting socket holds makes the C step through the UDP hash table
    (a stepping that depends on the boot-time table size), which is outside
    the domain. The IPv6 socket then binds the same port `v6only`, which
    conflicts with no fixture socket at a port the IPv4 bind got. -/
def socketInit (port : Nat) : M Int := do
  let d ← getDev
  -- `creating_net` is NULL only after wg_destruct or wg_netns_pre_exit (W8):
  -- socket.c:377-381, `-ENONET` without maybe_get_net (the function is
  -- unlisted: the arm is data, witnessed by wg_open's error branch)
  if !d.creatingNet then return -ENONET
  let bound := (← get).portBound
  -- wg0's own sockets, bound to the wildcard addresses while running
  let held (p : Nat) : Bool := bound p || d.sock4 == some p || d.sock6 == some p
  let chosen ← do
    if port == 0 then
      let bs ← hidden .udpPortDraw
      let rand := bs.foldr (fun b acc => acc * 256 + b.toNat) 0
      let first := randomPortFirst rand
      if held first then unsupported "the random port draw collides with a bound port"
      pure first
    else
      -- udp_sock_create4 fails: the socket was created, the bind refused,
      -- and udp_sock_create4's error path releases it (sock_release ->
      -- iput, the inode's only reference); pr_err (loglevel 3, no record);
      -- goto out
      if held port then
        iputReport true
        return -EADDRINUSE
      pure port
  -- ipv6_mod_enabled(); the IPv6 socket at `chosen`, v6only: no conflict
  socketReinit (some chosen) (some chosen)
  return 0

/-! ## The peer's endpoint (socket.c:258-314)

Moved here from `Netlink.lean` (W3): `Handshake` sets the endpoint from a
received message and must not import `Netlink`, which imports
`PeerRemove`, which imports `Handshake`. -/

/-! ## W9: the dst cache and `send4`/`send6`
(docs/2026-10-06-w8-w9-netns-routing.md, sections 2.3-2.6, 4.1-4.2)

The cache's hit test is `time_after(refresh_ts, reset_ts)` on two `jiffies`
stores the kernel records (kind 306, `.dstCacheResetTs`, `.dstCacheRefreshTs`),
plus the dst's validity check, which on this fixture is the route
generation (`rt_genid`, the IPv6 sernum). The routing (`World.route4/6`)
and the sockets the datagram leaves by are the environment's; `send4`'s
own choice points are mirrored line by line. -/

/-- `dst_cache_reset` (dst_cache.h:79): `reset_ts = jiffies`, the recorded
    value. Without the arm records the kernel wrote none: outside the domain. -/
def dstCacheReset (pid : PeerId) : M Unit := do
  -- the pre-W9 rule for captures without the records (`World.dstCacheRecords`)
  if !((← getAmbient).armRecords && (← get).dstCacheRecords) then return
  let ts ← hiddenJiffies .dstCacheResetTs
  let p ← getPeer pid
  setPeer pid { p with dstCache := { p.dstCache with resetTs := ts } }

/-- `dst_cache_reset_now` (dst_cache.c:169-185): the reset, then the slot's
    dst released. -/
def dstCacheResetNow (pid : PeerId) : M Unit := do
  dstCacheReset pid
  let p ← getPeer pid
  setPeer pid { p with dstCache := { p.dstCache with slot := none } }

/-- wg_socket_clear_peer_endpoint_src (socket.c:308-314): zeroes `src6`,
    which overlays `src4` and `src_if4`, then `dst_cache_reset_now` (W9:
    the reset's record, the slot dropped). -/
def clearPeerEndpointSrc (pid : PeerId) : M Unit := do
  let p ← getPeer pid
  setPeer pid { p with endpoint := p.endpoint.map fun e => { e with src := 0, srcIf := 0 } }
  dstCacheResetNow pid

/-- endpoint_eq (socket.c:258-271). -/
def endpointEq (a : Endpoint) (b : Option Endpoint) : M Bool := do
  let fb := b.map (·.family) |>.getD 0
  let field (f : Endpoint → Nat) := b.any fun e => f e == f a
  let v4 ← andM (branch .eqA4 (a.family == AF_INET)) (andM (branch .eqB4 (fb == AF_INET))
    (andM (branch .eqPort4 (field (·.port))) (andM (branch .eqAddr4 (field (·.addr)))
      (andM (branch .eqSrc4 (field (·.src))) (branch .eqSrcIf4 (field (·.srcIf)))))))
  if v4 then return true
  let v6 ← andM (branch .eqA6 (a.family == AF_INET6)) (andM (branch .eqB6 (fb == AF_INET6))
    (andM (branch .eqPort6 (field (·.port))) (andM (branch .eqAddr6 (field (·.addr)))
      (andM (branch .eqScope6 (field (·.scope))) (branch .eqSrc6 (field (·.src)))))))
  if v6 then return true
  andM (branch .eqANone (a.family == 0)) (branch .eqBNone (fb == 0))

/-- wg_socket_set_peer_endpoint (socket.c:273-297); `dst_cache_reset`
    (:294) stores the recorded `jiffies` (W9). -/
def setPeerEndpoint (pid : PeerId) (e : Endpoint) : M Unit := do
  requireNotPending pid "changing the endpoint"
  if ← branch .setEndpointEq (← endpointEq e (← getPeer pid).endpoint) then return
  if ← branch .setEndpointV4 (e.family == AF_INET) then
    setPeer pid { (← getPeer pid) with endpoint := some e }
    dstCacheReset pid
  else if ← branch .setEndpointV6 (e.family == AF_INET6) then
    setPeer pid { (← getPeer pid) with endpoint := some e }
    dstCacheReset pid

/-- `dst_cache_per_cpu_get` (dst_cache.c:39-64): a hit needs a cached dst,
    `time_after(refresh_ts, reset_ts)` (the C's macro, `timeAfter`: a
    refresh in the same jiffy as the reset is a miss, review item 8) and a
    dst the check accepts (its generation is the tables'); otherwise the
    slot is dropped and `refresh_ts = jiffies` (the recorded value) is
    stored: the miss. -/
def dstCacheGet (pid : PeerId) (gen : Nat) : M (Option DstSlot) := do
  -- the pre-W9 rule for captures without the records: every access misses
  if !((← getAmbient).armRecords && (← get).dstCacheRecords) then return none
  let p ← getPeer pid
  let c := p.dstCache
  if let some s := c.slot then
    if timeAfter c.refreshTs c.resetTs && s.gen == gen then return some s
  let ts ← hiddenJiffies .dstCacheRefreshTs
  setPeer pid { p with dstCache := { c with slot := none, refreshTs := ts } }
  return none

/-- `dst_cache_set_ip4`/`_ip6`: the route and its source, made in the
    tables' current generation. -/
def dstCacheSet (pid : PeerId) (src gen dev : Nat) : M Unit := do
  let p ← getPeer pid
  setPeer pid { p with dstCache := { p.dstCache with slot := some { src, gen, dev } } }

/-- The UDP tunnel transmit at the end of `send4`/`send6` (socket.c:85, :152):
    the IP output's cut-site records and, over `lo`, the NET_RX softirq
    nested at the send (`loopbackSend`); a datagram routed into wg0 re-enters
    `wg_xmit`, outside the domain until W9-R. `exactRx`: E's cookie-reply
    path keeps its lax NET_RX cut. The datagram goes to `World.sent` with the
    source the route gave; the environment delivers it. -/
private def tunnelXmit (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) : M Unit := do
  if r.dev == WG0_IFINDEX then unsupported "a datagram routed back into wg0"
  if exactRx then loopbackSend ([.ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts) true
  else skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx]
  -- iptunnel_xmit_stats: the device tstats (W5, 2.6)
  modifyDev fun d => { d with txPackets := d.txPackets + 1, txBytes := d.txBytes + bytes.length }
  let sport ← socketPort e.family
  modify fun w => { w with sent := w.sent ++ [{ family := e.family, addr := e.addr, port := e.port, bytes, ds, sport, src := r.src }] }

/-- send4 (socket.c:20-95). `cache`: the peer's `endpoint_cache`
    (`wg_socket_send_skb_to_peer`), or none (the reply path). Returns the
    C's result: 0 once the datagram left (whatever the transmit did), the
    route's error, `-ENONET` without a socket. -/
def send4 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) : M Int := do
  let d ← getDev
  if ← branch .send4SockNull d.sock4.isNone then return -ENONET   -- err: kfree_skb
  let gen := (← Net.Fib.inSocketNs Net.Fib.getTable).rtGenid4   -- lane C: `rt_genid` (rt_cache_valid, route.c:1602-1607)
  let mut saddr := e.src
  let mut srcIf := e.srcIf
  let mut route : Option Route := none
  -- `endpoint` is the peer's own (`&peer->endpoint`) when sent with its
  -- cache; the reply path's is a stack copy
  let clearSrc : M Unit := do
    if let some pid := cache then
      let p ← getPeer pid
      setPeer pid { p with endpoint := p.endpoint.map fun e => { e with src := 0, srcIf := 0 } }
  if ← branch .send4HasCache cache.isSome then
    let some pid := cache | invariant "unreachable"
    if let some s ← dstCacheGet pid gen then
      route := some { dev := s.dev, src := s.src }; saddr := s.src   -- dst_cache_get_ip4 writes fl.saddr
  if ← branch .send4CacheMiss route.isNone then
    -- inet_confirm_addr(net, NULL, 0, fl.saddr, RT_SCOPE_HOST): a zero source
    -- autoselects; a set one must be a configured address (devinet.c:1433)
    let w ← getRouting
    let confirmed := saddr == 0 || saddr == LOOPBACK4 || w.addrs4.contains saddr
    if ← branch .send4SrcNotLocal !confirmed then
      clearSrc; saddr := 0; srcIf := 0
      if ← branch .send4ResetA cache.isSome then dstCacheReset cache.get!
    let mut rt ← Net.Fib.inSocketNs (Net.routeLookup 4 saddr e.addr)
    let mismatch := srcIf != 0 && (match rt with
      | .error err => err == -EINVAL
      | .ok r => r.dev != srcIf)
    if ← branch .send4SrcIfMismatch mismatch then
      clearSrc; saddr := 0; srcIf := 0
      if ← branch .send4ResetB cache.isSome then dstCacheReset cache.get!
      if ← branch .send4PutRt (match rt with | .ok _ => true | .error _ => false) then pure ()   -- ip_rt_put
      rt ← Net.Fib.inSocketNs (Net.routeLookup 4 0 e.addr)
    match rt with
    | .error err =>
      if ← branch .send4RouteErr true then return err   -- net_dbg_ratelimited; err: kfree_skb
    | .ok r =>
      _ ← branch .send4RouteErr false
      if ← branch .send4CacheSet cache.isSome then dstCacheSet cache.get! r.src gen r.dev
      route := some r
  let some r := route | invariant "send4 without a route"
  -- lane C: `ip_finish_output2` on the route's device: its one neighbour
  Net.Fib.inSocketNs (Net.neighbourClassify r.dev)
  tunnelXmit e bytes ds r exactRx
  return 0

/-- send6 (socket.c:97-166), as `send4` without the `src_if` arm; the scope
    (`flowi6_oif`) is the endpoint's, which the mirror already refuses when
    set (`endpointFromSkb`). -/
def send6 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) : M Int := do
  let d ← getDev
  if ← branch .send6SockNull d.sock6.isNone then return -ENONET
  let gen := (← getRouting).ipv6Gen
  let mut saddr := e.src
  let mut route : Option Route := none
  if ← branch .send6HasCache cache.isSome then
    let some pid := cache | invariant "unreachable"
    if let some s ← dstCacheGet pid gen then
      route := some { dev := s.dev, src := s.src }; saddr := s.src
  if ← branch .send6CacheMiss route.isNone then
    -- !ipv6_addr_any(saddr) && !ipv6_chk_addr(net, saddr, NULL, 0)
    let w ← getRouting
    let notLocal := saddr != 0 && !(saddr == 1 || saddr == LO_LINK_LOCAL || w.addrs6.contains saddr)   -- W5: the link-local address on lo
    if ← branch .send6SrcNotLocal notLocal then
      if let some pid := cache then
        let p ← getPeer pid
        setPeer pid { p with endpoint := p.endpoint.map fun e => { e with src := 0 } }
      saddr := 0
      if ← branch .send6Reset cache.isSome then dstCacheReset cache.get!
    match ← Net.routeLookup 6 saddr e.addr with
    | .error err =>
      if ← branch .send6RouteErr true then return err
    | .ok r =>
      _ ← branch .send6RouteErr false
      if ← branch .send6CacheSet cache.isSome then dstCacheSet cache.get! r.src gen r.dev
      route := some r
  let some r := route | invariant "send6 without a route"
  tunnelXmit e bytes ds r exactRx
  return 0

end Leanux.WG
