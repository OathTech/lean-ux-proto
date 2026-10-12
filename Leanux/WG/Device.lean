import Leanux.WG.Netlink

/-!
# drivers/net/wireguard/device.c — bringing wg0 up and transmitting

`wg_up` is `dev_change_flags(wg0, flags | IFF_UP)`, which sets
`__LINK_STATE_START` and calls `wg_open`; `wg_down` clears it and calls
`wg_stop`. `wg_socket_init` (`Leanux/WG/Socket.lean`) binds the UDP sockets
on `incoming_port`, or a random port for 0.

L (docs/2026-10-05-l-lifecycle.md): creation (`wg_setup`, `wg_newlink`, from
`RTM_NEWLINK`) and deletion (`wg_stop` if up, then `wg_destruct`, from
`RTM_DELLINK`). The rtnetlink and `net/core/dev.c` core around them is a cut:
the mirror enters at the WireGuard callbacks, with the core's `-EEXIST` and
`-ENODEV` as outcomes.

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
    device (its MTU of 1420 admits both at registration) until an MTU change
    takes one down (W4: `Device.inet4Dev`, `inet6Dev`). -/
def wgOpen : M Int := do
  let dev ← getDev
  _ ← branch .openHasInet dev.inet4Dev    -- IN_DEV_CONF_SET(SEND_REDIRECTS, false)
  _ ← branch .openHasInet6 dev.inet6Dev   -- addr_gen_mode = IN6_ADDR_GEN_MODE_NONE
  let d ← getDev
  -- mutex_lock(&wg->device_update_lock); wg_socket_init on incoming_port
  let ret ← socketInit d.incomingPort
  if ← branch .openSocketError (ret < 0) then return ret   -- goto out
  for pid in d.peerList do
    _ ← branch .openPeersIter true
    sendStagedPackets pid
    if ← branch .openKeepalive ((← getPeer pid).persistentKeepaliveInterval != 0) then sendKeepalive pid
  _ ← branch .openPeersIter false
  return 0

/-- `dev_change_flags` to IFF_UP: `__dev_open` (dev.c:1519-1566) sets
    `__LINK_STATE_START` before `ndo_open`, and clears it again when
    `ndo_open` fails (the flags stay down). The routes added after it are
    fixture. -/
def wgUp : M Int := do
  modifyDev fun d => { d with running := true }
  let ret ← wgOpen
  if ret < 0 then modifyDev fun d => { d with running := false }
  return ret

/-! ## L: wg_stop, creation and deletion -/

/-- wg_stop (device.c:115-135), with `__LINK_STATE_START` already clear
    (`__dev_close_many`, dev.c:1612). The encrypt, decrypt and tx queues
    are not purged; the environment excludes work still queued there. -/
def wgStop : M Unit := do
  -- mutex_lock(&wg->device_update_lock)
  for pid in (← getDev).peerList do
    _ ← branch .stopPeersIter true
    -- the handshake send work stays queued across wg_stop; when it runs is
    -- not determined
    requireNotPending pid "wg_stop while a handshake is queued"
    purgeStagedPackets pid
    timersStop pid
    handshakeClear pid
    keypairsClear pid
    resetLastSentHandshake pid
  _ ← branch .stopPeersIter false
  -- `while ((skb = ptr_ring_consume(&wg->handshake_queue.ring)) != NULL)`:
  -- a message queued for a receive worker that has not run
  if !(← getDev).handshakeQueue.isEmpty then
    unsupported "wg_stop with handshake messages queued for the receive worker (its timing)"
  _ ← branch .stopDrainIter false
  modifyDev fun d => { d with handshakeQueue := [] }   -- atomic_set(&wg->handshake_queue_len, 0)
  socketReinit none none

/-- `dev_change_flags` without IFF_UP on an up device: `__dev_close_many`
    clears `__LINK_STATE_START`, then `ndo_stop`. -/
def wgDown : M Unit := do
  modifyDev fun d => { d with running := false }
  wgStop

/-- The ratelimiter's `table_size` (ratelimiter.c:173-177), sized from
    `totalram_pages()`: 2048 buckets for the fixture's 256 MB guest
    (an environment fact; docs/2026-10-05-l-lifecycle.md, section 2.1). -/
def RATELIMITER_TABLE_SIZE : Nat := 2048

/-- wg_ratelimiter_init (ratelimiter.c:158-203). The slab cache and the
    tables are allocation sites (A's domain); the GC work it queues runs on
    `system_power_efficient_wq` outside every section, reading no table
    entry on the modeled paths (a cut). -/
def ratelimiterInit : M Int := do
  -- mutex_lock(&init_lock); `++init_refcnt != 1`
  modifyK fun k => { k with ratelimiter := { k.ratelimiter with refcnt := k.ratelimiter.refcnt + 1 } }
  let undo : M Int := do   -- err: --init_refcnt
    modifyK fun k => { k with ratelimiter := { k.ratelimiter with refcnt := k.ratelimiter.refcnt - 1 } }
    return -ENOMEM
  if ← branch .ratelimiterInitNotFirst ((← getK).ratelimiter.refcnt != 1) then return 0
  if ← branch .ratelimiterInitCacheErr !(← envOk .ratelimiterCache) then return ← undo
  if ← branch .ratelimiterInitTableV4Err !(← envOk .ratelimiterTable) then return ← undo
  if ← branch .ratelimiterInitTableV6Err !(← envOk .ratelimiterTable) then return ← undo
  -- queue_delayed_work(system_power_efficient_wq, &gc_work, HZ)
  let key ← hidden .ratelimiterKey
  modifyK fun k => { k with ratelimiter := { k.ratelimiter with key } }
  return 0

/-- wg_ratelimiter_gc_entries (ratelimiter.c:55-83) on the empty tables of the
    modeled paths (an entry is made only under load, E's domain, which
    extends this walk with entries). `work` is NULL on the uninit path: its
    clock read's value is unused there. -/
def gcEntries (work : Bool) : M Unit := do
  let _now ← hiddenClock .ratelimiterGcNow
  -- The buckets are alike (all empty), so the first iteration's outcomes are
  -- reported and the rest evaluated silently: a repeatable decision's
  -- outcomes are a set per operation in the check, and the report of a
  -- trace is bounded (4096 branches, evaluator/protocol.py).
  for i in [0:RATELIMITER_TABLE_SIZE] do
    let report (dec : Decision) (outcome : Bool) : M Bool :=
      if i == 0 then branch dec outcome else pure outcome
    _ ← report .gcBucketIter true
    -- hlist_for_each_entry_safe over table_v4[i], then table_v6[i]: empty
    _ ← report .gcV4EntryIter false
    _ ← report .gcV6EntryIter false
    if ← report .gcHasWork work then unsupported "the ratelimiter GC's cond_resched (a work run)"
  _ ← branch .gcBucketIter false
  if ← branch .gcRequeue work then unsupported "the ratelimiter GC re-queuing itself (a work run)"

/-- wg_ratelimiter_uninit (ratelimiter.c:205-221). -/
def ratelimiterUninit : M Unit := do
  -- mutex_lock(&init_lock); `!init_refcnt || --init_refcnt`
  let r := (← getK).ratelimiter.refcnt
  if ← branch .ratelimiterUninitZero (r == 0) then return
  modifyK fun k => { k with ratelimiter := { k.ratelimiter with refcnt := r - 1 } }
  if ← branch .ratelimiterUninitNotLast (r - 1 != 0) then return
  -- cancel_delayed_work_sync(&gc_work): waits only for a GC run in progress,
  -- which reads and changes nothing the mirror holds (empty tables)
  gcEntries false
  mayHaveSlept   -- rcu_barrier()
  -- the tables and the cache are freed (cuts); `key` stays, unused

/-- wg_setup (device.c:274-307): the net_device's ops, type, flags and MTU
    (constants of the mirror: `DEVICE_MTU`), then `memset(wg, 0)`. The
    rtnetlink core (`rtnl_create_link`, rtnetlink.c:3499-3515) allocated it
    with the name "wg0" and `ifi_index` 0. -/
def wgSetup : M Unit :=
  modifyK fun k => { k with wg := some { ifindex := 0, ifname := "wg0", creatingNet := false, deviceUpdateGen := 0 } }

/-- wg_cookie_checker_init (cookie.c:19-26). -/
def cookieCheckerInit : M Unit := do
  let birthdate ← hiddenClock .cookieSecretBirthdate
  let secret ← hidden .cookieSecret
  modifyDev fun d => { d with cookieSecretBirthdate := birthdate, cookieSecret := secret }

/-- wg_pubkey_hashtable_alloc (peerlookup.c:22-33): `kvmalloc`, then the
    siphash key. Its `if (!table)` is an allocation outcome in an unlisted
    function (A's domain). -/
def pubkeyHashtableAlloc : M Bool := do
  if !(← envOk .pubkeyHashtableAlloc) then return false
  let key ← hidden .pubkeyHashKey
  modifyDev fun d => { d with pubkeyHashKey := key }
  return true

/-- wg_newlink (device.c:309-400), on the device `wgSetup` made. The
    unwinding arms (381-399) follow allocation failures, A's domain:
    reported, then outside the domain. -/
def wgNewlink : M Int := do
  let unwind : M Int := unsupported "wg_newlink's unwinding after an allocation failure"
  modifyDev fun d => { d with creatingNet := true }   -- rcu_assign_pointer(wg->creating_net, src_net)
  -- wg_allowedips_init: empty tries, seq 1 (the fresh device's)
  cookieCheckerInit
  modifyDev fun d => { d with deviceUpdateGen := 1 }
  if ← branch .newlinkPeerHashtableErr !(← pubkeyHashtableAlloc) then return -ENOMEM
  if ← branch .newlinkIndexHashtableErr !(← envOk .indexHashtableAlloc) then return ← unwind
  -- three alloc_workqueue: only packet_crypt_wq (WQ_MEM_RECLAIM) gets a
  -- rescuer, whose kthread_create the task waits for (a sleep point)
  if ← branch .newlinkRecvWqErr !(← envOk .allocWorkqueue) then return ← unwind
  if ← branch .newlinkSendWqErr !(← envOk .allocWorkqueue) then return ← unwind
  let crypt ← envOk .allocWorkqueue
  mayHaveSlept
  if ← branch .newlinkCryptWqErr !crypt then return ← unwind
  if ← branch .newlinkEncryptQueueErr !(← envOk .packetQueueInit) then return ← unwind
  if ← branch .newlinkDecryptQueueErr !(← envOk .packetQueueInit) then return ← unwind
  if ← branch .newlinkHandshakeQueueErr !(← envOk .packetQueueInit) then return ← unwind
  let ret ← ratelimiterInit
  if ← branch .newlinkRatelimiterErr (ret < 0) then return ← unwind
  -- register_netdevice: the ifindex (the netns cursor, dev.c:10000-10018),
  -- then NETDEV_REGISTER, whose inetdev_init and ipv6_add_dev each draw a
  -- neighbour parms' reachable time (a cut: unobserved)
  let ok ← envOk .registerNetdevice
  if ← branch .newlinkRegisterErr !ok then return ← unwind
  let ifindex := (← getK).netIfindexNext
  modifyK fun k => { k with netIfindexNext := ifindex + 1 }
  modifyDev fun d => { d with ifindex }
  skipCutExactly .neighReachTime 2
  -- list_add(&wg->device_list, &device_list); priv_destructor = wg_destruct
  return 0

/-- `RTM_NEWLINK` of "wg0" (rtnetlink.c:3716-3791, 3581-3671): an existing
    device with `NLM_F_EXCL` is `-EEXIST` before any WireGuard code; else
    `wg_setup` and `wg_newlink`. A failed `newlink` frees the device. -/
def wgCreate : M Int := do
  if (← getK).wg.isSome then return -EEXIST
  wgSetup
  let ret ← wgNewlink
  if ret < 0 then modifyK fun k => { k with wg := none }
  return ret

/-- wg_destruct (device.c:242-270), from `netdev_run_todo`. -/
def wgDestruct : M Unit := do
  -- list_del(&wg->device_list) under rtnl; mutex_lock(&wg->device_update_lock)
  modifyDev fun d => { d with creatingNet := false, incomingPort := 0 }
  socketReinit none none
  peerRemoveAll
  -- destroy_workqueue ×3: drain_workqueue runs what is still queued (work
  -- the environment excludes), then the rescuer's kthread_stop (a sleep)
  let d ← getDev
  if !d.sendWorkQueue.isEmpty || !d.encryptQueue.isEmpty || !d.txWorkQueue.isEmpty
      || !d.decryptQueue.isEmpty || !d.clearWorkQueue.isEmpty then
    unsupported "wg_destruct with queued work (destroy_workqueue runs it)"
  mayHaveSlept
  -- wg_packet_queue_free: the handshake ring is purged; the crypt rings are
  -- empty (WARN_ON otherwise)
  modifyDev fun d => { d with handshakeQueue := [] }
  mayHaveSlept   -- rcu_barrier()
  ratelimiterUninit
  -- memzero_explicit(&wg->static_identity); kvfree ×2; free_netdev
  modifyK fun k => { k with wg := none }

/-- `RTM_DELLINK` of "wg0" (rtnetlink.c:3383-3436): `-ENODEV` without one;
    else `unregister_netdevice_many_notify` (dev.c:11493-): `dev_close_many`
    runs `wg_stop` for an up device; then `flush_all_backlogs` (a sleep
    point), the notifiers, and `netdev_run_todo` (its `rcu_barrier`, a sleep
    point), which calls `wg_destruct`. -/
def wgDelete : M Int := do
  if (← getK).wg.isNone then return -ENODEV
  if (← getDev).running then wgDown
  mayHaveSlept
  wgDestruct
  return 0

/-- wg_xmit (device.c:137-233) for a datagram to `addr` (family 4 or 6):
    the IP packets `pkts` the environment's sender hands it (one, or the
    segments of a GSO skb, two or more; W4) and `mtu`, the `dst_mtu` of the
    datagram's route (device.c:173; `Env.xmitPackets`). -/
def wgXmit (family addr : Nat) (pkts : List Packet) (mtu : Nat) : M Int := do
  -- `real_protocol && skb->protocol == real_protocol`
  let ok ← andM (branch .checkProtoParsed true) (branch .checkProtoMatches true)
  if ← branch .xmitBadProtocol !ok then unsupported "unreachable"
  let err (ret : Int) : M Int := do
    -- err_icmp: icmp_ndo_send / icmpv6_ndo_send (cut points, whose rate limit
    -- and IP output draw cut-site choices), then err. The error is sent iff
    -- the rate limits allowed it, and then `icmp_global_consume` drew
    -- (icmp.c:310-339, ipv6/icmp.c:195-238: type 3 / type 1 is in the
    -- default ratemask, wg0 is not loopback, the reply's route is local);
    -- the ICMP's loopback delivery raises NET_RX, whose section runs at
    -- `__dev_queue_xmit`'s `rcu_read_unlock_bh` (`loopbackSend`).
    if !(← branch .xmitErrorInet (family == 4)) then _ ← branch .xmitErrorInet6 (family == 6)
    let drawn ← skipCutSites ([.icmpCredit, .ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts)
    loopbackSend [] (drawn.contains (HiddenSite.icmpCredit).info.id)
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
  -- `if (!skb_is_gso(skb))` (device.c:176): a GSO skb arrives as its segments
  if !(← branch .xmitNotGso (pkts.length < 2)) then
    -- skb_gso_segment(skb, 0) (device.c:179-186): `IS_ERR(segs)` only when
    -- an allocation inside skb_segment fails (A's domain, `envOk`)
    if ← branch .xmitGsoError !(← envOk .skbSegment) then
      peerPut peer   -- err_peer
      return ← err (-ENOMEM)
  -- skb_list_walk_safe (device.c:189-204): every packet of the list gets
  -- the one `mtu` of this call
  let mut packets : List Packet := []
  for pkt in pkts do
    _ ← branch .xmitWalk true
    _ ← branch .xmitShareFailed false
    packets := packets ++ [{ pkt with mtu }]
  _ ← branch .xmitWalk false
  -- `while (skb_queue_len(&peer->staged_packet_queue) > MAX_STAGED_PACKETS)`
  -- (device.c:211-214): the oldest packets go, one `tx_dropped` each, before
  -- the new ones are spliced (W4: the trim)
  for _ in [0:(← getPeer pid).staged.length + 1] do
    let p ← getPeer pid
    if ← branch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS) then
      setPeer pid { p with staged := p.staged.drop 1 }
      modifyDev fun d => { d with txDropped := d.txDropped + 1 }
    else break
  setPeer pid { (← getPeer pid) with staged := (← getPeer pid).staged ++ packets }   -- skb_queue_splice_tail
  sendStagedPackets pid
  peerPut peer
  return 0   -- NETDEV_TX_OK

/-! ## W4: `SIOCSIFMTU` (docs/2026-10-06-w4-w7-transmit-bulk.md, section 4) -/

/-- `dev->max_mtu` (device.c:297): `round_down(INT_MAX, MESSAGE_PADDING_MULTIPLE)
    - overhead`, the overhead being 32 + 8 + 40. -/
def MAX_MTU : Nat := 2147483647 / 16 * 16 - 80

/-- `dev_set_mtu` (net/core/dev.c:9085-9122) of wg0, a cut: `dev_validate_mtu`
    refuses above `max_mtu` (`-ERANGE`; wg sets no `min_mtu`, so 0 is
    accepted), `__dev_set_mtu` writes `dev->mtu`, and `NETDEV_CHANGEMTU`'s
    notifiers take the `inet6_dev` down below 1280 (addrconf.c:3691-3695)
    and the `in_device` down below 68 (devinet.c:1637-1643); a later valid
    MTU re-creates each, empty. -/
def setMtu (mtu : Nat) : M Int := do
  if mtu > MAX_MTU then return -ERANGE
  modifyDev fun d => { d with mtu, inet6Dev := mtu ≥ 1280, inet4Dev := mtu ≥ 68 }
  return 0

/-! ## W8: the creating namespace's exit (docs/2026-10-06-w8-w9-netns-routing.md, 3.3) -/

/-- wg_netns_pre_exit (device.c:409-428), run by `cleanup_net` for the
    creating namespace C: over `device_list` (the fixture's one device, or
    none after a `wg_delete`), the device whose `creating_net` is C loses its
    carrier (`netif_carrier_off`, whose linkwatch event is W8b's), its
    `creating_net`, its sockets (`wg_socket_reinit(NULL, NULL)`) and every
    peer's endpoint source. -/
def netnsPreExit : M Unit := do
  -- rtnl_lock(); list_for_each_entry(wg, &device_list, device_list)
  if (← getK).wg.isSome then
    _ ← branch .preExitDevIter true
    if ← branch .preExitCreator (← getDev).creatingNet then
      -- netif_carrier_off(wg->dev); mutex_lock(&wg->device_update_lock);
      -- rcu_assign_pointer(wg->creating_net, NULL)
      modifyDev fun d => { d with carrier := false, creatingNet := false }
      socketReinit none none
      for pid in (← getDev).peerList do
        _ ← branch .preExitPeerIter true
        clearPeerEndpointSrc pid
      _ ← branch .preExitPeerIter false
  _ ← branch .preExitDevIter false

end Leanux.WG
