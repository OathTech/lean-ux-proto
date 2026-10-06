# W8 + W9: netns exit, `-ENONET`/`-EPERM`, and `socket.c` routing — design, 2026-10-06

Status: **proposed** [AGENT], for the user's decisions in section 11. The
direction is the user's [USER 2026-10-06]: 100% of reasonable single-CPU
WireGuard; exclusions only for profound reasons. The two workstreams are rows
W8 and W9 of the [coverage census](2026-10-06-wireguard-census.md).

Base: the integrated tip of D3 (`task/d3-int`), L (`task/l-m`), A and E — W8
builds on L's lifecycle (the bare fixture, `socketInit`, `creatingNet`,
`rtnetlinkRequest`) and D3's sections and timers; W9 builds on D2/D3's send
path (`sendBufferToPeer`, `sendSkbToPeer`, `loopbackSend`) and on E's
reply-to-skb path. Line numbers are in the unpatched `.deps/linux`
(6.12.110); the kernel is `kernel/config-x86_64-net-choice`: one CPU,
`PREEMPT_NONE` (`:111`), `HZ=250` (`:335`, a 4 ms tick), `NET_NS=y` (`:161`),
no `USER_NS` (`:159`), no `IP_ADVANCED_ROUTER` (`:687`, so no
`IP_MULTIPLE_TABLES` and no fib rules), no `IPV6_MULTIPLE_TABLES` (`:724`), no
`IP_MULTICAST` (`:686`), no `NET_L3_MASTER_DEV` (`:761`), no `SECURITY`
(`:1570`), `IPV6_SIT=y` (`:720`).

Nothing in this note was run: no build, no VM. Every kernel claim carries its
file:line; the ones inferred rather than read are listed in section 12 for
the two Linux-only probes (section 10) to settle before any mirror code.

**Summary of what the design needs.** W8 needs **no kernel change**: a second
network namespace in the fixture, one operation, two more armed dispatch
symbols (`cleanup_net`, `linkwatch_event`), and the parent process pinning the
child's namespace across the disarm. W9 needs **one small kernel change**: a
record of `jiffies` at the two places the dst cache stores it (section 4.1),
because the cache's hit/miss decision is a `jiffies` comparison the mirror
cannot otherwise compute. Without it W9's cache decision is fail-open, which
the project's rules forbid without explicit authorization.

## 1. Targets

| # | Scope item | C entry | Observable through |
|---|---|---|---|
| W8.1 | the creating namespace exits while `wg0` lives on in another | `cleanup_net` (`net_namespace.c:595-677`) → `ops_pre_exit_list` (`:631-632`) → `wg_netns_pre_exit` (`device.c:409-428`) | the dispatch section of `cleanup_net`; `IFF_LOWER_UP` cleared in the link flags (new observable); everything below |
| W8.2 | `wg_socket_init` without a creating namespace | `socket.c:376-381` → `-ENONET` | `wg_up`'s `ioctl` errno (`ENONET`, device stays down); `wg_set` of `listen_port` while running |
| W8.3 | `wg_set_device` of `listen_port`/`fwmark` without a creating namespace | `netlink.c:513-521` → `-EPERM` | the ACK |
| W8.4 | `send4`/`send6` with a NULL socket (the device up, its sockets released by the exit) | `socket.c:41-44`, `:121-124` → `-ENONET` | the dump's `tx_bytes` unchanged; no datagram; no `wg_timers_data_sent` arm record (`send.c:251-256`) |
| W8.5 | carrier off → linkwatch → the queue deactivated | `device.c:418`; `link_watch.c:179-186` | the dispatch section of `linkwatch_event`; afterwards `sendto` into `wg0` succeeds and `wg_xmit` never runs (section 2.2) |
| W9.1 | `send4`/`send6` as mirrored decisions | `socket.c:20-95`, `:97-166` | coverage (A2); the datagram's source address at the sender's `recvfrom` (already printed, `guest.c:575-600`); `tx_bytes` |
| W9.2 | the dst cache: hit or miss, resets, staleness | `dst_cache.c:39-64`, `include/net/dst_cache.h:77-80`; `socket.c:49,59,69,81,129,137,148,294,312`; `peer.c:36` | coverage of `socket.c:51`/`:131` and the arms only a miss runs |
| W9.3 | the cached source address no longer local | `socket.c:53-60` (`inet_confirm_addr`, `devinet.c:1470-1491`), `:133-138` (`ipv6_chk_addr`, `addrconf.c:1961-1966`) | the reply's source address at the sender |
| W9.4 | route lookup errors | `socket.c:61,74-79`, `:139-146`; `route.c:2714`, `ipv6/route.c:298` | `tx_bytes` unchanged; no datagram |
| W9.5 | an endpoint routed back into `wg0`: `wg_xmit` nested at the send | `socket.c:85` → `udp_tunnel_xmit_skb` → `dev_queue_xmit(wg0)` → `wg_xmit` (`device.c:141-234`) | `tx_errors` (`:231`); coverage of the nested `wg_xmit` inside the worker's section; today `unsupported "a datagram routed back into wg0"` (`Env.lean:217`) |
| W9.6 | `src_if4` mismatch; `-EINVAL` from a bad source | `socket.c:62-73` | **stretch** (section 8): needs a non-local source or a multicast local address in the fixture |
| W9.7 | fwmark-dependent routing | `socket.c:27,36,105,116` | **unreachable on this config** (no fib rules: `IP_ADVANCED_ROUTER` unset); the mark reaches `skb->mark` only, which nothing observes |

## 2. The kernel paths, verified

### 2.1 `creating_net`, and how a namespace exits

`creating_net` is set once, in `wg_newlink` (`device.c:316`), to the
`src_net` argument, which `rtnl_newlink_create` passes as `link_net ?: net`
(`rtnetlink.c:3635`) — the **rtnetlink socket's** namespace (`:3588`), not
the namespace the device is created into (`dest_net`, from `IFLA_NET_NS_FD`
via `get_net_ns_by_fd`, `:2452-2453`, `net_namespace.c:723-737`; the device is
allocated there, `:3625`). It is read in three places: `wg_socket_init`
(`socket.c:377`, with `maybe_get_net`), `wg_set_device` (`netlink.c:516`) and
`wg_netns_pre_exit` (`device.c:416`); it is cleared by `wg_destruct`
(`:250`) and by `wg_netns_pre_exit` (`:420`). **No reference is taken**: the
pointer is RCU-published, and the UDP sockets `wg_socket_init` creates in
that namespace are kernel sockets (`udp_tunnel_core.c:18`, `sock_create_kern`),
which hold no `ns.count` reference (`sock.c:2245-2250`: `sk_net_refcnt = kern ?
0 : 1`, the passive count otherwise). So the creating namespace can reach a
zero count while `wg0` is alive elsewhere; that is what `pre_exit` is for.

**The exit.** The last `put_net` runs `__put_net` (`net_namespace.c:697-703`):
`llist_add` to `cleanup_list` and `queue_work(netns_wq, &net_cleanup_work)`
(`:701-702`), where `netns_wq` is `create_singlethread_workqueue("netns")`
(`:1200`) — an ordered unbound workqueue, so **`cleanup_net` is dispatched by
`process_one_work`** and opens a section under the common handle iff
`cleanup_net` is in the armed dispatch set (choice-stream strategy, section
4.3-4.4). `cleanup_net` (`:595-677`), in order: snapshot the list (`:604`);
`down_read(&pernet_ops_rwsem)` (`:606`); `down_write(&net_rwsem)`, unlink,
`up_write` (`:609-623`); `unhash_nsid` per namespace (`:625-628`;
`rtnl_net_notifyid(..., GFP_KERNEL)` at `:583`, a broadcast to no listener);
**`ops_pre_exit_list` for every pernet op, in reverse registration order**
(`:631-632`) — here `wg_netns_pre_exit` (`pernet_ops`, `device.c:430-432`,
registered by `register_pernet_device` at `:446`); `synchronize_rcu_expedited`
(`:640`; no sleep on Tiny RCU); `rtnl_lock`, the `exit_batch_rtnl` ops and
`unregister_netdevice_many` of the namespace's devices (`:642-648`: its `lo`
and `sit0`); the `exit` ops (`:651-652`); the `free` ops (`:655-656`);
`rcu_barrier` (`:663`, a sleep); the frees (`:668-676`).

So on the path from the section's start to `wg_netns_pre_exit` there is no
sleep (two uncontended rwsems, one `GFP_KERNEL` broadcast that sleeps only
under reclaim), and the sleeps come after it (`rcu_barrier` at `:663`, and
`netdev_run_todo`'s barriers for the two devices after `rtnl_unlock` at
`:648`). Whether a reschedule record lands inside the section before
`wg_netns_pre_exit`'s decisions is a probe item (section 10).

**`wg_netns_pre_exit`** (`device.c:409-428`): `rtnl_lock` (`:414`); for each
device of `device_list` (`:415`) whose `creating_net` is the exiting
namespace (`:416`): `netif_carrier_off` (`:418`), `creating_net = NULL`
under `device_update_lock` (`:419-420`), **`wg_socket_reinit(wg, NULL,
NULL)`** (`:421`; `socket.c:419-437`: the sockets swapped out,
`incoming_port` kept, `synchronize_net` without a sleep (L, section 2.2),
`sock_free` ×2 → `udp_tunnel_sock_release`, `udp_tunnel_core.c:181-187`,
`synchronize_rcu` without a sleep), and for each peer
**`wg_socket_clear_peer_endpoint_src`** (`:422-423`; `socket.c:308-314`: the
source union zeroed, `dst_cache_reset_now`, `dst_cache.c:169-185`). The
device stays registered, up or down as it was, with its peers, keys and
`incoming_port`.

**When it runs relative to the trace.** The work is queued inside the
syscall that drops the last reference (section 3.2 chooses `close` of a
namespace descriptor: `nsfs` → `netns_put` → `put_net`). On one CPU the
kworker runs when the trace process gives up the CPU: at the latest in the
operation's guest wait (`usleep`), possibly earlier at the syscall's return
to user space if the wakeup preempts (EEVDF's wakeup preemption; the kernel
is not preemptible, but a return to user space is a scheduling point).
Either way the section lands **inside the operation's window, before its
readout**, provided the wait is long enough for the whole of `cleanup_net`
(a few milliseconds: two `rcu_barrier`s on Tiny RCU and the unregistration
of two devices; measured by the probe). The record order places it exactly;
the mirror consumes the section where its start record is (section 3.4).

### 2.2 What the exit leaves behind

- **`wg_socket_init` → `-ENONET`** (`socket.c:376-381`): `creating_net`
  NULL at `:377` makes the ternary at `:378` skip `maybe_get_net`, and
  `:380` returns `-ENONET` (the only way to reach that arm: L, section 2.5).
  Reached by `wg_open` (`device.c:51`: the `ioctl` fails with `ENONET`,
  `__dev_open` clears `__LINK_STATE_START` and leaves `IFF_UP` clear,
  `dev.c:1556-1557`) and by `set_port` on a running device
  (`netlink.c:326`). The other arm — `creating_net` still set but the
  count already zero, so `maybe_get_net` (`net_namespace.h:267-275`,
  `refcount_inc_not_zero`) fails — is the window between `__put_net` and
  `cleanup_net`'s `pre_exit`; section 3.2's wait closes it, and it is
  declared out of scope (section 8).
- **`wg_set_device` → `-EPERM`** (`netlink.c:513-521`): with
  `WGDEVICE_A_LISTEN_PORT` or `WGDEVICE_A_FWMARK` present, `ret = !net ||
  !ns_capable(net->user_ns, CAP_NET_ADMIN) ? -EPERM : 0` (`:517`), before
  `device_update_gen++` (`:523`), so nothing changes. **The capability half
  is constant true on this config**: without `USER_NS` every namespace's
  `user_ns` is `init_user_ns`, `ns_capable` is `cap_capable`
  (`commoncap.c:67-79`: `ns == cred->user_ns` → `cap_raised`), and the
  operation already passed the family's `GENL_UNS_ADMIN_PERM` check
  (`netlink.c:616,620`; `genetlink.c:1187-1189`: `netlink_ns_capable(skb,
  net->user_ns, CAP_NET_ADMIN)`) with the same credential. A non-root trace
  would be refused at `genetlink.c:1188`, in an unanchored file, before any
  WireGuard code. So the decision at `:517` has one live operand, `!net`,
  and the `||` short-circuits past `ns_capable` when it is taken. Other
  `wg_set` content (keys, peers, flags) is unaffected; a peer added with an
  endpoint and a keepalive on a running device reaches `send4`'s `-ENONET`
  through `wg_packet_send_keepalive`.
- **`send4`/`send6` → `-ENONET`** (`socket.c:41-44`, `:121-124`): the
  sockets are NULL only after `pre_exit` on a running device (`wg_stop`
  also NULLs them, `device.c:133`, but with `__LINK_STATE_START` clear and
  the routes gone nothing reaches `wg_xmit`: L, section 2.2). The reached
  callers: the handshake send worker (`send.c:21-44`, which ignores the
  return), the retransmit and keepalive timers through it, the tx worker
  (`send.c:242-256`: a failed send leaves `data_sent` false, so
  `wg_timers_data_sent` does not run and no kind-303 arm record appears),
  and `wg_socket_send_skb_to_peer` keeps `tx_bytes` unchanged
  (`socket.c:182-183`). The skb is freed (`:91`).
- **Carrier off** (`device.c:418`; `sch_generic.c:608-616`): the first
  `netif_carrier_off` on `wg0` (WireGuard never calls `netif_carrier_on`;
  the bit starts clear) sets `__LINK_STATE_NOCARRIER` and fires a linkwatch
  event. **Synchronously** `dev_get_flags` (`dev.c:8903-8920`) drops
  `IFF_LOWER_UP`; `IFF_RUNNING` is already clear for a down device
  (`netif_running` false) and, for an up device, follows `operstate`, which
  the linkwatch work sets later. **Asynchronously** `linkwatch_event` runs
  on `system_unbound_wq` (`link_watch.c:137-160`): **urgent only if the
  device is running** (`:109-121`: `!netif_running → false`), then with
  delay 0 (`mod_delayed_work(system_unbound_wq, &linkwatch_work, 0)`);
  otherwise delayed up to `HZ` (1 s). `linkwatch_do_dev` (`:170-190`)
  recomputes `operstate` and, **for an `IFF_UP` device without carrier,
  `dev_deactivate`** (`:181-184`): the device's queue becomes `noop_qdisc`
  (`sch_generic.c:1286-1298`), so a later `dev_queue_xmit` takes the
  `q->enqueue` path (`dev.c:4510-4513`), `noop_enqueue` drops with
  `NET_XMIT_CN`, which `net_xmit_errno` maps to 0: **the sender's `sendto`
  succeeds and `wg_xmit` never runs**. For a down device the only effect is
  `operstate`, which no fixture output decodes; for an up device the
  deactivation is a state the mirror must know, so `linkwatch_event` must be
  an armed dispatch symbol whenever a running device can lose its creating
  namespace (section 3.2, W8b).

### 2.3 `send4` and `send6`, line by line

`send4` (`socket.c:20-95`), with `fl.saddr = endpoint->src4`, `daddr`,
`dport`, `flowi4_mark = wg->fwmark` (`:23-29`), `skb->mark` (`:36`):

| Line | Choice point | Operand |
|---|---|---|
| 41 | `!sock` → `-ENONET` | `sock4` NULL (W8.4) |
| 48 | `cache` | constant per caller: the peer's cache from `wg_socket_send_skb_to_peer` (`:175-176`), NULL from `wg_socket_send_buffer_as_reply_to_skb` (`:225`) |
| 49, 51 | `dst_cache_get_ip4` → `!rt` | hit/miss (section 2.4); on a hit `fl.saddr` is the cached source (`dst_cache.c:88`) |
| 53 | `!inet_confirm_addr(net, NULL, 0, fl.saddr, RT_SCOPE_HOST)` | section 2.5; on true: `src4 = src_if4 = 0`, `fl.saddr = 0`, `dst_cache_reset` if `cache` (`:55-59`) |
| 61 | `ip_route_output_flow` | section 2.6; writes `fl.saddr` back on success (`route.c:2833-2838` for a local destination) |
| 62-64 | `src_if4 && ((IS_ERR(rt) && PTR_ERR(rt) == -EINVAL) \|\| (!IS_ERR(rt) && rt->dst.dev->ifindex != src_if4))` | the receive interface vs the reply's device; on true: sources cleared, cache reset, `ip_rt_put` if a route (`:70-71`), a second lookup with `saddr = 0` (`:72`) |
| 74 | `IS_ERR(rt)` → the error, `kfree_skb` | `-ENETUNREACH` (section 2.6) |
| 80 | `cache` → `dst_cache_set_ip4(cache, &rt->dst, fl.saddr)` | constant per caller |
| 85 | `udp_tunnel_xmit_skb(rt, sock, skb, fl.saddr, fl.daddr, ds, ip4_dst_hoplimit, 0, sport, dport, false, false)` | returns `void` (`udp_tunnel_core.c:158`; `iptunnel_xmit`, `ip_tunnel_core.c:50`, also `void`): **`send4` returns 0 whatever the transmit did** |

`send6` (`:97-166`) mirrors it without the `src_if` check: `!sock` (`:121`),
`cache` (`:128`), `!dst` (`:131`), `!ipv6_addr_any(&fl.saddr) &&
!ipv6_chk_addr(net, &fl.saddr, NULL, 0)` (`:133-134`; on true `src6 = any`,
reset, `:135-137`), `ipv6_dst_lookup_flow` (`:139-140`), `IS_ERR(dst)`
(`:141`), `cache` (`:147`), `udp_tunnel6_xmit_skb` (`:152`). `flowi6_oif =
sin6_scope_id` (`:106`): the mirror already stops on a scoped source
(`Handshake.lean:472`). Then `wg_socket_send_skb_to_peer` (`:168-187`): the
family split (`:174`, `:177`, already decisions), `tx_bytes += skb_len` iff
`ret == 0` (`:182-183`). The reply path `wg_socket_send_buffer_as_reply_to_skb`
(`:203-233`, E's cookie replies) calls `send4`/`send6` with `cache = NULL`
(`:225`, `:227`) and an endpoint built from the received skb (`:213`).

The census counts 146 lines for W9 (`:20-95` and `:97-166`).

### 2.4 The dst cache: what decides a hit

`dst_cache_get_ip4` (`dst_cache.c:75-90`) → `dst_cache_per_cpu_get`
(`:39-64`), one CPU so one slot. A hit needs (i) a cached `dst` (`:46`),
(ii) **`time_after(idst->refresh_ts, dst_cache->reset_ts)`** (`:52-53`),
(iii) `!dst->obsolete || dst->ops->check(dst, idst->cookie)` (`:54`). On a
miss the slot's `refresh_ts = jiffies` (`:62`) and the caller stores the new
dst (`:93-104`, `:108-121`). `reset_ts = jiffies` is written by
`dst_cache_reset` (`dst_cache.h:77-80`, an inline: its callers are
`socket.c:59,69,137,294`, `dst_cache_init` at `dst_cache.c:150` from
`wg_peer_create` (`peer.c:36`), and `dst_cache_reset_now` at `:176` from
`wg_socket_clear_peer_endpoint_src`, which also drops the dst, `:177-184`).

So, with `J` the jiffy of the last reset and the accesses in order: every
access up to and including the first one in a jiffy later than `J` misses;
after that they hit (until the next reset or staleness). Two consequences:
- **the first send after a reset always misses** — deterministic, and the
  arms at `:53-73` run then;
- **whether the second send hits is a `jiffies` comparison** between the
  reset and the first miss. Those two events are typically microseconds
  apart inside one worker chain (the receive worker's endpoint update,
  `socket.c:294`, then the keepalive's tx worker) or separated by
  operations with no clock record in between (`wg_set` creates the peer and
  resets; the next `wg_xmit`'s tx worker misses). A 4 ms tick falls between
  them with a probability of order 1-5% per handshake. The mirror cannot
  compute (ii) from its records: `jiffies` is a plain load (strategy,
  section 4.3), and no recorded clock read sits at either event. D3 faced
  the same gap at `mod_timer` and closed it with the kind-303 arm record
  (D3, section 3.3). Section 4.1 does the same here.

(iii) is deterministic from fixture state. IPv4: every output route is
`DST_OBSOLETE_FORCE_CHK`, and `ipv4_dst_check` fails iff the namespace's
`rt_genid` moved since the dst was made; `rt_cache_flush` (`route.c:406-408`)
bumps it on every address or route change of the fixture:
`fib_inetaddr_event` (`fib_frontend.c:1506,1517,1521`), `fib_netdev_event`
(`:1459,1470`), `fib_disable_ip` (`:1442`), `fib_table_insert`
(`fib_trie.c:1385`) and `fib_table_delete` (`:1755`). IPv6: the cookie is
the route's fib node `fn_sernum` (`dst_cache.c:118` → `rt6_get_cookie`,
`ip6_fib.h:298-316`; checked by `rt6_check`/`rt6_dst_from_check`,
`ipv6/route.c:2764-2788`), which changes for the nodes on the path of an
added or deleted route (`fib6_update_sernum_upto_root`, `ip6_fib.c:1378-1381`)
and for every node on `rt_genid_bump_ipv6` (`net_namespace.h:542-546` →
`fib6_flush_trees`, `ip6_fib.c:2306-2311`; called from `addrconf_ifdown`
with `bump_id`, `addrconf.c:4406`, and on address completion/removal,
`:3241`, `:6339`). The environment keeps an IPv4 generation and an IPv6
generation, bumped by the operations that touch the fixture's tables
(section 4.2); a cached dst remembers the generation it was made in.

### 2.5 `inet_confirm_addr` and `ipv6_chk_addr` in the fixture

`inet_confirm_addr(net, NULL, dst = 0, local = saddr, RT_SCOPE_HOST)`
(`devinet.c:1470-1491`) walks every device and returns the first
`confirm_addr_indev` (`:1418-1460`) hit. With `local = 0` it autoselects: the
first address of the first device (`lo`'s `127.0.0.1`), so the test at
`socket.c:53` passes whenever any address exists. With `local` set it
returns `local` iff **some interface has exactly that `ifa_local`** (`:1433`)
and `local` matches that address's prefix (`:1440`); a `local` that is
merely inside a local prefix (`127.0.0.2` is inside `lo`'s `127.0.0.0/8`,
and `fib_lookup` treats it as local, `route.c:2751-2754` via
`__ip_dev_find`) returns 0 (`same` set, `addr` never set, `:1459`). So the
arm at `:53` fires for a `src4` that was the destination of a received
datagram but is not a configured address: **a datagram sent to `127.0.0.2`
reaches `wg0`'s wildcard socket with `daddr = 127.0.0.2`
(`wg_socket_endpoint_from_skb`, `socket.c:243`), and the reply's source
check fails** — no fixture change needed, only a `wg_inject` destination.
It also fires when the configured address `src4` was learned from (`wg0`'s
own `10.255.254.1`, `guest.c:496-500`) has since been deleted. The IPv6 side
(`ipv6_chk_addr`, `addrconf.c:1961-1966` → `ipv6_chk_addr_and_flags`,
`:2019-2025`, any device, non-strict) has no `/8`-style local prefix on
`lo` (`::1/128` only), so its arm needs the address removal: inject to
`wg0`'s `fd00:ffff::1`, delete that address, send.

The source that then goes out: `ip_route_output_key_hash_rcu` with `saddr =
0` and a local destination takes the route's `fib_prefsrc`
(`route.c:2833-2838`), `127.0.0.1` for both the `127.0.0.1/32` and the
`127.0.0.0/8` local routes (`fib_magic` sets `fc_prefsrc = ifa_local`), and
`::1` for `::1` (`ip6_route_get_saddr`). The sender's `recvfrom` prints that
source (`guest.c:575-600`), so the arm is **behaviourally observable**: a
mirror that keeps `src4 = 127.0.0.2` would report the reply from `127.0.0.2`.

**Today's mirror is wrong here.** `Env.deliverSent` assumes "over loopback
the source is the destination's own address" (`Env.lean:206-213`), which
holds for the corpus (every endpoint is the sender at `127.0.0.1`/`::1`,
`guest.c:853-863`) and fails as soon as a datagram is injected to `wg0`'s
own address: `src4 = 10.255.254.1` passes `inet_confirm_addr`, the reply
to `127.0.0.1:51998` leaves `lo` with source `10.255.254.1`, and the sender
sees `::ffff:10.255.254.1`. W9's inject destination variants make this a
checked case (section 7, W9-M1).

### 2.6 Routing: the fixture's tables, errors, re-entry, fwmark

The fixture namespace has `lo` up (`guest.c:253-257`; `127.0.0.0/8` and
`::1` local), and after a successful up `10.255.254.1/32` and
`fd00:ffff::1/128` on `wg0` plus a default route per family via `wg0`
(`route_into_wg0`, `guest.c:483-521`; `RT_SCOPE_LINK`, no gateway, no
`prefsrc`). The sender is a dual-stack `[::]:51998` socket (`:730`), the
listeners `127.0.0.1:51999` and `[::1]:51999` (`:719-721`). So for `send4`
with `saddr = 0`: a `127/8` destination or `wg0`'s own address → `lo`
(ifindex 1, `RTN_LOCAL`, source = prefsrc); anything else → the default
route into `wg0` (ifindex 3) with source `10.255.254.1` (`inet_select_addr`)
while the routes exist, else **`-ENETUNREACH`** (`route.c:2714`, the only
error without a set `saddr`; with `saddr` set and not local, also
`-ENETUNREACH` via `:2751-2754`; **`-EINVAL`** only for a multicast,
limited-broadcast or zeronet `saddr`, `:2706-2712`). IPv6: `::1` and
`fd00:ffff::1` → `lo`; else the default route or `ip6_null_entry`'s
`-ENETUNREACH` (`ipv6/route.c:298`, returned by `ip6_dst_lookup_tail`,
`ip6_output.c:1115-1140`). A `wg_down` removes the IPv4 default route and the
IPv6 address and route (L, section 2.2); a `wg_up` restores them. W9 adds
operations that delete the default route or the address while up (section
4.3) so that the error arms are reached on a running device.

**Re-entry.** When the endpoint routes into `wg0` — any non-loopback
endpoint while the default route exists — `udp_tunnel_xmit_skb` →
`iptunnel_xmit` → `ip_local_out` → `dev_queue_xmit(wg0)` → **`wg_xmit`,
synchronously inside `send4`**, in the sending worker's task (or the trace
process for a reply from `wg_set`'s keepalive). `wg_xmit` (`device.c:141-234`)
then looks the outer UDP datagram's destination up in the allowed IPs:
- **no peer** (`:153-162`): `icmp_ndo_send` (`:226-227`; the ICMP goes to
  the outer source, `wg0`'s own address, is delivered locally and reaches
  the kernel UDP socket's `udp_err`, with no further effect), **`tx_errors`
  incremented** (`:231`), `kfree_skb`. Bounded, observable (`print_stats`
  reports `tx_errors`), in domain;
- **a peer whose endpoint is on loopback** (two peers): one more cycle,
  bounded, in domain;
- **a peer whose allowed IPs cover the endpoint and whose endpoint routes
  into `wg0` again** (the usual `0.0.0.0/0` peer with such an endpoint):
  every cycle wraps the datagram again and re-queues the encrypt worker;
  past the MTU the IP layer fragments (`ignore_df`, `socket.c:84`) and the
  packet count grows. `XMIT_RECURSION_LIMIT` (`netdevice.h:3302`) does not
  bound it: each cycle crosses a work item. The loop ends only at deletion
  (`wg_allowedips_remove_by_peer`). **Profound exclusion** (section 8).

The nested `wg_xmit`'s coverage lands inside the worker's section, like the
NET_RX softirq the mirror already nests at the send (`loopbackSend`). The
sender's `sendto` of the *inner* packet is unaffected; the mirror's
`wgXmit` runs nested with `World.xmitDepth` 1.

**fwmark.** `flowi4_mark`/`flowi6_mark` (`socket.c:27`, `:105`) steer the
lookup only through fib rules (`fib_rules` needs `IP_MULTIPLE_TABLES`,
selected by `IP_ADVANCED_ROUTER`, unset; `IPV6_MULTIPLE_TABLES` unset), and
`skb->mark` (`:36`, `:116`) is read by nothing in the fixture (no netfilter
rules, no `tc`). So on this config the mark changes no decision and no
observable: W9.7 is excluded with the config as evidence; `CONFIG_IP_ADVANCED_ROUTER=y`
plus a fixture rule (`ip rule add fwmark … table …`) would lift it, which
is a kernel config change (needs user approval), listed in section 8.

## 3. W8: the design

### 3.1 The fixture mode `"net_fixture": "foreign-creator"`

The creating namespace must exit inside a window while `wg0` and the
trace's handles to it survive. Since `lookup_interface` finds the device in
the genetlink socket's namespace (`netlink.c:52-73`) and a user socket pins
its namespace (`sock.c:2246-2247`), the device, the genetlink socket and the
inner-traffic sender must live in a namespace that does **not** exit, and
the creating namespace must hold nothing but what the operation closes.
Two namespaces, then:

- **D, the device namespace**: where `wg0` lives, where the trace process
  lives, and where today's fixture roles that are about the *inner* side
  stay: the genetlink socket (`NETLINK_FD` 7) and the sender for inner
  packets, `wg_up`'s `ioctl`, `route_into_wg0`, `print_stats` (`SEND_FD` 6).
  `lo` up, `wg0` at ifindex 3 (`lo` 1, `sit0` 2, as in the plain fixture).
- **C, the creating namespace**: where `wg_socket_init` binds (`socket.c:387`
  with `net = creating_net`), so where the *outer* side lives: the two
  listeners (`LISTEN4_FD` 4, `LISTEN6_FD` 5) and an **injector**, a second
  dual-stack `[::]:51998` socket (descriptor 8) that sends `wg_inject`'s
  datagrams to `wg0`'s port and receives `wg0`'s replies to that endpoint —
  the same address and port the plain fixture's sender has, so the endpoint
  `wg0` learns is unchanged (`127.0.0.1:51998`, `::1:51998`) and
  `Env.isSender` and `portBound` (`{51998, 51999}`) keep their meaning. Plus
  the **pin**, descriptor 9: `open("/proc/self/ns/net")` while in C, the
  reference the operation drops.

`network_fixture` in this mode: `unshare(CLONE_NEWNET)` → D, `lo` up, park
`open("/proc/self/ns/net")` at a high descriptor; `unshare` → C, `lo` up;
over a temporary rtnetlink socket **in C**, `RTM_NEWLINK wg0` with the
existing attributes (`newlink_wg0`) plus `IFLA_NET_NS_FD` = D's descriptor:
`rtnl_newlink_create` allocates the device in D (`rtnetlink.c:3625`) and
calls `wg_newlink` with `src_net = C` (`:3635`), so `creating_net = C`
(`device.c:316`) and `register_netdevice` runs in D (ifindex 3). Close the
rtnetlink socket. Then the descriptors in order, switching with
`setns(fd, CLONE_NEWNET)`: in C, 4 and 5; in D, 6 and 7; in C, 8 and the pin
at 9; `setns(D)`; close the parked D descriptor. The final table is the
plain fixture's four plus 8 and 9, `next_fd` 10; the mirror's
`initialKernel` for this mode installs fixture files at 4-9 (the L design
rejected a persistent extra descriptor for *all* network traces because it
shifts the layout of every existing trace; here it is confined to this
mode, and its traces are new). An alternative plumbing — create in C as
today, then move with `RTM_SETLINK` + `IFLA_NET_NS_FD`
(`__dev_change_net_namespace`, which keeps `creating_net` and the sockets)
— reaches the same state through more core code outside any window; not
taken [AGENT: one attribute on the existing message is smaller].

The fixture's end: `delete_wg0` (`RTM_DELLINK` over a rtnetlink socket in
D, as today, synchronous); C's teardown is the operation below, which
**every trace of this mode must contain** (the harness validates it), so
that no `cleanup_net` of C runs after the trace process exits (section
3.2). `fail()`'s best-effort teardown is unchanged (it deletes `wg0`; C
and D then die after exit, unarmed by the parent's pin, below).

### 3.2 The operation `wg_netns_close`, the dispatch set, the parent's pin

**`wg_netns_close {op}`** (wire opcode 18; L's are 15-17, D3's 14): inside
the window, `close(9)`, `close(8)`, `close(5)`, `close(4)` in that order,
then the guest waits `NETNS_WAIT_US` (200 ms [AGENT], sized by the probe)
before the readout, like the queueing operations' `QUEUE_WAIT_US`
(`guest.c:940`). Each close is an anchored FS syscall the mirror already
models (`__x64_sys_close` → `file_close_fd` → `filp_close` → `fput`): the
operation is four mirrored closes of fixture files. The UDP sockets'
`put_net` runs in their RCU-deferred destructors (`udp.c:330`,
`SOCK_RCU_FREE`), the pin's in `nsfs`'s release; whichever is last queues
`cleanup_net`. The result is 0; a close error is an environment failure
(the descriptors are the fixture's).

The mirror's `Env.wgNetnsClose`: the four `close`s through `Syscalls`;
`World.netnsCHolders := []`; then **`runWorker .netnsCleanup
WG.netnsPreExit`** consuming the section's start record, the pre-exit's
decisions, and the stop. Between pre-exit and the stop the records may show
a `linkwatch_event` section (urgent, queued at `device.c:418`, run when the
netns kworker sleeps at `net_namespace.c:663` or at `:648`'s
`netdev_run_todo`): `runNetnsCleanup` accepts `.linkwatch` sections there
(and runs `WG.linkwatchDoDev`), the ambient scheduler site anywhere, and
nothing else; the stop must arrive before the operation ends (no pending
stop: `Runner.executeTrace` already requires none). A timer section there
is `unsupported "a timer section inside the netns cleanup"` (the generator
places no due timer in the wait: section 10).

**The dispatch set** gains `cleanup_net` and `linkwatch_event`
(`harness/linux.py:39-44`, `DISPATCH_SYMBOLS`; the mirror's `Worker` gains
`.netnsCleanup` and `.linkwatch` with those symbols, `Defs.lean:241-262`,
and `check.py:852-854` keeps requiring every section site to be in the set).
The set is batch-wide (`trace.py:190-205`, `linux.py:436`), so both are
armed for **every** network trace. Consequences, each closed:
- **The fixture namespace's own teardown.** Today D (the plain fixture's
  single namespace) dies after the trace process exits, before or after the
  parent's `KCOV_LEANUX_SECTION_STATUS` (`guest.c:685-689`); with
  `cleanup_net` armed its section would be opened and not recorded, and
  `section_problems` (`check.py:358-372`) would fail the trace. So **the
  parent pins the child's namespace**: after `fork` (`:672`) the child, once
  its fixture is built, writes one byte to the existing status channel; the
  parent opens `/proc/<child>/ns/net` (D), keeps it across `waitpid` and the
  section status, and closes it last. D's `cleanup_net` then runs after the
  disarm, unrecorded, as today. (A trace that ends without `wg_netns_close`
  in the foreign-creator mode would still leak C's section after exit; the
  harness rejects such a trace up front.)
- **Sections in the existing suites.** No existing trace drops a namespace
  or changes a carrier inside a window, so neither symbol should open a
  section in them; the probe runs the regression suites with the two armed
  and requires `opened = 0` everywhere (fail-closed by the existing check).
- **Record inventory inside `cleanup_net`.** The section covers the whole
  teardown of C (`lo` and `sit0` unregistered, every pernet `exit`); its
  random and clock consumers are unknown until measured. Any consumer other
  than the ambient scheduler site becomes a declared cut consumer of the
  `.netnsCleanup` cut point with a justification, or the trace is
  `hidden_mismatch`; the mirror runs nothing of it beyond `wg_netns_pre_exit`.
- **Coverage volume.** The teardown's PCs and comparisons count against the
  operation's `CAPACITY` (256 K words after L0, `guest.c:34`); `proc` and
  sysctl removals compare names byte by byte in the comparison child. The
  probe measures both children's counts for `wg_netns_close`.

**Ordering, stated.** The exit is queued inside the operation's last
`close`; the section opens when the kworker first runs (the return to user
space, or the wait); `wg_netns_pre_exit`'s decisions precede the section's
first sleep; the stop follows within milliseconds. The mirror consumes the
section at the operation, in record order, and every later operation sees
`creatingNet = false`. Two residues are fail-noisy, not silent: a section
that did not open in the wait leaves the mirror's `hidden (.sectionStart
.netnsCleanup)` unmatched; a section whose stop outlives the wait leaves a
pending stop at the operation's end.

### 3.3 Mirror: state, functions, decisions, the map

State (`Leanux/WG/Types.lean`, `Leanux/Kernel/Defs.lean`):
- `Device.creatingNet : Bool` (L) — now also cleared by `wgNetnsPreExit`.
- `Device.carrier : Bool := true` — `__LINK_STATE_NOCARRIER` inverted;
  cleared by `wgNetnsPreExit`; reported in the new `flags` observable.
- `Device.qdiscNoop : Bool := false` — set by the linkwatch run on an up
  device without carrier (`link_watch.c:181-184`); cleared by `dev_activate`
  at the next `wg_up` (`dev.c:1559-1561`; `linkwatch_do_dev` re-activates on
  carrier, which never returns for `wg0`). While set, `Env`'s `wg_xmit`
  dispatch returns the datagram's length and runs nothing (section 2.2).
- `World.fixtureMode : .plain | .bare | .foreignCreator`; `World.netnsCHolders
  : List Fd` (`[9, 8, 5, 4]`), emptied by the operation; the mode's fixture
  files at 8 and 9.

Functions (`Leanux/WG/Device.lean`, `Socket.lean`, `Netlink.lean`, `Env.lean`):

| Mirror | C | Notes |
|---|---|---|
| `wgNetnsPreExit` | `device.c:409-428` | over `device_list` (one device: `.preExitDevIter`), `.preExitCreator` (`creating_net == net`, true in this mode), `carrier := false`, `creatingNet := false`, `socketReinit none none` (L's decisions: `.reinitHasNew4` false, `.sockFreeNull` ×2 by whether the device was up), per peer `.preExitPeerIter` → `clearPeerEndpointSrc` (`endpoint.src := 0, srcIf := 0, scope := 0`; `dstCache := .empty`) |
| `linkwatchDoDev` | `link_watch.c:170-190` | data only, no anchored decision: `qdiscNoop := running && !carrier`; run by `runWorker .linkwatch` |
| `socketInit` | `socket.c:376-381` | `.socketInitNoNet` becomes a live decision on `!creatingNet` → `-ENONET` (L declared it constant false); listed in `kcov.json` with two operand exclusions (below) |
| `setDevice` | `netlink.c:513-521` | new decision `.setDevNoCreatingNet` at `:517`: with a port or fwmark attribute, `!creatingNet` → `-EPERM` before `deviceUpdateGen` moves; the `ns_capable` operand constant true (section 2.2) |
| `send4`/`send6` `.sock4Null`/`.sock6Null` | `socket.c:41`, `:121` | W9's functions (section 4.2); in W8a (device down) unreached; in W8b reached from the timers' and keepalive paths |
| `Env.wgUp` | | the L rule stays; `wgOpen`'s `socketInit` now returns `-ENONET` → `running := false`, `ioctl` fails `ENONET`; `Env.routesViaWg0` stays false |
| `Env.observe` | `print_stats` | adds `flags` (section 6) |

`correspondence/kcov.json`: `wg_netns_pre_exit` listed; **`wg_socket_init`
listed** (L left it out, section 16.3 of the L design: its inlined
`maybe_get_net` and `put_net` put `include/linux/refcount.h` comparisons —
an anchored header — into a listed function, with the namespace's reference
count as operand). The P-int precedent resolves exactly this:
`operand_exclusions` (`kcov.json` at `45d7702:219-226`, `README.md:150-164`,
`OperandExclusion` in `Decision.lean:295-303`) declares a single call site
of a comparison whose operand is a guest-wide value the mirror does not
model; the mirror reports the outcome with `operands_excluded`, and the
check requires Linux's comparison at that call site. Two entries:
`__refcount_add_not_zero.old_zero` (`refcount.h:145`, the `if (!old)` of the
cmpxchg loop; outcome: not zero — the namespace is alive whenever
`creatingNet` is set, by section 2.1's ordering) at call `socket.c:378`
(through `maybe_get_net`), and `__refcount_sub_and_test.last` (`:269`,
`old > 0 && old == i`; outcome: false — the fixture's holders, section 3.1,
outnumber the temporary reference) at call `socket.c:415` (through
`put_net`), with the saturation checks at `:152` and `:274` as constant-false
decisions sharing the exclusion's operand. The two outcomes are still
A2-checked. With that, `.socketInitNoNet` (`:380`), `.socketInitV4Err`
(`:388`), `.socketInitHasIpv6` (`:396`), `.socketInitV6Err` (`:399`) and
`.socketInitRetry` (`:401`) are reported and witnessed as the L design
intended (its section 4.3).

New `Decision` constructors (the `d` form, `Decision.lean:912-916`):
`preExitDevIter` (device.c:415, repeatable), `preExitCreator` (416),
`preExitPeerIter` (422, repeatable); `setDevNoCreatingNet` (netlink.c:517);
`socketInitNetNull` (socket.c:378, the ternary's first operand);
`refcountAddNotZeroOldZero` (refcount.h:145, excluded operand),
`refcountAddSaturate` (152), `refcountSubLast` (269, excluded operand),
`refcountSubSaturate` (274); the `send4`/`send6` ones in section 4.4.

### 3.4 Environment rules for the mode

- **Two namespaces, one routing model each.** C has `lo` only: `wg0`'s
  outer datagrams to `127/8` and `::1` reach the listeners or the injector
  as `deliverSent` does today; any other destination has **no route in C**
  (no default route there) → `send4` returns `-ENETUNREACH` (section 2.6),
  which W9's routing function reports from `World.netnsCRoutes`. D has the
  plain fixture's tables (the address and default route via `wg0`), used
  by the inner side (`wg_xmit`'s dispatch) only. So in this mode the
  re-entry (W9.5) cannot occur: an endpoint off loopback is unroutable in C.
- **After `wg_netns_close`.** `wg_inject` has no socket in C: `unsupported`
  (the generator never injects after the close). `wg_observe` drains the
  sender (D) and prints the listeners and injector as absent (`null`,
  like `stats: null`); the mirror's `observe` mirrors that from
  `netnsCHolders`. `wg_up` → `ENONET`; `wg_set` with port/fwmark → `EPERM`;
  `wg_delete` works (`wg_destruct` tolerates a NULL `creating_net`, L
  section 2.4).
- **`portBound` is C's**: `{51998, 51999}`, as in the plain fixture.
- **Carrier and flags.** `flags = (IFF_UP if running) | (IFF_LOWER_UP if
  carrier)`; `IFF_RUNNING` masked (section 6).

### 3.5 Feasibility and determinism, answered

- *Is `netns_wq` work a dispatch section?* Yes: `queue_work(netns_wq, …)`
  (`net_namespace.c:702`) on a `create_singlethread_workqueue` (`:1200`)
  runs through `process_one_work`, where the hook opens a section for an
  armed function. Adding `cleanup_net` to `DISPATCH_SYMBOLS` suffices; the
  symbol is one text symbol (`static void cleanup_net` in one TU).
- *When does it run?* Inside the operation that drops the last reference,
  at the return to user space or in the operation's wait (section 2.1);
  the records order it; the mirror expects it at that operation and
  nowhere else.
- *Is `wg_socket_init`'s `-ENONET` deterministic?* Yes, after the section:
  `creating_net` is NULL. The `maybe_get_net`-fails arm is a window the wait
  closes (section 8).
- *The `-EPERM`?* Yes, data-only: `!net` (section 2.2).
- *The capability check through a user or child namespace?* No `USER_NS`:
  `user_ns` is always `init_user_ns`, `ns_capable` is root's `capable`;
  unreachable as a WireGuard decision, and refused earlier in genetlink for
  a non-root sender.
- *The transitions `creatingNet`/socket-NULL?* Set in `wgNetnsPreExit` at
  the section; W8a (device down) observes them through `wg_up`, `wg_set`
  and the dump; W8b (device up) additionally through the timers' and
  keepalive sends (`send4` `-ENONET`) and through the linkwatch deactivation
  (a `sendto` into `wg0` that runs nothing). W8b needs D3's advance and the
  armed `linkwatch_event`; it is a second stage after W9's `send4`/`send6`
  land, since the `-ENONET` arm is theirs.

## 4. W9: the design

### 4.1 The hidden input: `jiffies` at the dst cache — a kernel change

Section 2.4 shows the cache's hit/miss is `time_after(refresh_ts,
reset_ts)` on two `jiffies` stores the mirror cannot see. The options, with
the project's rules applied:

| | Option | Verdict |
|---|---|---|
| J1 | derive `jiffies` from the recorded clock reads (on the D3 oracle every coarse read is tick-granular, so each record pins a jiffy) | **insufficient**: neither the reset (`socket.c:294` in the receive worker; `peer.c:36` in `wg_set`) nor the access (the tx worker's `send4`) has a clock record at it; the two are bracketed by the same records most of the time, so the comparison is undetermined in exactly the common case |
| J2 | **record `jiffies` where the cache stores it**: `kcov_choice_ip(305, _RET_IP_, &jiffies, 8)` at `dst_cache.h:79` (`dst_cache_reset`, inline — the record carries each caller's chain) and `dst_cache.c:62` (the refresh on a miss) | **recommended** [AGENT]. One kind, two sites, in `net/core` (unanchored), generic for every `dst_cache` user in the kernel. The mirror stores the recorded value in its own cache state and computes `time_after` itself: the decision stays computed, the input is recorded — the same shape as D3's kind-303 arm record, which closed the `jiffies`-at-`mod_timer` gap (D3, section 3.3). An oracle change: a patch on `kernel/patches/choice-stream.patch`, a new identity, **user approval** |
| J3 | declare `socket.c:51` and `:131` as `known_gaps` (hits reported, not failed) and model the cache as always missing | **fail-open** at the one decision that gates `:53-82`; the arms would be unverified. Forbidden without explicit authorization; listed only as the fallback if J2 is refused |
| J4 | an environment rule "a reset and the next access are in the same jiffy iff in the same operation" | wrong in 1-5% of handshakes (section 2.4); a wrong prediction fails the trace (A2), so it is noisy, but as a flake rate over 1,400 traces it is not acceptable |
| J5 | force a tick between every reset and send with guest waits | impossible inside one worker chain (the receive worker's reset and the keepalive's send) |

With J2 the mirror's cache is exact: `DstCache := { resetTs : Nat, slot :
Option { refreshTs : Nat, src : Nat, gen : Nat } }` per peer;
`dstCacheReset` consumes a kind-305 record (`.dstCacheResetTs`) into
`resetTs`; `dstCacheGet` decides `slot.isSome && refreshTs > resetTs && gen
== World.gen(family)`, and on a miss consumes the refresh record
(`.dstCacheRefreshTs`) into `refreshTs` (the C does both the comparison and
the store in `dst_cache_per_cpu_get`; on a hit no record). `dst_cache_reset_now`
is a reset record plus `slot := none`. `dst_cache_init` (`wg_peer_create`)
is a reset record. The record inventory per operation is bounded: one per
reset, one per miss. Steering is not needed (the value is consumed as data,
never chosen).

### 4.2 Mirror: `send4`/`send6`, the routing function, the nested `wg_xmit`

**State.** `Endpoint` already carries `src`, `srcIf`, `scope`
(`Types.lean:52-60`). Add `Peer.dstCache : DstCache` (above).
`SentDatagram` gains `src : Nat` (the source `send4` chose) and keeps
`sport` (L); `InboxDatagram.addr` for the sender's `recvfrom` becomes that
`src` instead of "the destination's own address" (`Env.lean:206-213`),
fixing the defect of section 2.5. `World` gains `ipv4Gen`, `ipv6Gen`
(bumped by the operations of section 4.3 and by `wg_down`/`wg_up`'s route
changes), `xmitDepth : Nat` (0 outside a send), and a routing table
abstraction: `World.addrs4/addrs6 : List Addr` on `wg0`,
`World.defaultRoute4/6 : Bool` (replacing L's single `routesViaWg0`, which
becomes `defaultRoute4 && defaultRoute6`), the loopback prefixes as
constants.

**`Env.route4 (saddr daddr) : Except Errno { dev : Nat, src : Nat }`**, the
fixture's `ip_route_output_flow` (section 2.6): if `saddr ≠ 0` and
`saddr ∉ {loopback, addrs4}` → `-ENETUNREACH` (`route.c:2751-2754`; the
`-EINVAL` class of `:2706-2712` is the stretch item); `daddr ∈ 127/8 ∪
addrs4` → `{lo, if saddr ≠ 0 then saddr else prefsrc}` with prefsrc
`127.0.0.1` for `127/8` and the address itself for `addrs4`
(`:2833-2838`); else if `defaultRoute4` → `{wg0, if saddr ≠ 0 then saddr
else addrs4.head}`; else `-ENETUNREACH` (`:2714`). `route6` likewise with
`::1` and `addrs6`. The same function answers the inner side's question
("does the sender's datagram route into `wg0`?") in `Env`'s `wg_xmit`
dispatch, replacing the `routesViaWg0` test (`Syscalls.lean:95` in L): one
model of the tables, two users.

**`send4 pid bytes ds cache`** (`Leanux/WG/Socket.lean`), the C in order:
`.send4SockNull` (41) → `-ENONET`, free; `.send4HasCache` (48; `cache` is
`some pid` or `none`); `dstCacheGet` → `.send4CacheMiss` (51); on a miss:
`.send4SrcNotLocal` (53, `src ≠ 0 && src ∉ addrs4 ∪ {127.0.0.1}` —
`inet_confirm_addr`'s rule of section 2.5: exactly a configured address;
with `src = 0` autoselect succeeds) → sources cleared, `fl.saddr := 0`,
`.send4ResetA` (58) reset; `route4`; `.send4SrcIfMismatch` (62-64: `srcIf ≠
0 && (route = -EINVAL || (route ok && dev ≠ srcIf))`) → cleared,
`.send4ResetB` (68) reset, `.send4PutRt` (70), second `route4` with `saddr
= 0`; `.send4RouteErr` (74) → the errno, free; `.send4CacheSet` (80) →
`slot := { refreshTs, src := fl.saddr, gen }`; then the transmit: `src :=
fl.saddr`; if `dev = lo` → `World.sent` (delivered by `deliverSent` as
today, with the source), if `dev = wg0` → **`xmitNested`**: `xmitDepth +=
1`, run `wgXmit` on the outer datagram (an IPv4 UDP packet from `src` to the
endpoint, length `bytes.length + 28`, TTL `ip4_dst_hoplimit` = 64) as the
C does synchronously, `xmitDepth -= 1`; `xmitDepth = 1` on entry →
`unsupported "a datagram routed into wg0 for the second time (an endpoint
inside a peer's allowed IPs)"` (section 2.6's profound case; the first
re-entry is modeled). Return 0 for a transmitted datagram (the transmit's
own outcome is invisible to `send4`, section 2.3). `send6` likewise with
`.send6SrcNotLocal` (133-134, `src ≠ ::` and `src ∉ addrs6 ∪ {::1}`) and no
`srcIf` arm. `sendSkbToPeer`/`sendBufferToPeer` call them instead of the cut
(`Handshake.lean:402-416`, `Data.lean:135-150`); `loopbackSend`'s NET_RX
nesting stays for the `lo` case; E's `sendBufferAsReplyToSkb` passes `cache
:= none`. The IP-ident cut consumers (`.ipIdentKey`, `.ipIdentReserve`,
`.flowHashSecret`) stay at the send cut point, which is now the transmit at
`:85`/`:152`, one level down; a nested `wg_xmit`'s own inner send adds its
own cut records at the same site.

**`wg_socket_set_peer_endpoint`** (`socket.c:273-297`): already mirrored for
the endpoint; adds the reset record at `:294` (and `endpoint_eq`'s
`src`/`srcIf` comparison, `:258-271`, is already data). `clearPeerEndpointSrc`
(`:308-314`): the reset-now record. `wgPeerCreate`: the init record.

### 4.3 Harness: operations and observables

- **`wg_inject` gains a destination** (`trace.py` field `"to"`:
  `"loopback"` (default, today's `127.0.0.1`/`::1`), `"wg0"` (the fixture
  address `10.255.254.1`/`fd00:ffff::1`, reached through the local route
  over `lo`, `skb_iif` 1), `"loopback-alias"` (`127.0.0.2`; IPv4 only).
  The guest (`guest.c:853-863`) builds the sockaddr from it. These make
  `src4` a configured address, a non-configured local one, or the sender's
  address — the three cases of `inet_confirm_addr`.
- **`wg_deladdr {op, family}`** (opcode 19): `RTM_DELADDR` of the fixture's
  address on `wg0`, over L's temporary rtnetlink descriptor
  (`rtnetlinkRequest`), result the ACK (`0`, or `-EADDRNOTAVAIL` when
  absent). Environment: `addrs := addrs.erase a`, the family's generation
  bumped (`fib_inetaddr_event` NETDEV_DOWN → `rt_cache_flush`,
  `fib_frontend.c:1517`; the IPv6 removal bumps through `addrconf`), the
  local route gone; the default route stays (no `prefsrc`,
  `fib_sync_down_addr` removes only routes whose `prefsrc` is the address).
  `route_into_wg0(first = 0)` after a later re-up must then tolerate a
  missing IPv4 address: the L rule "the IPv4 add must fail `EEXIST` on a
  later up" becomes "must fail `EEXIST` unless a `wg_deladdr` removed it
  since" — the guest tracks it, fail-closed otherwise.
- **`wg_delroute {op, family}`** (opcode 20): `RTM_DELROUTE` of the default
  route via `wg0`; result the ACK (`0` or `-ESRCH`). Environment:
  `defaultRoute := false`, the generation bumped (`fib_table_delete`,
  `fib_trie.c:1755`; `fib6_del` → sernum). Afterwards the sender's inner
  `sendto` to a non-local destination fails `-ENETUNREACH` without reaching
  `wg0`, and `wg0`'s outer sends to a non-loopback endpoint hit
  `.send4RouteErr`.
- **`wg_set` endpoints off loopback** need no new operation
  (`WGPEER_A_ENDPOINT` is free-form today); with the default route present
  they route into `wg0` (W9.5); with it deleted, `-ENETUNREACH` (W9.4).
- **Observables**: the sender's `recvfrom` source (already printed; the
  mirror now computes it), the dump's per-peer `tx_bytes` (decoded by
  `harness/wg.py:252-253`), `tx_errors` (`print_stats`), coverage; and
  W8's `flags` (section 6).

### 4.4 The map and the decisions

`correspondence/kcov.json`: `send4` and `send6` listed (static, each with
two callers of about 75 lines: expected out of line; the probe confirms
`t send4`/`t send6` in `System.map` — if either is inlined, its lines are
attributed to the caller's frame and the entries name the callers);
`net/core/dst_cache.c`, `net/ipv4/route.c`, `net/ipv4/devinet.c`,
`net/ipv6/addrconf.c`, `net/ipv6/route.c` stay unanchored (their internal
branches are the environment's; `send4`'s decisions carry the outcomes).

New constructors, the `d` form, file `wso`: `send4SockNull` (41),
`send4HasCache` (48), `send4CacheMiss` (51), `send4SrcNotLocal` (53),
`send4ResetA` (58), `send4SrcIfMismatch` (62, spans 65-72 / 74),
`send4ResetB` (68), `send4PutRt` (70), `send4RouteErr` (74), `send4CacheSet`
(80); `send6SockNull` (121), `send6HasCache` (128), `send6CacheMiss` (131),
`send6SrcNotLocal` (133), `send6Reset` (136), `send6RouteErr` (141),
`send6CacheSet` (147); `replyFromSkbInet`/`Inet6` (224, 226) if E has not
added them. `send4SrcIfMismatch`'s `IS_ERR`/`-EINVAL` operands are reported
with the route's errno as the mirror computes it (`-EINVAL` never, on this
fixture: section 8).

Hidden sites (`HiddenSite`, `Defs.lean`): `.dstCacheResetTs` (kind 305,
consumer frames `socket.c:59`, `:69`, `:137`, `:294`, `dst_cache.c:150`,
`:176` — six chains, one site each, the inline's callers) and
`.dstCacheRefreshTs` (kind 305, `dst_cache.c:62`). The probe confirms the
resolved frames.

## 5. Hidden inputs

| Site | Kind | Consumer frame | Role | Consumed by |
|---|---|---|---|---|
| `.sectionStart/.sectionStop .netnsCleanup` | 300/301 | `cleanup_net` | dispatch | `Env.wgNetnsClose` only |
| `.sectionStart/.sectionStop .linkwatch` | 300/301 | `linkwatch_event` | dispatch | inside `runNetnsCleanup`; W8b: also at the operation's end for a delayed (non-urgent) event on a *down* device, where the mirror runs `linkwatchDoDev` with no effect — accepted anywhere a section may land (the idle points), since it changes nothing observable for a down device |
| `.dstCacheResetTs` | **305 (new)** | `dst_cache.h:79` through its six callers | mirror (data) | `dstCacheReset` |
| `.dstCacheRefreshTs` | **305 (new)** | `dst_cache.c:62` | mirror (data) | `dstCacheGet` on a miss |
| cut: the ambient scheduler site | 200+ | `deadline.c:1153` | ambient | anywhere (unchanged) |
| cut: consumers inside `cleanup_net` after `wg_netns_pre_exit` | ? | measured by W8-0 | cut, per entry with a justification | the `.netnsCleanup` cut point |
| the existing send-cut consumers (`ip_idents_reserve`, `__ip_select_ident`, `__flow_hash_secret_init`) | 110/104/1 | unchanged | cut | the transmit at `socket.c:85`/`:152`, including the nested `wg_xmit`'s inner send |

No steering is needed for either workstream. The kind number 305 follows
304 (`check.py:194-203`); the class is `jiffies`, resolved by consumer
frame like the clock readers.

## 6. Observables

- **`flags`** (new, in `print_stats`, `guest.c:528-559`): `ifi_flags &
  (IFF_UP | IFF_LOWER_UP)` from the `RTM_GETLINK` reply's header
  [AGENT: `IFF_RUNNING` is masked because `operstate` is set by the
  linkwatch work, which for a down device runs unarmed up to 1 s later].
  The plain fixture shows `IFF_LOWER_UP` always (carrier never goes off),
  `IFF_UP` while up; after a `wg_netns_close` `IFF_LOWER_UP` is clear. The
  mirror: `(if running then IFF_UP else 0) ||| (if carrier then
  IFF_LOWER_UP else 0)`. A regression-safe addition: the check compares
  Linux and the mirror, not stored expectations.
- The `ioctl` errno of `wg_up` (`ENONET`), the ACK of `wg_set` (`EPERM`),
  of `wg_deladdr`, `wg_delroute`.
- The dump: `listen_port` (unchanged by the exit), per-peer `tx_bytes`.
- `stats`: `tx_errors` for the re-entry's `!peer` arm.
- The sender's `recvfrom` source address (printed today, computed by the
  mirror from now on) and the listeners' datagrams; `null` for closed C
  descriptors.
- The kind-303 arm records of `wg_timers_data_sent` (absent after a failed
  send) and the kind-305 records (counts per operation).
- Coverage: `wg_netns_pre_exit`, `wg_socket_init`'s arms, `send4`/`send6`'s
  arms, the nested `wg_xmit`.

## 7. Evidence: what pays for itself

Each mutant names what no existing check catches; an `unsupported` counts
as rejected (`scripts/wg-mutants.py`).

- **W9-M1** the source of a loopback datagram is the destination's own
  address (today's `Env.deliverSent` rule, kept as a mutant): rejected by
  the trace `w9_inject_to_wg0_addr` (inject to `10.255.254.1`, the reply's
  source at the sender is `10.255.254.1`, not `127.0.0.1`). **A real defect
  of the current mirror**, unreachable by the current corpus (section 2.5).
- **W9-M2** `.send4SrcNotLocal` never fires (`src4` kept): `w9_inject_to_alias`
  (inject to `127.0.0.2`): the mirror's reply source `127.0.0.2`, Linux's
  `127.0.0.1`; and A2 at `socket.c:53-60`.
- **W9-M3** the cache never hits (every send misses): A2 at `:51` on the
  second send of `w9_two_sends` (needs J2).
- **W9-M4** the cache ignores the reset at `:294` (a changed endpoint keeps
  the old dst): A2 at `:51` after a roaming inject; and the stale source
  (`src` cached from the old endpoint) at the sender.
- **W9-M5** a route error still counts `tx_bytes`: the dump differs after
  `wg_delroute` + a send to an off-loopback endpoint (`w9_unroutable`).
- **W9-M6** the re-entry treated as a loopback drop (no nested `wgXmit`):
  `tx_errors` differs in `w9_endpoint_into_wg0` (a peer with allowed IPs
  not covering its endpoint); and A2: Linux ran `wg_xmit` inside the tx
  worker's section.
- **W9-M7** the IPv4 generation not bumped by `wg_deladdr`: the cache hits
  in the mirror and misses in Linux (A2 at `:51`), and the mirror skips
  `inet_confirm_addr` where Linux clears the source.
- **W8-M1** `wgNetnsPreExit` does not clear `creatingNet`: `wg_up` returns 0
  in the mirror, `ENONET` in Linux (`w8_down_exit_up`).
- **W8-M2** it does not NULL the sockets: in W8b the retransmit's `send4`
  sends in the mirror; Linux's `tx_bytes` unchanged; the kind-303 arm
  record absent for a data send (`w8_up_exit_keepalive`).
- **W8-M3** `.setDevNoCreatingNet` missing: the ACK differs (`w8_exit_set_port`).
- **W8-M4** the `cleanup_net` section not consumed (the mirror ignores it):
  `hidden_mismatch` on the unconsumed start record; and the control: the
  section's absence (a trace in the plain mode that the mirror wrongly
  expects to exit) fails the same way.
- **W8-M5** `qdiscNoop` not set by the linkwatch run (W8b): the mirror
  reaches `wg_xmit` for a `wg_xmit` after the exit, Linux does not (A2:
  Linux ran no `wg_xmit`); `tx_errors`/`tx_bytes` unchanged in Linux.
- **W8-M6** `.socketInitNoNet` tested on `sock4.isNone` instead of
  `creatingNet`: every plain `wg_up` fails in the mirror — rejected by the
  whole suite; recorded as a sanity mutant, not claimed as new evidence.
- **Controls**: `opened = 0` sections of the two new symbols across the
  regression suites (W8-0); the profound re-entry (`w9_endpoint_in_allowed_ips`,
  a control suite of its own, must stop `unsupported`); the record inventory
  of `wg_netns_close` must show no undeclared consumer.

**Not claimed:** the `src_if4` mismatch and `-EINVAL` arms (stretch); the
IPv6 bind retry; the `maybe_get_net`-fails window.

## 8. Out of scope (fail-noisy), and why

| Item | Why it waits |
|---|---|
| `-ENONET` through a failed `maybe_get_net` (`socket.c:378`, count zero before `cleanup_net` ran) | a scheduling window the operation's wait closes; reaching it needs a `wg_up` between `__put_net` and the kworker's run, which the guest cannot order (P5-class) |
| a second re-entry level (an endpoint covered by a peer's allowed IPs and routed into `wg0`) | unbounded (section 2.6): `unsupported` at `xmitDepth = 1`; a control trace shows the stop |
| `send4`'s `-EINVAL` operand (`:62-63`) | needs a configured multicast, limited-broadcast or zeronet local address (`route.c:2706-2712`) *and* a datagram delivered to it (so that `inet_confirm_addr` passes): an `ifa` in `224/4` on `lo` with `IP_ADD_MEMBERSHIP` and `IP_MULTICAST_IF` on the injector. Reachable, contrived; **stretch W9-S1**, reported with its recipe, not built unless asked |
| the `src_if4` mismatch (`:64`) | the reply must leave by a device other than the one the datagram arrived on (`lo`, 1): an endpoint off loopback learned *from a received datagram*, which needs a non-local source address on the injector (`IP_TRANSPARENT` + a bind to e.g. `192.0.2.1`; loopback output keeps its dst, `loopback.c:84`, `ip_input.c:364`, so no martian check runs). Then the reply routes into `wg0` (3 ≠ 1): the arm fires, the second lookup re-enters `wg0` (W9.5). **Stretch W9-S2**, same treatment |
| fwmark-dependent routing | no fib rules on this config (section 2.6); `CONFIG_IP_ADVANCED_ROUTER=y` would lift it — a kernel config change for the user's approval |
| `IFF_RUNNING`/`operstate` | set by the unarmed, up-to-1 s-delayed linkwatch work for a down device; masked from `flags` |
| `wg_create` from a foreign namespace inside a window; moving `wg0` with `RTM_SETLINK` | the same `wg_newlink` with another `src_net`; `dev_change_net_namespace` is core code with no WireGuard decision |
| timers due inside `wg_netns_close`'s wait | `unsupported`; the generator keeps keepalive peers and pending advances away from it |
| `wg_inject` after the close in the foreign-creator mode | no socket in C; `unsupported` |
| a datagram to a closed-port endpoint in C | ICMP to the kernel socket, unobservable; the existing `unsupported "a datagram to a port other than wg0's"` stays |
| the netns exit's effect on E's ratelimiter or on `wg_destruct` | none: both are per device or global, not per namespace |

## 9. Risks

- **High: the kind-305 records are an oracle change** (J2). Without
  approval W9's cache decision cannot be exact; the fallback J3 is
  fail-open and needs its own authorization. Decision 11.3.
- **Medium: the `cleanup_net` section's contents.** Unknown consumers and
  unknown coverage volume (section 3.2). W8-0 measures both; each
  consumer becomes a justified cut entry or stops the design.
- **Medium: the parent's pin and the opened-section check.** If the
  pin is opened late (after the child's namespace already changed) or
  closed early, D's `cleanup_net` opens a section after the readout and
  every network trace fails. Fail-noisy; W8-0 runs the regression suites
  with the two symbols armed and requires zero sections.
- **Medium: the foreign-creator descriptor layout** touches
  `initialKernel`, the Runner's literal domain (`Runner.lean:70` in L's
  numbering) and `observe`'s `null` fields for closed descriptors. Confined
  to the mode's traces.
- **Low: `send4`/`send6` inlined.** Then their lines are the callers'; the
  map names the callers and the decisions keep their lines. W9-0 checks
  `System.map`.
- **Low: the wait after `wg_netns_close`.** 200 ms against a few
  milliseconds of teardown; the trace bound (4 s) absorbs it. A stop that
  outlives the wait is a pending stop at the operation's end — noisy.
- **Low: `linkwatch_event` for `lo`.** `lo` is brought up before any window;
  no carrier change in a window. W8-0's zero-section requirement covers it.
- **Sequencing.** W8b (the up case) needs W9's `send4` and D3's advance;
  W8a and W9's core are independent of each other; both need L and D3.

## 10. Execution plan

Worktrees `task/w8-*` and `task/w9-*` on the integrated base; signoff at
the end covering the merge and, for W9, the oracle change. Streams:

**W8-0 — Linux-only probe (first; one VM slot briefly; no mirror change).**
The guest gains the foreign-creator fixture, the parent pin and opcode 18;
`cleanup_net` and `linkwatch_event` are armed. Traces: `w8_down_exit_up`
(set, close, `wg_up` → `ENONET`, `wg_get`, `wg_observe` for `flags`),
`w8_exit_set_port` (`EPERM`), `w8_up_exit` (up, a completed handshake, close,
`wg_observe`), plus the regression suites. Checklist: the section opens
inside the operation (its start record's position; whether a resched
record precedes `wg_netns_pre_exit`'s decisions); the duration to the
stop; the PC and comparison counts of the operation against `CAPACITY`;
the record inventory inside the section (sites, counts, frames); the
`linkwatch_event` section's position for the up case and its absence (or
delayed presence) for the down case; `opened = 0` in every other trace;
`IFF_LOWER_UP` in `flags` before and after; the `ENONET`/`EPERM` results;
`wg_delete` after the exit; `wg_socket_init`'s refcount comparison frames
(the two call lines for the exclusions).

**W9-0 — Linux-only probe.** `t send4`/`t send6` in `System.map`; the
inject destination variants (the reply's source at the sender for
`loopback`, `wg0`, `loopback-alias`); `wg_deladdr`/`wg_delroute` outcomes
and the sends after them (`tx_bytes`, no datagram); an endpoint routed into
`wg0` with non-covering allowed IPs (`tx_errors`, the nested coverage); the
cut-record counts at the transmit; and, on a throwaway kernel with the
kind-305 hook, the record counts per operation and the resolved frames of
the six reset chains and the refresh.

**W8-G — guest and harness** (`harness/guest.c`: the mode, opcodes 18;
the parent pin; `flags`; `observe`'s `null`s; `harness/trace.py`,
`harness/linux.py`: `DISPATCH_SYMBOLS`, the mode, the mandatory close).

**W8-M — mirror** (`Leanux/Kernel/Defs.lean`: `Worker` + 2, the mode,
`netnsCHolders`; `Leanux/WG/Types.lean`: `carrier`, `qdiscNoop`;
`Leanux/WG/Device.lean`: `wgNetnsPreExit`, `linkwatchDoDev`;
`Leanux/WG/Socket.lean`: `socketInit`'s live arm; `Leanux/WG/Netlink.lean`:
`setDevice`'s `EPERM`; `Leanux/Kernel/Decision.lean`: the constructors and
`OperandExclusion` + 2; `Leanux/Env.lean`: `wgNetnsClose`,
`runNetnsCleanup`, the mode's rules, `flags`; `Leanux/Runner.lean`;
`correspondence/kcov.json`: `wg_netns_pre_exit`, `wg_socket_init`, the two
exclusions; `correspondence/README.md`).

**W9-K — kernel** (`kernel/patches/choice-stream.patch`: the two kind-305
sites; the identity file; `evaluator/check.py`: kind 305 as class
`jiffies`). The oracle change, for the user's approval before W9-M's full
check.

**W9-M — mirror** (`Leanux/WG/Socket.lean`: `send4`, `send6`, `DstCache`;
`Leanux/Env.lean`: `route4/6`, the generations, `deliverSent` with the
source, `xmitNested`; `Leanux/WG/Handshake.lean`, `Data.lean`: the calls;
`Leanux/WG/Types.lean`: `Peer.dstCache`, `SentDatagram.src`;
`Leanux/Kernel/Defs.lean`: the sites, the tables; `Decision.lean`;
`correspondence/kcov.json`: `send4`, `send6`).

**W9-G — guest and harness** (`harness/guest.c`: the inject destination,
opcodes 19-20; `harness/trace.py`: the fields; `harness/wg.py`: nothing).

**W-H — corpus, generator, mutants** (`scripts/wg-w89-corpus.py`,
`corpus/wireguard/w8_*.json`, `w9_*.json`, a control suite for the
profound re-entry; `evaluator/generate.py`: a `routing` class with the
inject destinations and the two fixture operations, and a `netns` class in
the foreign-creator mode; `scripts/wg-mutants.py`: section 7).

**W8b** (the up case): after W9-M and D3: `w8_up_exit_keepalive`,
`w8_up_exit_retransmit` (advance to the retransmit → `send4` `-ENONET`),
`w8_up_exit_xmit` (the deactivated queue).

**Integration:** the full check (all suites: `DISPATCH_SYMBOLS`,
`deliverSent` and the routing model changed), all mutants, the controls,
on the W9 kernel; the report with the section and record inventories;
signoff.

File ownership: W8 and W9 share `Leanux/WG/Socket.lean` (W8: `socketInit`;
W9: `send4`/`send6` — disjoint hunks), `Leanux/Env.lean` (W8: the mode and
`wgNetnsClose`; W9: routing and delivery), `Defs.lean`, `Decision.lean`,
`kcov.json`, `guest.c`, `trace.py` — all in disjoint regions; W9's
`deliverSent` rewrite lands first [AGENT], W8's mode rules follow it.

## 11. Decisions for the user, and open questions

1. **Scope**: W8 in two stages (W8a down, W8b up) and W9's core (sections
   1, 8); the stretch items W9-S1/S2 reported with recipes and not built.
2. **The foreign-creator fixture** (section 3.1): two namespaces, the
   device in D, the outer sockets in C, descriptors 8 (injector) and 9
   (pin), the mandatory `wg_netns_close`; the parent's pin of D.
3. **The kind-305 `jiffies` records at the dst cache** (section 4.1, J2):
   an oracle change (two lines in `net/core`), needing approval; the
   fallback J3 is fail-open and is not recommended. **Without a decision
   here W9's cache decision cannot be built exactly.**
4. **Arming `cleanup_net` and `linkwatch_event` for every network trace**
   (section 3.2), with the zero-section requirement as the regression
   guard.
5. **Listing `wg_socket_init` with two operand exclusions** (section 3.3),
   on the P-int precedent.
6. **`flags` as an observable with `IFF_RUNNING` masked** (section 6).
7. **The routing model in the environment** (`route4/6`, the generations,
   the address and route sets) replacing L's `routesViaWg0`, used by both
   the inner dispatch and `send4`/`send6`.
8. **Question:** should W8's mode keep the listeners in C (four closes, the
   plain `portBound`) or hold only the injector and the pin (two closes, a
   `portBound` of `{51998}`)? The design keeps them [AGENT: identical
   bound-port rules across modes].
9. **Question:** is the re-entry's first level worth modeling now (W9.5,
   bounded by non-covering allowed IPs), or should every datagram routed
   into `wg0` stay `unsupported` until W13 (two devices) gives it a
   natural use? The design models one level [AGENT: it is the C's
   control flow, it is observable through `tx_errors`, and W13's
   `wg0↔wg1` pair needs the same nesting].
10. **Question:** the `-EINVAL` and `src_if4` arms (W9-S1/S2): build them
    with the fixture recipes of section 8, or leave them as documented
    unreached arms? The user's "100% of reasonable" rule decides what
    "reasonable" means for an `IP_TRANSPARENT` injector.

## 12. Kernel claims inferred rather than read, for the probes

- `wg0`'s carrier is on from registration (`__LINK_STATE_NOCARRIER` never
  set; WireGuard calls neither `netif_carrier_on` nor `_off` outside
  `pre_exit`): inferred from `sch_generic.c:608-616` and the absence of
  carrier calls in `drivers/net/wireguard`; W8-0's `flags` before the
  close shows `IFF_LOWER_UP`.
- No sleep between `cleanup_net`'s section start and `wg_netns_pre_exit`
  (section 2.1): inferred from the code at `:604-632`; W8-0 checks for a
  resched record before the pre-exit's decisions.
- The wakeup of the netns kworker may preempt the trace process at the
  syscall's return (EEVDF): either placement is acceptable; W8-0 reports
  which occurs.
- `wg_netns_pre_exit` runs no hooked random or clock reader; the rest of
  `cleanup_net` may (the pernet exits of `lo` and `sit0`, the `proc` and
  sysctl removals): W8-0's inventory.
- `send4`/`send6` are out of line in this build: W9-0's `System.map`.
- The sender's `[::]:51998` datagram to `127.0.0.2:port` reaches `wg0`'s
  wildcard IPv4 socket with `daddr 127.0.0.2` (local delivery through the
  `127.0.0.0/8` local route, dst kept over `lo`): W9-0's
  `loopback-alias` inject, and the reply's source `127.0.0.1`.
- `net_xmit_errno(NET_XMIT_CN) = 0` so `sendto` into a deactivated `wg0`
  succeeds (W8b): W8-0's `w8_up_exit` observes the `sendto` result.
- The `fib_prefsrc` of the `127.0.0.0/8` local route is `127.0.0.1`
  (`fib_magic` with `ifa_local`): the same probe's reply source.
- `linkwatch_event` is urgent only for a running device
  (`link_watch.c:109-121`, read); its delayed run for a down device lands
  anywhere within 1 s — W8-0 reports where, and whether it is inside a
  later operation's window (then its section must be accepted at idle
  points, as the hidden-inputs table says).
