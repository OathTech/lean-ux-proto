# W8 + W9: netns exit, `-ENONET`/`-EPERM`, and `socket.c` routing — design, 2026-10-06

Status: **proposed, revision v2** [AGENT 2026-10-06], after a critical audit
whose findings and their dispositions are in section 13; the remaining user
decisions are in section 11. The direction is the user's [USER 2026-10-06]:
100% of reasonable single-CPU WireGuard; exclusions only for profound
reasons. The two workstreams are rows W8 and W9 of the
[coverage census](2026-10-06-wireguard-census.md).

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
network namespace in the fixture, one operation, two more dispatch symbols
(`cleanup_net`, `linkwatch_event`) armed **per trace**, and a quiescence rule
for namespace teardowns (no fixture namespace's `cleanup_net` may run while
any run is armed with it: section 3.2). The two symbols bring the armed set
to `KCOV_DISPATCH_MAX` (16). W9 needs **one small kernel change**: a kind-306
record of `jiffies` at the two places the dst cache stores it (section 4.1),
because the cache's hit/miss decision is a `jiffies` comparison the mirror
cannot otherwise compute. Without it W9's cache decision is fail-open, which
the project's rules forbid without explicit authorization. W9.5 (a datagram
routed back into `wg0`) stays `unsupported` until W5-W6's ICMP rules land
(section 2.6).

Coordinator allocations [AGENT], used throughout: wire opcodes — 14 `pipe2`
(the positional `OPCODES` table on `main` caused clashes; integration
switches to an explicit table), 15-17 L, 18 `wg_flood`/`wg_batch` (E-B, W4),
19 `wg_advance` (D3, renumbered from 14), 20-21 W2, **22 `wg_netns_close`**,
**23 `wg_deladdr`, 24 `wg_delroute`**; record kind **306** for the dst-cache
`jiffies` records (305 is A's allocation outcome); dispatch budget 12 now, +2
for W5-W6, +2 for W8 = 16 = `KCOV_DISPATCH_MAX`.

## 1. Targets

| # | Scope item | C entry | Observable through |
|---|---|---|---|
| W8.1 | the creating namespace exits while `wg0` lives on in another | `cleanup_net` (`net_namespace.c:595-677`) → `ops_pre_exit_list` (`:631-632`) → `wg_netns_pre_exit` (`device.c:409-428`) | the dispatch section of `cleanup_net`; everything below (the link flags change only for an up device: W8b, section 6) |
| W8.2 | `wg_socket_init` without a creating namespace | `socket.c:376-381` → `-ENONET` | `wg_up`'s `ioctl` errno (`ENONET`, device stays down); `wg_set` of `listen_port` while running |
| W8.3 | `wg_set_device` of `listen_port`/`fwmark` without a creating namespace | `netlink.c:513-521` → `-EPERM` | the ACK |
| W8.4 | `send4`/`send6` with a NULL socket (the device up, its sockets released by the exit) | `socket.c:41-44`, `:121-124` → `-ENONET` | the dump's `tx_bytes` unchanged; no datagram; no `wg_timers_data_sent` arm record (`send.c:251-256`) |
| W8.5 | carrier off → linkwatch → the queue deactivated | `device.c:418`; `link_watch.c:179-186` | the dispatch section of `linkwatch_event`; afterwards `sendto` into `wg0` succeeds, `wg_xmit` never runs and `tx_dropped` counts the datagram (section 2.2) |
| W9.1 | `send4`/`send6` as mirrored decisions | `socket.c:20-95`, `:97-166` | coverage (A2); the datagram's source address at the sender's `recvfrom` (already printed, `guest.c:575-600`); `tx_bytes` |
| W9.2 | the dst cache: hit or miss, resets, staleness | `dst_cache.c:39-64`, `include/net/dst_cache.h:77-80`; `socket.c:49,59,69,81,129,137,148,294,312`; `peer.c:36` | coverage of `socket.c:51`/`:131` and the arms only a miss runs |
| W9.3 | the cached source address no longer local | `socket.c:53-60` (`inet_confirm_addr`, `devinet.c:1470-1491`), `:133-138` (`ipv6_chk_addr`, `addrconf.c:1961-1966`) | the reply's source address at the sender |
| W9.4 | route lookup errors | `socket.c:61,74-79`, `:139-146`; `route.c:2714`, `ipv6/route.c:298` | `tx_bytes` unchanged; no datagram |
| W9.5 | an endpoint routed back into `wg0`: `wg_xmit` nested at the send | `socket.c:85` → `udp_tunnel_xmit_skb` → `dev_queue_xmit(wg0)` → `wg_xmit` (`device.c:141-234`) | `tx_errors` (`:231`); coverage of the nested `wg_xmit` inside the worker's section. **Deferred (W9-R)**: stays `unsupported "a datagram routed back into wg0"` (`Env.lean:217`) until W5-W6's ICMP rules land (section 2.6) |
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
— more than a few milliseconds: besides the `rcu_barrier`s on Tiny RCU, the
unregistration of `lo` and `sit0` goes through `netdev_run_todo`'s
`netdev_wait_allrefs_any` (`dev.c:10798-10860`: `rcu_barrier` and a doubling
`msleep` while a reference lingers). The probe measures it; the wait starts
at 500 ms (section 3.2). The record order places it exactly; the mirror
consumes the section where its start record is (section 3.4).

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
  callers: the handshake send worker for initiations (`send.c:21-44`, which
  ignores the return; the retransmit timer queues it), and the tx worker
  for data and keepalives (the keepalive timers and `wg_packet_send_keepalive`
  stage an empty packet that goes through the encrypt and tx workers;
  `send.c:242-256`: a failed send leaves `data_sent` false, so
  `wg_timers_data_sent` does not run and no kind-303 arm record appears),
  where `wg_socket_send_skb_to_peer` keeps `tx_bytes` unchanged
  (`socket.c:182-183`). The skb is freed (`:91`).
- **Carrier off** (`device.c:418`; `sch_generic.c:608-616`): the first
  `netif_carrier_off` on `wg0` (WireGuard never calls `netif_carrier_on`;
  the bit starts clear) sets `__LINK_STATE_NOCARRIER` and fires a linkwatch
  event. **The link flags change only for an up device**: `dev_get_flags`
  (`dev.c:8903-8925`) adds `IFF_RUNNING` (from `operstate`), `IFF_LOWER_UP`
  (from the carrier) and `IFF_DORMANT` only inside `if (netif_running(dev))`
  (`:8915-8921`); a down device reports the same flags before and after.
  **The linkwatch event is non-urgent in both modes**: `linkwatch_urgent_event`
  (`link_watch.c:109-121`) is false for a device that is not running, and
  for a running `wg0` its last clause `netif_carrier_ok(dev) && …` (`:120`)
  is false once the carrier is off (`iflink == ifindex` for `wg0`, no LAG).
  Its delay is `linkwatch_nextevent - jiffies` (`:139`), which is only
  nonzero within one second of a previous linkwatch run (`:217` sets
  `linkwatch_nextevent = jiffies + HZ` after a non-urgent run; a wrapped
  value is clamped to 0, `:151-152`); no other carrier change happens in
  the fixture, so the work is queued with delay 0 on `system_unbound_wq`
  (`:159`) and **runs promptly, inside the operation's wait**, in both
  modes — the mirror consumes its section deterministically inside
  `wg_netns_close` (section 3.2). `linkwatch_do_dev` (`:170-190`)
  recomputes `operstate` (`rfc2863_policy`, `:179`: down without carrier,
  so `IFF_RUNNING` goes with `IFF_LOWER_UP` for an up device) and, **for an
  `IFF_UP` device without carrier, `dev_deactivate`** (`:181-184`): the
  device's queue becomes `noop_qdisc` (`sch_generic.c:1286-1298`), so a
  later `dev_queue_xmit` takes the `q->enqueue` path (`dev.c:4510-4513`) and
  `noop_enqueue` (`sch_generic.c:642-647`) **increments `tx_dropped`**
  (`dev_core_stats_tx_dropped_inc`), frees the skb and returns
  `NET_XMIT_CN`, which `net_xmit_errno` maps to 0: **the sender's `sendto`
  succeeds, `wg_xmit` never runs, and `print_stats` shows the drop**. The
  queue is never re-activated: `dev_activate` returns early without carrier
  (`:1262-1264`), and in any case a later `wg_up` fails at `ndo_open`
  (`wg_socket_init`'s `-ENONET`) before `__dev_open` reaches `dev_activate`
  (`dev.c:1551-1559`). For a down device the only effect is `operstate`,
  which no fixture output decodes; for an up device the deactivation is a
  state the mirror must know, so `linkwatch_event` is an armed dispatch
  symbol in this mode (section 3.2, W8b).

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
`fib_inetaddr_event` (`fib_frontend.c:1459,1470`; the last address's
deletion goes through `fib_disable_ip(dev, NETDEV_DOWN, true)`, `:1464-1468`,
→ `fib_flush` → `:199`), `fib_netdev_event` (`:1506,1517,1521`),
`fib_disable_ip` (`:1442`), `fib_table_insert` (`fib_trie.c:1385`) and
`fib_table_delete` — **only if the deleted alias was ever looked up**
(`:1754-1755`, `FA_S_ACCESSED`, set by `fib_alias_accessed` at `:1571` in
`fib_table_lookup`, `fib_lookup.h:29-34`; a route deleted before any lookup
bumps nothing). IPv6: the cookie is
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

**What a datagram to `wg0`'s own address does** (audit M5). The sender's
`sendto(10.255.254.1:port)` takes the `RTN_LOCAL` route of that address,
whose `prefsrc` is the address itself (`fib_magic`, `fib_frontend.c:1095`;
`route.c:2835-2836`), so the datagram leaves as `10.255.254.1 →
10.255.254.1`. `wg0` therefore learns the endpoint **`10.255.254.1:51998`**
with `src4 = 10.255.254.1`, `src_if4 = 1`; `endpoint_eq` (`socket.c:258-271`)
is false against a previously learned `127.0.0.1:51998`, so
`wg_socket_set_peer_endpoint` **resets the dst cache** (`:294`). The reply
goes to `10.255.254.1:51998`: `inet_confirm_addr` passes (a configured
address), the route is `lo` with source `10.255.254.1`, and the wildcard
sender receives it with that source. The same holds for `fd00:ffff::1`. So
the environment's model of the sender must be **destination-dependent**:
`Env.senderSource` (`Env.lean:44-47`, today a constant loopback source) must
give `saddr = prefsrc(dst)`, `daddr = dst`, and `Env.isSender`
(`Env.lean:38-39`, today exactly `127.0.0.1`/`::1`) must model the
**wildcard bind**: port 51998 at any local address (`127/8`, `::1`, `wg0`'s
addresses).

**Where today's mirror is wrong.** For a `to: wg0` inject today's mirror
stops with `unsupported "a datagram routed back into wg0"` (`Env.lean:217`:
the endpoint `10.255.254.1` is neither the sender nor a listener nor
loopback) — fail-noisy, not wrong. The rule "over loopback the source is
the destination's own address" (`Env.lean:206-213`) is wrong exactly when
the destination differs from its route's `prefsrc`: an endpoint
**`127.0.0.2:51998`** (set with `wg_set`). Linux routes it through the
`127.0.0.0/8` local route, replies from `127.0.0.1`, and delivers to the
wildcard sender; today's mirror (`isSender` false for `127.0.0.2`, no
listener, inside `127/8`) **drops it silently** as "another loopback port
with no socket" — a latent fail-open in `deliverSent`, a drop rule standing
where Linux delivers. W9's `isSender` and `route4` make this a checked case
(section 7, W9-M1).

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
IPv6 address and route (L, section 2.2); a `wg_up` restores them. Deleting
`wg0`'s only IPv4 address while up removes the default route as well
(`fib_inetaddr_event` NETDEV_DOWN: `fib_del_ifaddr`, then, the list being
empty, `fib_disable_ip(dev, event, true)` → `fib_sync_down_dev` marks every
nexthop via `wg0` dead and `fib_flush` removes them, `fib_frontend.c:1461-1469`,
`:1437-1444`). W9 adds operations that delete the default route or the
address while up (section 4.3) so that the error arms are reached on a
running device.

**Re-entry.** When the endpoint routes into `wg0` — any non-loopback
endpoint while the default route exists — `udp_tunnel_xmit_skb` →
`iptunnel_xmit` → `ip_local_out` → `dev_queue_xmit(wg0)` → **`wg_xmit`,
synchronously inside `send4`**, in the sending worker's task (or the trace
process for a reply from `wg_set`'s keepalive). `wg_xmit` (`device.c:141-234`)
then looks the outer UDP datagram's destination up in the allowed IPs:
- **no peer** (`:153-162`): `icmp_ndo_send` (`:226-227`), **`tx_errors`
  incremented** (`:231`), `kfree_skb`. Bounded and observable (`print_stats`
  reports `tx_errors`), but the ICMP error path has a **hidden-input
  footprint** of its own (audit M7): the global ICMP credit's draw
  (`icmp.c:268`, `get_random_u32_below(3)`, a cut consumer today only at
  `wg_xmit`'s own ICMP arm), `inet_getpeer_v4` (`:328`) and its `GFP_ATOMIC`
  slab allocation (`inetpeer.c:232`, an A kind-305 outcome), the per-peer
  `xrlim` on `jiffies` (`:245`, `:310-330`, with `sysctl_icmp_ratelimit =
  HZ`, `:1545`), the ICMP's own `__ip_select_ident` (`route.c:497`, a kind-110
  record at a new chain) and its local delivery over `lo` as a NET_RX
  section nested at the send, ending at the kernel UDP socket's `udp_err`.
  W5-W6 own the ICMP rules (`icmp_ratelimit=0` and the inventory); **W9.5
  waits for them (W9-R)** and stays `unsupported` meanwhile;
- **a peer whose endpoint is on loopback** (two peers): one more cycle,
  bounded; part of W9-R;
- **a peer whose allowed IPs cover the endpoint and whose endpoint routes
  into `wg0` again** (the usual `0.0.0.0/0` peer with such an endpoint):
  every cycle wraps the datagram again and re-queues the encrypt worker;
  past the MTU the IP layer fragments (`ignore_df`, `socket.c:84`) and the
  packet count grows. `XMIT_RECURSION_LIMIT` (`netdevice.h:3302`) does not
  bound it: each cycle crosses a work item. The loop ends only at deletion
  (`wg_allowedips_remove_by_peer`). **Profound exclusion** (section 8).

When W9-R lands, the nested `wg_xmit`'s coverage lands inside the worker's
section, like the NET_RX softirq the mirror already nests at the send
(`loopbackSend`), and the mirror's `wgXmit` runs nested at depth 1 with the
second level `unsupported`. Until then `send4`/`send6` stop at a route
whose device is `wg0` with the existing message.

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
  `wg0` learns from a loopback inject is unchanged (`127.0.0.1:51998`,
  `::1:51998`) and `Env.isSender` and `portBound` (`{51998, 51999}`) keep
  their meaning. The listeners **must** be in C (audit m7): `wg0` sends in
  C, and only a socket in C can receive. Plus the **pin**, descriptor 9:
  `open("/proc/self/ns/net")` while in C, the reference the operation drops.
  Of W9's inject destinations (section 4.3) only `loopback` and
  `loopback-alias` exist in C (`127/8` is local there); `to: wg0` names an
  address of D, unroutable from C: `unsupported` in this mode.

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
and D then die after exit, under the quiescence rule of section 3.2).

### 3.2 The operation `wg_netns_close`, the dispatch set, teardown quiescence

**`wg_netns_close {op}`** (wire opcode **22**, the coordinator's allocation):
inside the window, `close(9)`, `close(8)`, `close(5)`, `close(4)` in that
order, then the guest waits `NETNS_WAIT_US` (**500 ms** [AGENT], sized by
the probe against the measured teardown, within the 4 s bound: one such
operation per trace) before the readout, like the queueing operations'
`QUEUE_WAIT_US` (`guest.c:940`). Each close is an anchored FS syscall the mirror already
models (`__x64_sys_close` → `file_close_fd` → `filp_close` → `fput`): the
operation is four mirrored closes of fixture files. The UDP sockets'
`put_net` runs in their RCU-deferred destructors (`udp.c:330`,
`SOCK_RCU_FREE`), the pin's in `nsfs`'s release; whichever is last queues
`cleanup_net`. The result is 0; a close error is an environment failure
(the descriptors are the fixture's).

The mirror's `Env.wgNetnsClose`: the four `close`s through `Syscalls`;
`World.netnsCHolders := []`; then **`runWorker .netnsCleanup
WG.netnsPreExit`** consuming the section's start record, the pre-exit's
decisions, and the stop. The `linkwatch_event` section (non-urgent, delay
0, queued at `device.c:418` under `rtnl`, section 2.2) runs on another
unbound worker when the netns kworker sleeps (`net_namespace.c:648`'s
`netdev_run_todo`, `:663`) or after its stop, still inside the wait:
`runNetnsCleanup` accepts the `.linkwatch` section interleaved with or
following the `.netnsCleanup` section (and runs `WG.linkwatchDoDev`), the
ambient scheduler site anywhere, and nothing else; both stops must arrive
before the operation ends (no pending stop: `Runner.executeTrace` already
requires none). A timer section there is `unsupported "a timer section
inside the netns cleanup"` (the generator places no due timer in the wait:
section 10).

**The dispatch set** gains `cleanup_net` and `linkwatch_event`
(`harness/linux.py:39-44`, `DISPATCH_SYMBOLS`; the mirror's `Worker` gains
`.netnsCleanup` and `.linkwatch` with those symbols, `Defs.lean:241-262`,
and `check.py:852-854` keeps requiring every section site to be in the set).
**Budget**: the armed set is 12 today, W5-W6 add 2, W8 adds 2: **16, which
is `KCOV_DISPATCH_MAX`** (`kernel/patches/choice-stream.patch`, the
`kcov_dispatch` table). Any later symbol (W13 or anything else) needs the
cap raised — a kernel change; section 11 proposes folding a raise to 32 into
W9-K's patch, which is an oracle change anyway.

**How the kernel arms** (verified in the patch, `kcov_dispatch_start`):
there is one global armed instance (`kcov_dispatch_kcov`) and one global
function table (`kcov_dispatch.funcs`, loaded by `KCOV_LEANUX_DISPATCH_LOAD`,
`guest.c:670`); **any task or softirq that dispatches an armed function while
any instance is armed opens a section under that instance**, whoever queued
the work. So an asynchronous `cleanup_net` left over from a *previous* run
— the fixture namespace D dying after its trace process exited, with
`netdev_wait_allrefs_any`'s `rcu_barrier`s and `msleep`s still in flight —
opens a section in the *next* run's area if that run arms `cleanup_net`,
and `section_problems` (`check.py:358-372`, `opened ≠` recorded starts)
fails it (audit C1). **Invariant: no fixture namespace's `cleanup_net` runs
while any run is armed with `cleanup_net`.** Two measures establish it,
both taken:
- **(a) Per-trace arming.** The wire carries, per trace, the subset of
  `DISPATCH_SYMBOLS` to arm (today's 12 for every network trace; plus
  `cleanup_net` and `linkwatch_event` for foreign-creator traces only;
  `trace.py:190-205`, `linux.py:436`); the guest loads that subset before
  the fork. A run that does not arm `cleanup_net` cannot be hurt by a stale
  teardown, and `check.py:852-854`'s rule (section sites ⊆ the full set)
  is unchanged.
- **(b) Teardown quiescence.** For a foreign-creator trace, C dies inside
  `wg_netns_close` (mandatory, section 3.1) and D must not die while a
  later foreign-creator run is armed. The batch process (the guest's top
  level, which forks the per-trace parents, `guest.c:1136`) therefore
  **holds a pin on D** — `/proc/<child>/ns/net`, opened after the child
  signals its fixture is built, before any window — **until the batch
  ends**, so D's teardown runs after the last disarm. The cost is one idle
  namespace (`lo`, `sit0`, its sysctl and proc trees) per foreign-creator
  trace for the batch's lifetime; W8-0 measures it. If memory forbids it,
  the fallback (b2) is a fixed quiescence wait by the batch process after
  releasing a pin, with the next run's `opened = 0` as the guard
  (fail-noisy, not silent). A plain trace's D needs no pin under (a).
- **The control.** W8-0 runs the regression suites **twice in a row, armed**,
  and requires `opened = 0` in every trace of both runs; the second run is
  the one that would see a stale teardown.

Consequences, each closed:
- **Record inventory inside `cleanup_net`.** The section covers the whole
  teardown of C (`lo` and `sit0` unregistered, every pernet `exit`); its
  random and clock consumers are unknown until measured. The allocations on
  the path — `rtnl_net_notifyid`'s message before `pre_exit`, the exits'
  frees after it — are **A's kind-305 outcomes**, declared as cut consumers
  of the `.netnsCleanup` cut point under A's rule for allocations outside
  modeled paths (audit m8). Any other consumer than those and the ambient
  scheduler site becomes a declared cut consumer with a justification, or
  the trace is `hidden_mismatch`; the mirror runs nothing of it beyond
  `wg_netns_pre_exit`.
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
  cleared by `wgNetnsPreExit`. `Device.operUp : Bool := true` — the
  `operstate` the linkwatch run derives from it (`rfc2863_policy`). Both
  reach an observable only on an up device (W8b's `flags`, section 6).
- `Device.qdiscNoop : Bool := false` — set by the linkwatch run on an up
  device without carrier (`link_watch.c:181-184`); **never cleared**: a
  later `wg_up` fails at `ndo_open` before `dev_activate` (`dev.c:1551-1559`),
  and `dev_activate` would return early without carrier anyway
  (`sch_generic.c:1262-1264`); it ends with the device. While set, `Env`'s
  `wg_xmit` dispatch returns the datagram's length, runs nothing, and
  **`txDropped += 1`** (`noop_enqueue`, section 2.2; `print_stats` reports
  it).
- `World.fixtureMode : .plain | .bare | .foreignCreator`; `World.netnsCHolders
  : List Fd` (`[9, 8, 5, 4]`), emptied by the operation; the mode's fixture
  files at 8 and 9.

Functions (`Leanux/WG/Device.lean`, `Socket.lean`, `Netlink.lean`, `Env.lean`):

| Mirror | C | Notes |
|---|---|---|
| `wgNetnsPreExit` | `device.c:409-428` | over `device_list` (one device: `.preExitDevIter`), `.preExitCreator` (`creating_net == net`, true in this mode), `carrier := false`, `creatingNet := false`, `socketReinit none none` (L's decisions: `.reinitHasNew4` false, `.sockFreeNull` ×2 by whether the device was up), per peer `.preExitPeerIter` → `clearPeerEndpointSrc` (`endpoint.src := 0, srcIf := 0` — the `src6` union only, `socket.c:311`; `scope` lives in `addr6` and stays; `dstCache := .empty`) |
| `linkwatchDoDev` | `link_watch.c:170-190` | data only, no anchored decision: `operUp := carrier`; `qdiscNoop := running && !carrier`; run by `runWorker .linkwatch` inside `wg_netns_close` |
| `socketInit` | `socket.c:376-381` | `.socketInitNoNet` becomes a live decision on `!creatingNet` → `-ENONET` (L declared it constant false); listed in `kcov.json` with two operand exclusions (below) |
| `setDevice` | `netlink.c:513-521` | new decision `.setDevNoCreatingNet` at `:517`: with a port or fwmark attribute, `!creatingNet` → `-EPERM` before `deviceUpdateGen` moves; the `ns_capable` operand constant true (section 2.2) |
| `send4`/`send6` `.sock4Null`/`.sock6Null` | `socket.c:41`, `:121` | W9's functions (section 4.2); in W8a (device down) unreached; in W8b reached from the timers' and keepalive paths |
| `Env.wgUp` | | the L rule stays; `wgOpen`'s `socketInit` now returns `-ENONET` → `running := false`, `ioctl` fails `ENONET`; `Env.routesViaWg0` stays false |
| `Env.observe` | `print_stats` | W8b, if decision 11.6 adopts it: adds `flags` (section 6); W8b: `txDropped` already reported |

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
A2-checked. The cmpxchg loop (`:147`) and the two-operand lines (`:152`,
`:269`, `:274`) may each produce more than one comparison record per call
(audit m6); W8-0 enumerates the records at the two call sites and the
exclusions name every comparison line that appears, one label each. With
that, `.socketInitNoNet` (`:380`), `.socketInitV4Err`
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
  `wg_inject` with `to: loopback-alias` works in C (`127/8` is local there,
  the reply from `127.0.0.1` reaches the wildcard injector); `to: wg0` does
  not (`unsupported`, section 3.1).
- **After `wg_netns_close`.** `wg_inject` has no socket in C: `unsupported`
  (the generator never injects after the close). `wg_observe` drains the
  sender (D) and prints the listeners and injector as absent (`null`,
  like `stats: null`); the mirror's `observe` mirrors that from
  `netnsCHolders`. `wg_up` → `ENONET`; `wg_set` with port/fwmark → `EPERM`;
  `wg_delete` works (`wg_destruct` tolerates a NULL `creating_net`, L
  section 2.4).
- **`portBound` is C's**: `{51998, 51999}`, as in the plain fixture (the
  listeners are in C by necessity, section 3.1).
- **Carrier and flags.** For a down device nothing observable changes
  (`dev_get_flags`, section 2.2). For an up device (W8b), after the
  linkwatch section: `flags = IFF_UP | (if operUp then IFF_RUNNING) | (if
  carrier then IFF_LOWER_UP)` — both cleared by the exit — reported only if
  decision 11.6 adopts the observable; and every `wg_xmit` afterwards is a
  `txDropped` increment with no `wg_xmit` run.

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
  (a `sendto` into `wg0` that runs nothing and counts `tx_dropped`). W8b
  needs D3's advance and the armed `linkwatch_event`; it is a second stage
  after W9's `send4`/`send6` land, since the `-ENONET` arm is theirs.

## 4. W9: the design

### 4.1 The hidden input: `jiffies` at the dst cache — a kernel change

Section 2.4 shows the cache's hit/miss is `time_after(refresh_ts,
reset_ts)` on two `jiffies` stores the mirror cannot see. The options, with
the project's rules applied:

| | Option | Verdict |
|---|---|---|
| J1 | derive `jiffies` from the recorded clock reads (on the D3 oracle every coarse read is tick-granular, so each record pins a jiffy) | **insufficient**: neither the reset (`socket.c:294` in the receive worker; `peer.c:36` in `wg_set`) nor the access (the tx worker's `send4`) has a clock record at it; the two are bracketed by the same records most of the time, so the comparison is undetermined in exactly the common case |
| J2 | **record `jiffies` where the cache stores it**: `kcov_choice_ip(306, _THIS_IP_, &jiffies, 8)` at `dst_cache.h:79` (`dst_cache_reset`, inline — `_THIS_IP_`, not `_RET_IP_`, because an inline's `_RET_IP_` is the enclosing function's return address; the DWARF inline chain then resolves the site to `dst_cache.h:79` under each caller's frame; a `noinline` helper is the alternative) and `dst_cache.c:62` (the refresh on a miss) | **recommended** [AGENT]; the coordinator approves it subject to the user's approval of the kernel change. One kind, two sites, in `net/core` (unanchored), generic for every `dst_cache` user in the kernel. The mirror stores the recorded value in its own cache state and computes `time_after` itself: the decision stays computed, the input is recorded — the same shape as D3's kind-303 arm record, which closed the `jiffies`-at-`mod_timer` gap (D3, section 3.3). An oracle change: a patch on `kernel/patches/choice-stream.patch`, a new identity, **user approval** |
| J3 | declare `socket.c:51` and `:131` as `known_gaps` (hits reported, not failed) and model the cache as always missing | **fail-open** at the one decision that gates `:53-82`; the arms would be unverified. Forbidden without explicit authorization; listed only as the fallback if J2 is refused |
| J4 | an environment rule "a reset and the next access are in the same jiffy iff in the same operation" | wrong in 1-5% of handshakes (section 2.4); a wrong prediction fails the trace (A2), so it is noisy, but as a flake rate over 1,400 traces it is not acceptable |
| J5 | force a tick between every reset and send with guest waits | impossible inside one worker chain (the receive worker's reset and the keepalive's send) |

With J2 the mirror's cache is exact: `DstCache := { resetTs : Nat, slot :
Option { refreshTs : Nat, src : Nat, gen : Nat } }` per peer;
`dstCacheReset` consumes a kind-306 record (`.dstCacheResetTs`) into
`resetTs`; `dstCacheGet` decides `slot.isSome && refreshTs > resetTs && gen
== World.gen(family)`, and on a miss consumes the refresh record
(`.dstCacheRefreshTs`) into `refreshTs` (the C does both the comparison and
the store in `dst_cache_per_cpu_get`; on a hit no record). `dst_cache_reset_now`
is a reset record plus `slot := none`. `dst_cache_init` (`wg_peer_create`)
is a reset record. The record inventory per operation is bounded: one per
reset, one per miss. Steering is not needed (the value is consumed as data,
never chosen).

### 4.2 Mirror: `send4`/`send6`, the routing function, the sender model

**State.** `Endpoint` already carries `src`, `srcIf`, `scope`
(`Types.lean:52-60`). Add `Peer.dstCache : DstCache` (above).
`SentDatagram` gains `src : Nat` (the source `send4` chose) and keeps
`sport` (L); `InboxDatagram.addr` for the sender's `recvfrom` becomes that
`src` instead of "the destination's own address" (`Env.lean:206-213`),
fixing the rule of section 2.5. `Env.isSender` becomes the **wildcard
bind**: port 51998 at any local address (`127/8`, `::1`, `wg0`'s addresses);
`Env.senderSource` becomes destination-dependent (`saddr = prefsrc(dst)`,
`daddr = dst`, `iif = 1`), so a `to: wg0` inject makes `wg0` learn
`10.255.254.1:51998` and reset the cache, as Linux does. `World` gains
`ipv4Gen`, `ipv6Gen` (bumped by the operations of section 4.3 and by
`wg_down`/`wg_up`'s route changes), `defaultRoute4Accessed : Bool` (set when
a lookup resolves through the default route — the sender's inner `sendto`,
`send4`'s outer lookup — so that `wg_delroute`'s generation bump follows
`FA_S_ACCESSED`, section 2.4), and a routing table abstraction:
`World.addrs4/addrs6 : List Addr` on `wg0`, `World.defaultRoute4/6 : Bool`
(replacing L's single `routesViaWg0`, which becomes `defaultRoute4 &&
defaultRoute6`), the loopback prefixes as constants.

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
fl.saddr`; if `dev = lo` → `World.sent` (delivered by `deliverSent` with
the source and the wildcard sender rule), if `dev = wg0` → `unsupported "a
datagram routed back into wg0"` (unchanged; W9-R replaces it with one
nested `wgXmit` level once W5-W6's ICMP rules exist, section 2.6). Return 0
for a transmitted datagram (the transmit's own outcome is invisible to
`send4`, section 2.3). `send6` likewise with
`.send6SrcNotLocal` (133-134, `src ≠ ::` and `src ∉ addrs6 ∪ {::1}`) and no
`srcIf` arm. `sendSkbToPeer`/`sendBufferToPeer` call them instead of the cut
(`Handshake.lean:402-416`, `Data.lean:135-150`); `loopbackSend`'s NET_RX
nesting stays for the `lo` case; E's `sendBufferAsReplyToSkb` passes `cache
:= none`. The IP-ident cut consumers (`.ipIdentKey`, `.ipIdentReserve`,
`.flowHashSecret`) stay at the send cut point, which is now the transmit at
`:85`/`:152`, one level down.

**`wg_socket_set_peer_endpoint`** (`socket.c:273-297`): already mirrored for
the endpoint; adds the reset record at `:294` (and `endpoint_eq`'s
`src`/`srcIf` comparison, `:258-271`, is already data). `clearPeerEndpointSrc`
(`:310-312`): the reset-now record. `wgPeerCreate`: the init record.

### 4.3 Harness: operations and observables

- **`wg_inject` gains a destination** (`trace.py` field `"to"`:
  `"loopback"` (default, today's `127.0.0.1`/`::1`), `"wg0"` (the fixture
  address `10.255.254.1`/`fd00:ffff::1`, reached through the local route
  over `lo`, `skb_iif` 1), `"loopback-alias"` (`127.0.0.2`; IPv4 only).
  The guest (`guest.c:853-863`) builds the sockaddr from it. What `wg0`
  sees (section 2.5): `loopback` — source `127.0.0.1`, `src4 = 127.0.0.1`;
  `wg0` — **source `10.255.254.1`** (the local route's `prefsrc`), so the
  endpoint becomes `10.255.254.1:51998`, `src4 = 10.255.254.1`, and the
  cache is reset; `loopback-alias` — source `127.0.0.1` (the `127/8` route's
  `prefsrc`), endpoint unchanged, `src4 = 127.0.0.2`. These make `src4` the
  sender's address, a configured address, or a non-configured local one —
  the three cases of `inet_confirm_addr`. In the foreign-creator mode only
  the first two destinations exist (section 3.1).
- **`wg_deladdr {op, family}`** (opcode **23**): `RTM_DELADDR` of the
  fixture's address on `wg0`, over L's temporary rtnetlink descriptor
  (`rtnetlinkRequest`), result the ACK (`0`, or `-EADDRNOTAVAIL` when
  absent). Environment, IPv4: `addrs4 := []`, the local route gone, **and
  the default route gone too** — it was the device's only address, so
  `fib_inetaddr_event` NETDEV_DOWN runs `fib_disable_ip(dev, event, true)`
  → `fib_sync_down_dev` → `fib_flush` (`fib_frontend.c:1461-1469`,
  `:1437-1444`; audit M3): `defaultRoute4 := false`, `ipv4Gen` bumped
  (`fib_flush` → `rt_cache_flush`, `:199`). Afterwards a `wg_delroute 4`
  returns `-ESRCH` and the sender's inner `sendto` fails `-ENETUNREACH`.
  IPv6: `addrs6 := []`, the local route gone, the default route stays (the
  IPv6 address removal does not disable the device's routes), `ipv6Gen`
  bumped through `addrconf`. `route_into_wg0(first = 0)` after a later re-up
  must then tolerate a missing IPv4 address: the L rule "the IPv4 add must
  fail `EEXIST` on a later up" becomes "must fail `EEXIST` unless a
  `wg_deladdr` removed it since" — the guest tracks it, fail-closed
  otherwise.
- **`wg_delroute {op, family}`** (opcode **24**): `RTM_DELROUTE` of the
  default route via `wg0`; result the ACK (`0` or `-ESRCH`). Environment:
  `defaultRoute := false`; IPv4's generation bumped **only if the route was
  ever looked up** (`defaultRoute4Accessed`; `fib_table_delete`,
  `fib_trie.c:1754-1755`; audit M4) — every trace that sent through `wg0`
  has looked it up, a trace that deletes it untouched has not; IPv6's
  sernum moves unconditionally (`fib6_del`). Afterwards the sender's inner
  `sendto` to a non-local destination fails `-ENETUNREACH` without reaching
  `wg0`, and `wg0`'s outer sends to a non-loopback endpoint hit
  `.send4RouteErr`.
- **`wg_set` endpoints off loopback** need no new operation
  (`WGPEER_A_ENDPOINT` is free-form today); with the default route deleted,
  `-ENETUNREACH` (W9.4); with it present they route into `wg0` (W9.5,
  `unsupported` until W9-R). An endpoint **`127.0.0.2:51998`** is the
  wildcard-sender case of section 2.5 (W9-M1).
- **Observables**: the sender's `recvfrom` source (already printed; the
  mirror now computes it) and the learned endpoint in the dump, the dump's
  per-peer `tx_bytes` (decoded by `harness/wg.py:252-253`), coverage;
  `tx_errors` with W9-R; W8b's `tx_dropped` and, if adopted, `flags`
  (section 6).

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

Hidden sites (`HiddenSite`, `Defs.lean`): `.dstCacheResetTs` (kind 306,
innermost frame `dst_cache.h:79` under the consumer frames `socket.c:59`,
`:69`, `:137`, `:294`, `dst_cache.c:150`, `:176` — six chains, one site
each, resolved through the DWARF inline chain of `_THIS_IP_`) and
`.dstCacheRefreshTs` (kind 306, `dst_cache.c:62`). W9-0 confirms the
resolved frames on the throwaway kernel before the site table is written.

## 5. Hidden inputs

| Site | Kind | Consumer frame | Role | Consumed by |
|---|---|---|---|---|
| `.sectionStart/.sectionStop .netnsCleanup` | 300/301 | `cleanup_net` | dispatch | `Env.wgNetnsClose` only |
| `.sectionStart/.sectionStop .linkwatch` | 300/301 | `linkwatch_event` | dispatch | inside `wg_netns_close` (`runNetnsCleanup`), interleaved with or after the `cleanup_net` section; both modes (non-urgent, delay 0: section 2.2) |
| `.dstCacheResetTs` | **306 (new)** | `dst_cache.h:79` through its six callers | mirror (data) | `dstCacheReset` |
| `.dstCacheRefreshTs` | **306 (new)** | `dst_cache.c:62` | mirror (data) | `dstCacheGet` on a miss |
| cut: the ambient scheduler site | 200+ | `deadline.c:1153` | ambient | anywhere (unchanged) |
| cut: A's allocation outcomes inside the `cleanup_net` section (`rtnl_net_notifyid`'s message before `pre_exit`; the exits after it) | 305 | measured by W8-0 | cut, under A's rule for allocations outside modeled paths | the `.netnsCleanup` cut point |
| cut: other consumers inside `cleanup_net` after `wg_netns_pre_exit` | ? | measured by W8-0 | cut, per entry with a justification | the `.netnsCleanup` cut point |
| the existing send-cut consumers (`ip_idents_reserve`, `__ip_select_ident`, `__flow_hash_secret_init`) | 110/104/1 | unchanged | cut | the transmit at `socket.c:85`/`:152` |

No steering is needed for either workstream. The kind number 306 follows
A's 305 (allocation outcomes) in the kind table of `evaluator/check.py`; the
class is `jiffies`, resolved by consumer frame like the clock readers.

## 6. Observables

- **`flags`** (W8b only, if decision 11.6 adopts it; in `print_stats`,
  `guest.c:528-559`): `ifi_flags & (IFF_UP | IFF_RUNNING | IFF_LOWER_UP)`
  from the `RTM_GETLINK` reply's header. `dev_get_flags` reports
  `IFF_RUNNING` and `IFF_LOWER_UP` only for a running device
  (`dev.c:8915-8921`; audit M1), so **a down device shows no change across
  the exit** and W8a has no such observable. For an up device the plain
  value is `IFF_UP | IFF_RUNNING | IFF_LOWER_UP`, and after `wg_netns_close`
  (carrier off; `operstate` down after the linkwatch section, which the
  operation consumes, so the value is deterministic — audit M2, m2) it is
  `IFF_UP` alone. The mirror: `if running then IFF_UP ||| (if operUp then
  IFF_RUNNING else 0) ||| (if carrier then IFF_LOWER_UP else 0) else 0`.
  What it pays for: on a trace that closes the namespace and observes
  without a later `wg_xmit` or timer, only `flags` rejects W8-M7 (section
  7); with a later `wg_xmit`, A2 rejects it anyway (no `wg_xmit` ran in
  Linux). A regression-safe addition (the check compares Linux and the
  mirror, not stored expectations).
- **`tx_dropped`** (W8b, already reported): one per `sendto` into the
  deactivated `wg0` (section 2.2).
- The `ioctl` errno of `wg_up` (`ENONET`), the ACK of `wg_set` (`EPERM`),
  of `wg_deladdr`, `wg_delroute`.
- The dump: `listen_port` (unchanged by the exit), per-peer `tx_bytes` and
  the learned endpoint (`10.255.254.1:51998` after a `to: wg0` inject).
- `stats`: `tx_errors` for the re-entry's `!peer` arm (W9-R).
- The sender's `recvfrom` source address (printed today, computed by the
  mirror from now on) and the listeners' datagrams; `null` for closed C
  descriptors.
- The kind-303 arm records of `wg_timers_data_sent` (absent after a failed
  send) and the kind-306 records (counts per operation).
- Coverage: `wg_netns_pre_exit`, `wg_socket_init`'s arms, `send4`/`send6`'s
  arms.

## 7. Evidence: what pays for itself

Each mutant names what no existing check catches; an `unsupported` counts
as rejected (`scripts/wg-mutants.py`).

- **W9-M1** today's delivery rule kept as a mutant: `isSender` exact on
  `127.0.0.1`/`::1`, a datagram to any other `127/8` port dropped silently,
  the source "the destination's own address" (`Env.lean:38-39, 206-217`).
  Rejected by `w9_endpoint_alias` (`wg_set` endpoint `127.0.0.2:51998`,
  `wg_xmit`, `wg_observe`): Linux's sender receives the datagram from
  `127.0.0.1`; the mutant delivers nothing (and a variant that delivers
  reports `127.0.0.2`). **The latent fail-open of section 2.5**: a drop
  where Linux delivers, unreachable by the current corpus. (The first draft
  claimed a `to: wg0` inject showed it; that inject stops `unsupported`
  today — audit M6.)
- **W9-M2** `.send4SrcNotLocal` never fires (`src4` kept): `w9_inject_to_alias`
  (inject to `127.0.0.2`): the mirror's reply source `127.0.0.2`, Linux's
  `127.0.0.1`; and A2 at `socket.c:53-60`. The real evidence for W9.3.
- **W9-M3** the cache never hits (every send misses): A2 at `:51` on the
  second send of `w9_two_sends` (needs J2).
- **W9-M4** the cache ignores the reset at `:294` (a changed endpoint keeps
  the old dst): A2 at `:51` after a roaming inject; and the stale source
  (`src` cached from the old endpoint) at the sender.
- **W9-M5** a route error still counts `tx_bytes`: the dump differs after
  `wg_delroute` + a send to an off-loopback endpoint (`w9_unroutable`).
- **W9-M6** (W9-R, not claimed now) the re-entry treated as a loopback drop
  (no nested `wgXmit`): `tx_errors` differs in `w9_endpoint_into_wg0` (a
  peer with allowed IPs not covering its endpoint); and A2: Linux ran
  `wg_xmit` inside the tx worker's section.
- **W9-M7** the IPv4 generation not bumped by `wg_deladdr`: the cache hits
  in the mirror and misses in Linux (A2 at `:51`), and the mirror skips
  `inet_confirm_addr` where Linux clears the source.
- **W9-M8** `wg_deladdr 4` keeps the default route: the mirror's
  `wg_delroute 4` returns 0 where Linux returns `-ESRCH`, and the inner
  `sendto` reaches `wg_xmit` in the mirror and fails `-ENETUNREACH` in
  Linux (`w9_deladdr_then_send`).
- **W9-M9** `wg_delroute 4` bumps the generation regardless of
  `FA_S_ACCESSED`: on `w9_delroute_untouched` (delete before any send
  through `wg0`, then a second send to a loopback endpoint) the mirror
  misses where Linux hits (A2 at `:51`).
- **W9-M10** `isSender` not a wildcard: a `to: wg0` inject's reply (to
  `10.255.254.1:51998`) is `unsupported` in the mirror while Linux's sender
  receives it (`w9_inject_to_wg0_addr`; today's behaviour, kept as a
  mutant).
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
- **W8-M7** (W8b, only with `flags`) `wgNetnsPreExit` keeps `carrier` true
  (so `linkwatchDoDev` leaves `operUp` and `qdiscNoop` alone): on
  `w8_up_exit_observe` (close, then observe, no later `wg_xmit`) only
  `flags` rejects it; on `w8_up_exit_xmit` A2 does.
- **W8-M8** (W8b) the deactivated queue does not count `tx_dropped`:
  `stats` differs on `w8_up_exit_xmit`.
- **Controls**: `opened = 0` in every trace of **two consecutive armed
  runs** of the regression suites (W8-0, section 3.2); a datagram routed
  into `wg0` (`w9_endpoint_into_wg0`, a control suite of its own) must stop
  `unsupported` until W9-R; the record inventory of `wg_netns_close` must
  show no undeclared consumer.

**Not claimed:** the `src_if4` mismatch and `-EINVAL` arms (stretch); the
re-entry (W9-R); the IPv6 bind retry; the `maybe_get_net`-fails window.

## 8. Out of scope (fail-noisy), and why

| Item | Why it waits |
|---|---|
| `-ENONET` through a failed `maybe_get_net` (`socket.c:378`, count zero before `cleanup_net` ran) | a scheduling window the operation's wait closes; reaching it needs a `wg_up` between `__put_net` and the kworker's run, which the guest cannot order (P5-class) |
| any datagram routed into `wg0` (W9.5) | **deferred to W9-R**, after W5-W6's ICMP rules (`icmp_ratelimit=0`, the ICMP inventory): the `!peer` arm's footprint of section 2.6 (the credit draw, `inet_getpeer`'s allocation, `xrlim`'s `jiffies`, the ICMP's ident, a NET_RX section). Stays `unsupported "a datagram routed back into wg0"`; a control trace shows the stop |
| a second re-entry level (an endpoint covered by a peer's allowed IPs and routed into `wg0`) | unbounded (section 2.6): profound; `unsupported` at depth 1 once W9-R models the first level |
| `send4`'s `-EINVAL` operand (`:62-63`) | needs a configured multicast, limited-broadcast or zeronet local address (`route.c:2706-2712`) *and* a datagram delivered to it (so that `inet_confirm_addr` passes): an `ifa` in `224/4` on `lo` with `IP_ADD_MEMBERSHIP` and `IP_MULTICAST_IF` on the injector. Reachable, contrived; **stretch W9-S1**, reported with its recipe, not built unless asked |
| the `src_if4` mismatch (`:64`) | the reply must leave by a device other than the one the datagram arrived on (`lo`, 1): an endpoint off loopback learned *from a received datagram*, which needs a non-local source address on the injector (`IP_TRANSPARENT` + a bind to e.g. `192.0.2.1`; loopback output keeps its dst, `loopback.c:84`, `ip_input.c:364`, so no martian check runs). Then the reply routes into `wg0` (3 ≠ 1): the arm fires, the second lookup re-enters `wg0` (W9.5). **Stretch W9-S2**, same treatment |
| fwmark-dependent routing | no fib rules on this config (section 2.6); `CONFIG_IP_ADVANCED_ROUTER=y` would lift it — a kernel config change for the user's approval |
| the link flags of a down device across the exit | nothing changes (`dev_get_flags`, section 2.2): no observable, nothing to model beyond `carrier` |
| `wg_inject` with `to: wg0` in the foreign-creator mode | `wg0`'s address is in D, unroutable from C's injector: `unsupported` |
| `wg_create` from a foreign namespace inside a window; moving `wg0` with `RTM_SETLINK` | the same `wg_newlink` with another `src_net`; `dev_change_net_namespace` is core code with no WireGuard decision |
| timers due inside `wg_netns_close`'s wait | `unsupported`; the generator keeps keepalive peers and pending advances away from it |
| `wg_inject` after the close in the foreign-creator mode | no socket in C; `unsupported` |
| a datagram to a closed-port endpoint in C | ICMP to the kernel socket, unobservable; the existing `unsupported "a datagram to a port other than wg0's"` stays |
| the netns exit's effect on E's ratelimiter or on `wg_destruct` | none: both are per device or global, not per namespace |

## 9. Risks

- **High: the kind-306 records are an oracle change** (J2). Without
  approval W9's cache decision cannot be exact; the fallback J3 is
  fail-open and needs its own authorization. Decision 11.3.
- **High: teardown quiescence** (section 3.2, audit C1). A stale
  `cleanup_net` from a previous run opens a section in the next armed run.
  Per-trace arming and batch-long pins establish the invariant; the pins'
  memory is unmeasured (one namespace per foreign-creator trace per batch),
  and the fallback is a fixed wait guarded by `opened = 0`. Fail-noisy
  either way; W8-0's two consecutive armed runs are the control.
- **High: the dispatch budget** (audit M10). W8's two symbols reach
  `KCOV_DISPATCH_MAX` (16). Any later symbol needs the cap raised, a kernel
  change; decision 11.11 proposes folding a raise to 32 into W9-K.
- **Medium: the `cleanup_net` section's contents.** Unknown consumers and
  unknown coverage volume (section 3.2). W8-0 measures both; each
  consumer becomes a justified cut entry or stops the design.
- **Medium: the foreign-creator descriptor layout** touches
  `initialKernel`, the Runner's literal domain (`Runner.lean:70` in L's
  numbering) and `observe`'s `null` fields for closed descriptors. Confined
  to the mode's traces.
- **Low: `send4`/`send6` inlined.** Then their lines are the callers'; the
  map names the callers and the decisions keep their lines. W9-0 checks
  `System.map`.
- **Low: the wait after `wg_netns_close`.** 500 ms against a teardown of
  more than a few milliseconds (`netdev_wait_allrefs_any`'s `msleep` loop,
  section 2.1); the trace bound (4 s) absorbs one such wait. A stop that
  outlives the wait is a pending stop at the operation's end — noisy. W8-0
  measures the teardown.
- **Low: `linkwatch_event` for `lo`, or a run within the previous second.**
  `lo` is brought up before any window; no other carrier change happens in
  a window; a global `linkwatch_nextevent` within one second of the close
  would delay the section up to 1 s (section 2.2). W8-0's zero-section
  requirement and its placement check cover both.
- **Sequencing.** W8b (the up case) needs W9's `send4` and D3's advance;
  W8a and W9's core are independent of each other; both need L and D3. W9-R
  needs W5-W6. Cross-stream: section 10's ownership note.

## 10. Execution plan

Worktrees `task/w8-*` and `task/w9-*` on the integrated base; signoff at
the end covering the merge and, for W9, the oracle change. Streams:

**W8-0 — Linux-only probe (first; one VM slot briefly; no mirror change).**
The guest gains the foreign-creator fixture, per-trace arming, the batch
pins and opcode 22; `cleanup_net` and `linkwatch_event` are armed for the
W8 traces. Traces: `w8_down_exit_up` (set, close, `wg_up` → `ENONET`,
`wg_get`, `wg_observe`), `w8_exit_set_port` (`EPERM`), `w8_up_exit` (up, a
completed handshake, close, `wg_observe`, a `wg_xmit`), plus the regression
suites. Checklist: the section opens inside the operation (its start
record's position; whether a resched record precedes `wg_netns_pre_exit`'s
decisions); **the teardown's duration to the stop** (sizing
`NETNS_WAIT_US`); the PC and comparison counts of the operation against
`CAPACITY`; the record inventory inside the section (sites, counts, frames;
the kind-305 allocations); the `linkwatch_event` section's position in
**both** modes (expected promptly, inside the operation); **two consecutive
armed runs of the regression suites with `opened = 0` in every trace of
both**; the memory held by the batch pins; the `flags` value before and
after on the up device (`IFF_UP|IFF_RUNNING|IFF_LOWER_UP` → `IFF_UP`) and
its invariance on the down device; **`tx_dropped`** after the `wg_xmit` in
`w8_up_exit`; the `ENONET`/`EPERM` results; `wg_delete` after the exit;
`wg_socket_init`'s refcount comparison records at the two call lines (how
many, which lines: the exclusions' labels).

**W9-0 — Linux-only probe.** `t send4`/`t send6` in `System.map`; **the
learned endpoint (dump) and the reply's source at the sender for all three
inject destinations** (`loopback`: `127.0.0.1:51998` / `127.0.0.1`; `wg0`:
`10.255.254.1:51998` / `10.255.254.1`; `loopback-alias`: `127.0.0.1:51998` /
`127.0.0.1`); the `127.0.0.2:51998` endpoint's reply reaching the wildcard
sender; `wg_deladdr`/`wg_delroute` outcomes and the sends after them
(`tx_bytes`, no datagram), **the default route after `wg_deladdr 4`** (gone:
`wg_delroute 4` → `-ESRCH`) and after `wg_deladdr 6` (kept); the
`FA_S_ACCESSED` rule (a delete before any lookup leaves a cached dst valid);
the cut-record counts at the transmit; the `!peer` arm's record inventory
on one re-entry trace, for W9-R only; and, on a throwaway kernel with the
kind-306 hook, the record counts per operation and **the resolved frames
of the six inline reset chains** (`_THIS_IP_` through the DWARF inline
chain) and the refresh.

**W8-G — guest and harness** (`harness/guest.c`: the mode, opcode 22;
per-trace arming; the batch pins and the fixture-ready signal; `observe`'s
`null`s; `flags` if adopted; `harness/trace.py`, `harness/linux.py`:
`DISPATCH_SYMBOLS` and the per-trace arm subset in the wire, the mode, the
mandatory close).

**W8-M — mirror** (`Leanux/Kernel/Defs.lean`: `Worker` + 2, the mode,
`netnsCHolders`; `Leanux/WG/Types.lean`: `carrier`, `operUp`, `qdiscNoop`;
`Leanux/WG/Device.lean`: `wgNetnsPreExit`, `linkwatchDoDev`;
`Leanux/WG/Socket.lean`: `socketInit`'s live arm; `Leanux/WG/Netlink.lean`:
`setDevice`'s `EPERM`; `Leanux/Kernel/Decision.lean`: the constructors and
`OperandExclusion` + 2; `Leanux/Env.lean`: `wgNetnsClose`,
`runNetnsCleanup`, the mode's rules, `txDropped` on the deactivated queue,
`flags` if adopted; `Leanux/Runner.lean`; `correspondence/kcov.json`:
`wg_netns_pre_exit`, `wg_socket_init`, the exclusions;
`correspondence/README.md`).

**W9-K — kernel** (`kernel/patches/choice-stream.patch`: the two kind-306
sites with `_THIS_IP_`; optionally `KCOV_DISPATCH_MAX` 16 → 32 (decision
11.11); the identity file; `evaluator/check.py`: kind 306 as class
`jiffies`). The oracle change, for the user's approval before W9-M's full
check.

**W9-M — mirror** (`Leanux/WG/Socket.lean`: `send4`, `send6`, `DstCache`;
`Leanux/Env.lean`: `route4/6`, the generations and `defaultRoute4Accessed`,
`isSender` as the wildcard bind, `senderSource` by destination,
`deliverSent` with the source; `Leanux/WG/Handshake.lean`, `Data.lean`: the
calls; `Leanux/WG/Types.lean`: `Peer.dstCache`, `SentDatagram.src`;
`Leanux/Kernel/Defs.lean`: the sites, the tables; `Decision.lean`;
`correspondence/kcov.json`: `send4`, `send6`).

**W9-G — guest and harness** (`harness/guest.c`: the inject destination,
opcodes 23-24; `harness/trace.py`: the fields; `harness/wg.py`: nothing).

**W-H — corpus, generator, mutants** (`scripts/wg-w89-corpus.py`,
`corpus/wireguard/w8_*.json`, `w9_*.json`, a control suite for the
datagram routed into `wg0`; `evaluator/generate.py`: a `routing` class with
the inject destinations and the two fixture operations, and a `netns` class
in the foreign-creator mode; `scripts/wg-mutants.py`: section 7).

**W8b** (the up case): after W9-M and D3: `w8_up_exit_keepalive`,
`w8_up_exit_retransmit` (advance to the retransmit → `send4` `-ENONET`),
`w8_up_exit_xmit` (the deactivated queue, `tx_dropped`),
`w8_up_exit_observe` (if `flags` is adopted).

**W9-R** (the re-entry's first level): after W5-W6's ICMP rules: the nested
`wgXmit`, `tx_errors`, W9-M6, the `!peer` arm's inventory as declared cut
consumers.

**Integration:** the full check (all suites: the per-trace arm subset,
`deliverSent` and the routing model changed), all mutants, the controls,
on the W9 kernel; the report with the section and record inventories;
signoff.

**Cross-stream ownership and sequencing** (audit M11). W1-W2, W4-W7 and
W5-W6 also edit `Leanux/Env.lean`, `Leanux/Kernel/Defs.lean`,
`Leanux/Kernel/Decision.lean`, `Leanux/WG/Device.lean`,
`Leanux/WG/Types.lean`, `harness/guest.c`, `harness/trace.py` and
`correspondence/kcov.json`. The shared surfaces and their single owners:
the explicit opcode table in `trace.py` (integration; the allocations in
the summary), `DISPATCH_SYMBOLS` and the per-trace arm subset (W8 adds
two symbols; W5-W6 add two; the order in the list is the wire's),
`Worker` and its section sites (each stream appends its constructors in
its own block, as D3 and L did), the `Decision` constructors and the
`kcov.json` function list (append-only blocks per stream), the fixture
modes in `Env`/`Runner` (L's `bare`, W8's `foreignCreator`), the routing
model (`route4/6`, the generations: W9 owns; W4's MTU and W5-W6's ICMP
rules extend it; L's `routesViaWg0` is retired by W9). **The interface
commit** — the opcode table, the arm-subset wire field, the retired
`routesViaWg0`, the `Worker` and `HiddenSite` blocks reserved per stream —
**comes after D3+L+A+E are integrated**, and every W stream branches from
it. Within W8/W9: `Leanux/WG/Socket.lean` (W8: `socketInit`; W9:
`send4`/`send6` — disjoint hunks), `Leanux/Env.lean` (W8: the mode and
`wgNetnsClose`; W9: routing, the sender model and delivery) — disjoint
regions; W9's `deliverSent`/`isSender` rewrite lands first [AGENT], W8's
mode rules follow it.

## 11. Decisions, with options and recommendations

Numbering is kept from v1; the coordinator's answers to the audit are
recorded as [AGENT] dispositions, the items that need the user are tagged
[USER].

1. **Scope** [AGENT, approved]: W8 in two stages (W8a down, W8b up); W9's
   core (sections 1, 8); W9.5 deferred to W9-R after W5-W6; the stretch
   items W9-S1/S2 documented with their recipes and **not built** (v1's
   Q10, resolved).
2. **The foreign-creator fixture** [AGENT, approved]: two namespaces, the
   device in D, the outer sockets in C, descriptors 8 (injector) and 9
   (pin), the mandatory `wg_netns_close`. The listeners are in C by
   necessity (v1's Q8, forced: audit m7).
3. **The kind-306 `jiffies` records at the dst cache** (section 4.1, J2)
   [USER: a kernel change]. Options: (i) **J2** — two lines in `net/core`
   with `_THIS_IP_`, kind 306, a new oracle identity; exact, generic,
   recommended [AGENT], approved by the coordinator subject to the user;
   (ii) J3 — `known_gaps` at `socket.c:51`/`:131` and a cache that always
   misses: fail-open at the decision that gates W9.3's arms, not
   recommended, and itself needing explicit authorization; (iii) defer the
   cache-dependent arms (`:48-82`, `:128-149`) and build only `:41`/`:121`
   and the family split now. **Without (i) W9's cache decision cannot be
   built exactly.**
4. **Arming `cleanup_net` and `linkwatch_event`** [AGENT, approved only
   with C1's measures]: per-trace arming plus teardown quiescence (section
   3.2). The quiescence mechanism is a sub-decision pending W8-0's memory
   measurement: (b1) batch-long pins — recommended [AGENT]: the invariant
   holds by construction; (b2) a fixed wait after releasing a pin with the
   next run's `opened = 0` as the guard — only if (b1)'s memory is
   prohibitive.
5. **Listing `wg_socket_init` with operand exclusions** (section 3.3)
   [AGENT, approved], one label per comparison line W8-0 finds at the two
   call sites.
6. **`flags` as an observable** [USER]. It does not exist for a down device
   (audit M1), so it leaves W8a. Options for W8b: (i) **drop it** —
   recommended default [AGENT]: `tx_dropped` and A2 already reject every
   carrier mutant on a trace with a later `wg_xmit`; (ii) add it in W8b
   with the trace `w8_up_exit_observe` and the mutant W8-M7 that only it
   rejects — worth it only if "close, then observe, no later send" is a
   shape the user wants covered on its own.
7. **The routing model in the environment** (`route4/6`, the generations,
   `defaultRoute4Accessed`, the address and route sets) replacing L's
   `routesViaWg0` [AGENT, approved with M3 and M4]; with it the sender
   model (the wildcard `isSender`, the destination-dependent
   `senderSource`).
8. (resolved: forced, see 2.)
9. (resolved: W9.5 stays `unsupported` until W5-W6, as W9-R.)
10. (resolved: W9-S1/S2 documented, not built.)
11. **The dispatch budget** [USER: a kernel change]. W8 fills
    `KCOV_DISPATCH_MAX` (16). Options: (i) **fold a raise to 32 into
    W9-K's patch** — recommended [AGENT]: W9-K is an oracle change anyway,
    and W13 or any later symbol would otherwise need its own; (ii) leave
    16 and accept that the next symbol is a kernel change of its own.
12. **The teardown wait** [AGENT]: `NETNS_WAIT_US` 500 ms, resized by W8-0's
    measurement; the trace bound absorbs one per trace.

## 12. Kernel claims inferred rather than read, for the probes

- `wg0`'s carrier is on from registration (`__LINK_STATE_NOCARRIER` never
  set; WireGuard calls neither `netif_carrier_on` nor `_off` outside
  `pre_exit`): inferred from `sch_generic.c:608-616` and the absence of
  carrier calls in `drivers/net/wireguard`; W8-0's `flags` on the up
  device before the close shows `IFF_LOWER_UP`.
- C's teardown completes within `NETNS_WAIT_US`, and no linkwatch run
  happened within the second before the close (the global
  `linkwatch_nextevent`): W8-0's durations and the section placements.
- The sender's datagram to `wg0`'s own address leaves from that address
  (the `/32` local route's `prefsrc`), and a reply to `127.0.0.2:51998` or
  `10.255.254.1:51998` reaches the wildcard sender: W9-0's endpoint and
  source checks.
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
- `linkwatch_event` is non-urgent in both modes and runs with delay 0
  (`link_watch.c:109-121`, `:137-160`, `:217`, read): W8-0 reports its
  section's position in both modes, expected inside `wg_netns_close`.

## 13. Revision v2 — audit response [AGENT 2026-10-06]

Each finding was checked against `.deps/linux` and the patch before being
adopted; where the audit's reasoning or citation differs from what the code
says, the note keeps the code and says so. "Adopted" means the sections
named were rewritten accordingly.

**Critical.**
- **C1 — stale `cleanup_net` sections in the next armed run. Adopted**
  (sections 3.2, 9, 10, 11.4). Verified in `kernel/patches/choice-stream.patch`:
  `kcov_dispatch_kcov` is a single global armed instance and
  `kcov_dispatch.funcs` a single global table; `kcov_dispatch_start` opens
  a section for any task or softirq dispatching an armed function while an
  instance is armed, with no test of who queued the work. v1's "parent pins
  D across the disarm" merely moved D's asynchronous teardown
  (`netdev_run_todo` → `netdev_wait_allrefs_any`, `dev.c:10798-10860`, with
  `rcu_barrier` and `msleep`) into the next run's armed window, exactly as
  the audit says. The invariant is stated; per-trace arming (a) and
  batch-long pins (b1, with the fixed-wait fallback b2) establish it; W8-0
  validates with two consecutive armed runs of the regression suites.
- **C2 — opcode 18 taken. Adopted**: 22 for `wg_netns_close`, 23-24 for
  `wg_deladdr`/`wg_delroute`; the coordinator's allocation table is in the
  summary.

**Major.**
- **M1 — `IFF_LOWER_UP` only when running. Adopted** (sections 2.2, 3.4, 6,
  8, 11.6). Verified: `dev.c:8915-8921` sets `IFF_RUNNING`, `IFF_LOWER_UP`
  and `IFF_DORMANT` inside `if (netif_running(dev))`. W8a's observable does
  not exist; `flags` is deferred to W8b as decision 11.6 with the mutant
  W8-M7 that only it rejects, default drop.
- **M2 — the linkwatch event is non-urgent and prompt in both modes.
  Adopted, with one caveat** (sections 2.2, 3.2, 5, 6, 8, 12). Verified:
  `linkwatch_urgent_event`'s last clause (`link_watch.c:120`) needs
  `netif_carrier_ok`, false once the carrier is off, and `wg0`'s `iflink`
  equals its `ifindex`; so v1's "urgent only if running" was wrong. The
  delay `linkwatch_nextevent - jiffies` (`:139`) is 0 unless a linkwatch
  run happened within the previous second (`:217` sets `linkwatch_nextevent
  = jiffies + HZ` after each non-urgent run; the wrap is clamped to 0,
  `:151-152`). **The caveat**: `linkwatch_nextevent` is global, so "0 here"
  holds because no other carrier event occurs in the fixture — a
  measurable claim (section 12) rather than a code fact; a delayed section
  would be fail-noisy (unconsumed). The "accepted anywhere at idle points"
  rule and the `IFF_RUNNING` masking rationale are removed; the section is
  consumed inside `wg_netns_close`.
- **M3 — deleting the last IPv4 address flushes the routes via `wg0`.
  Adopted** (sections 2.4, 2.6, 4.3, 7). Verified at `fib_inetaddr_event`
  (`fib_frontend.c:1461-1469`: `fib_del_ifaddr`, then with an empty
  `ifa_list` `fib_disable_ip(dev, event, true)`, `:1437-1444` →
  `fib_sync_down_dev` → `fib_flush`). The audit's cited lines `:1512-1521`
  are `fib_netdev_event`'s NETDEV_DOWN (`fib_disable_ip(dev, event,
  false)`), a different event with the same effect; the conclusion stands.
  `defaultRoute4 := false`; a later `wg_delroute 4` is `-ESRCH`; inner
  sends `-ENETUNREACH`; mutant W9-M8. IPv6 as in v1.
- **M4 — the delete-time genid bump is conditional on `FA_S_ACCESSED`.
  Adopted** (sections 2.4, 4.2, 4.3, 7). Verified: `fib_trie.c:1754-1755`;
  the flag is set by `fib_alias_accessed` (`fib_lookup.h:29-34`) called at
  `fib_trie.c:1571` in `fib_table_lookup`. The environment tracks
  `defaultRoute4Accessed` (set by any lookup through the route) rather
  than making the operation `unsupported`; mutant W9-M9.
- **M5 — a `to: wg0` inject leaves from `10.255.254.1`. Adopted** (sections
  2.5, 3.1, 3.4, 4.2, 4.3, 12). Verified: the local route's `prefsrc` is
  `ifa_local` (`fib_frontend.c:1095`) and `RTN_LOCAL` output takes it
  (`route.c:2835-2836`). `wg0` learns `10.255.254.1:51998`, `endpoint_eq`
  resets the cache (`socket.c:294`), the reply goes to the wildcard sender
  from `10.255.254.1`. `Env.senderSource` becomes destination-dependent and
  `Env.isSender` models the wildcard bind; `to: wg0` is `unsupported` in
  the foreign-creator mode (D's address, unroutable from C). The same for
  `fd00:ffff::1`.
- **M6 — W9-M1 mis-stated. Adopted** (sections 2.5, 7). Verified: a
  `to: wg0` inject stops at `Env.lean:217` today (`unsupported`, not a
  wrong source). The rule is wrong exactly when the destination differs
  from its `prefsrc` — the `127.0.0.2:51998` endpoint — where today's
  mirror silently drops a datagram Linux delivers to the wildcard sender:
  the latent fail-open. W9-M1 is re-based on that trace; W9-M2 is the
  evidence for the `inet_confirm_addr` arm.
- **M7 — the `!peer` arm's hidden-input footprint. Adopted** (sections
  1, 2.6, 4.2, 7, 8, 10). Verified: `icmp.c:268` (`get_random_u32_below(3)`),
  `:328` (`inet_getpeer_v4`, `inetpeer.c:232` `GFP_ATOMIC`), `:245` and
  `:310-330` (`jiffies`, `xrlim`), `sysctl_icmp_ratelimit = HZ` (`:1545`),
  plus the ICMP's ident and the NET_RX section over `lo`. W9.5 stays
  `unsupported` until W5-W6's ICMP rules; the one-level model becomes
  W9-R; the second level stays profound.
- **M8 — `tx_dropped` and `dev_activate`. Adopted** (sections 1, 2.2, 3.3,
  3.4, 6, 7). Verified: `noop_enqueue` (`sch_generic.c:642-647`) calls
  `dev_core_stats_tx_dropped_inc`; `dev_activate` returns early without
  carrier (`:1262-1264`). Stated as moot for re-activation: a later `wg_up`
  fails at `ndo_open` (`-ENONET`) before `__dev_open` reaches
  `dev_activate` (`dev.c:1551-1559`); `qdiscNoop` is never cleared; W8b
  models `txDropped += 1` per `sendto` (mutant W8-M8).
- **M9 — kind 306 and `_THIS_IP_`. Adopted** (sections 4.1, 4.4, 5, 10).
  Verified that 305 is A's allocation outcome (A's patch). An inline's
  `_RET_IP_` is the enclosing function's return address; `_THIS_IP_`
  resolves through the DWARF inline chain; W9-0 confirms the frames.
- **M10 — the dispatch budget reaches the cap. Adopted** (summary,
  sections 3.2, 9, 11.11). Verified: `KCOV_DISPATCH_MAX 16` in the patch;
  12 symbols today (`linux.py:39-44`), +2 (W5-W6) +2 (W8) = 16. Decision
  11.11 proposes folding a raise to 32 into W9-K.
- **M11 — cross-stream ownership and sequencing. Adopted** (section 10):
  the shared surfaces, their owners, the interface commit after D3+L+A+E.

**Minor.**
- **m1 — `scope` not cleared. Adopted** (section 3.3): `socket.c:311`
  zeroes the `src6` union only; `sin6_scope_id` lives in `addr6`.
- **m2 — `IFF_RUNNING` deterministic after M2. Adopted** (section 6):
  `operUp := carrier` at the linkwatch section, consumed in the operation.
- **m3 — keepalives through the crypt workers. Adopted** (section 2.2).
- **m4 — citation drift. Adopted**: the `check.py` kind table is cited by
  name (its line numbers differ between bases: on `task/d3-int` `:194-203`
  is the kind table, on the audit's base the exclusion validator);
  `wg_socket_clear_peer_endpoint_src`'s body is cited as `socket.c:310-312`.
- **m5 — the teardown takes longer than a few milliseconds. Adopted**
  (sections 2.1, 3.2, 9, 11.12): `NETNS_WAIT_US` 500 ms, measured by W8-0.
- **m6 — more comparison records than expected from the refcount inlines.
  Adopted** (sections 3.3, 10): W8-0 enumerates them; one exclusion label
  per comparison line found.
- **m7 — the listeners must be in C. Adopted** (sections 3.1, 3.4, 11.2):
  v1's Q8 was not a choice.
- **m8 — kind-305 allocations inside the section. Adopted** (sections 3.2,
  5): declared cut consumers of the `.netnsCleanup` cut point under A's
  rule.

**Answers to v1's open questions**, as the coordinator decided [AGENT]:
J2 approved with kind 306 and `_THIS_IP_`, subject to the user's approval of
the kernel change (11.3); 11.4 approved only with C1's measures; 11.5
approved; 11.6 the formula fixed, the observable dropped from W8a and left
to the user for W8b; 11.7 approved with M3 and M4; Q8 forced; Q9 `unsupported`
until W5-W6; Q10 documented, not built.

**Probe checklists** gained: two consecutive armed runs with `opened = 0`;
the learned endpoint and the reply's source for all three inject
destinations; `tx_dropped` in W8b; the default route after `wg_deladdr`;
the resolved frames of the inline reset sites.

## 14. Results [AGENT 2026-10-11]

Branch `task/w89` on the dispatch-order base (`task/dispatch-order`
dbe9e0e: main + housekeeping + the interface commit + the dispatch
identity). W9's core is built; W8 is not started (section 14.4).

### 14.1 What was built

- **W9-K** (commit 18bbdbf, record-only): `kernel/patches/gen-choice-stream.py`
  adds `kcov_dst_cache_ts(ts, ip)` in kcov.c, gated by
  `KCOV_DISPATCH_ARM_RECORDS` like the arm record, called with the value
  stored from `dst_cache_reset` (include/net/dst_cache.h, the inline; the
  prototype lives there under `CONFIG_KCOV`, an empty inline otherwise) and
  from `dst_cache_per_cpu_get`'s fail label (net/core/dst_cache.c), both at
  `_THIS_IP_`. Both patches regenerated; `scripts/build-kernel` CHOICE_SHA
  `8b34860c…`, ACTL_SHA `114c2969…`. Not built here: the coordinator
  builds both kernels and records the identities (the identity files'
  lines are the dispatch-order builds' until then). Decision 11.11 (the
  dispatch cap) is moot: the cap is already 32 since the D3+A integration.
- **W9-G** (50ed61c): `wg_deladdr`/`wg_delroute` (opcodes 23/24,
  `{op, family}`; the ACK is the result: EADDRNOTAVAIL 99, ESRCH 3);
  `wg_inject`'s optional `to` (loopback, wg0, loopback-alias; the code in
  the wire's value field); the guest's message builders beside
  `route_into_wg0`'s; L's EEXIST-on-a-later-up rule refined (not after a
  `wg_deladdr 4`). `evaluator/check.py`: kind 306 is class `jiffies`.
- **W9-M** (8083c7c): section 4.2 as designed, with these placements:
  the routing model is `World.route4/6` in `Leanux/Kernel/Defs.lean`
  (not `Env`: `Leanux/WG` cannot import `Env`, and `send4` needs it), with
  `routeLookup` noting the IPv4 default route's use; `send4`/`send6` take
  the endpoint and an optional cache peer (`&peer->endpoint` for
  `wg_socket_send_skb_to_peer`, a stack copy for the reply path); the
  transmit keeps the IP-ident cut and the nested NET_RX section
  (`loopbackSend`), E's reply path its lax cut; a route into wg0 stays
  `unsupported` (W9-R). Sites 150/151 (kind `jiffies`): on the W9 build
  (identity `313c2cc9…`) the records resolve, as every record does, by
  their address minus one (`evaluator/coverage.py`): the reset's four
  callers (`dst_cache_init`, `wg_socket_set_peer_endpoint:294`,
  `send4:59`, `dst_cache_reset_now:177`) share the inline's frame
  `include/net/dst_cache.h:90` and the refresh is `net/core/dst_cache.c:63`
  (the patched files' lines; section 4.4's 79/62 are the pristine ones).
  The first run on that build failed every WireGuard chunk at the first
  `wg_set` ("no record left for dst_cache_reset_ts") with the sites at the
  pristine lines: the records were unknown sites.
  Captures made before the record (`evaluator/test_model_replay.py`)
  carry `"dst_cache_records": false`, under which the mirror keeps the
  pre-W9 rule (the cache always misses, no record consumed); a live run
  never sets it.
- **W-H** (this commit): `scripts/wg-w89-corpus.py`, eight `w9_*` traces
  (section 14.2); mutants W9-M1, M2, M3, M5, M8, M9, M10 on the `w9_`
  subset (`scripts/wg-mutants.py`). W9-M4 needs a roaming inject and is
  not written; W9-M6 waits for W9-R; W9-M7 needs a deladdr-while-cached
  trace.

### 14.2 The corpus

| Trace | What it reaches |
|---|---|
| `w9_endpoint_alias` | the initiation to `127.0.0.2:51998`: the `127/8` local route, the sender's wildcard bind, source `127.0.0.1` (W9-M1) |
| `w9_two_sends` | the initiation (a miss after `dst_cache_init`) and the retransmit: a hit iff the recorded refresh jiffy is after the reset's (W9-M3) |
| `w9_delroute_untouched` | `wg_delroute 4` before any lookup through the route: no generation bump (W9-M9) |
| `w9_unroutable` | `-ENETUNREACH` at `send4`: no datagram, `tx_bytes` unchanged (W9-M5); the peer starts without an endpoint so the running-device `wg_set` queues the keepalive's initiation |
| `w9_deladdr_then_send` | `wg_deladdr 4` takes the default route (`wg_delroute 4` → ESRCH), the inner `sendto` fails (W9-M8) |
| `w9_deladdr6_then_send` | the IPv6 removal keeps the default route (the second `wg_delroute 6` → ESRCH) |
| `w9_inject_to_alias` | a response from the alias: `src4 = 127.0.0.2`, rejected by `inet_confirm_addr` at the keepalive's send (W9-M2) |
| `w9_inject_to_wg0_addr` | a response to wg0's own address: the endpoint `10.255.254.1:51998`, the cache reset, the reply from that address (W9-M10) |
| `w9_session_two_sends` | after the session, two data sends: the second always hits the cache (the keepalive after the endpoint's reset refreshes in the same or the next jiffy) (W9-M3) |
| `w9_session_delroute_untouched` | IPv6 inner packets, so the IPv4 default route is never looked up before `wg_delroute 4`; the outer send after the delete hits (W9-M9) |

### 14.3 Validation

On the dispatch-order oracle (`bb3e577d`), which writes no kind-306 record:
- `lake build leanux-model`: OK (82 jobs); unit and replay tests: 111 OK;
  `leanux-model --hidden-sites` lists 150/151 as kind `jiffies`.
- `evaluator.check --suite handwritten`: pass (no WireGuard trace).
- Every WireGuard trace with a peer fails at its first `wg_set` with
  "no record left for dst_cache_reset_ts" (`d1_basic` and the eight
  `w9_*` traces, each accepted by the domain filter): the expected,
  uniform failure until the W9-K kernel exists. **The suite-level check
  of W9-M, the eight traces and the seven mutants is the coordinator's,
  on the rebuilt oracle.**

### 14.3b On the W9 build (identity `313c2cc9…`) [AGENT 2026-10-12]

After the sites moved to the resolved lines and the `dst_cache_init`
record took its place in `wg_peer_create`'s order (before the handshake
init, peer.c:36 vs :55), the send decisions became repeatable (several
datagrams per operation) and the miss's first witness the confirm-addr
test (line 52/132, `security_sk_classify_flow`, has no instrumentation
point without `SECURITY`):
- `--suite handwritten,wireguard`: 166/190 agreement; `s2_index_collision`
  (repeatable) and `w9_inject_to_alias` (the witness order) then pass alone,
  as do `w9_endpoint_alias`, `w9_two_sends`, `w9_unroutable`,
  `w9_deladdr_then_send`, `w9_inject_to_wg0_addr`, `w9_delroute_untouched`
  (8/8 single-trace runs).
- **One open finding, a scheduling race.** `e_cookie_bad_mac1_aad`
  operation 5 (a `wg_set` whose keepalive sends an initiation) stopped
  with "expected the NET_RX section, the record is site 151": Linux's
  cache missed where the mirror's hit. The records: resets at op 0
  (jiffies 4296157671, `dst_cache_init` and the endpoint set), the first
  send's refresh at op 1 (4296157706, after the resets: the slot valid by
  `time_after`), no reset after, a refresh at op 5. So the dst made at op
  1 failed `ipv4_dst_check`: `rt_genid` moved after it. The guest adds
  wg0's addresses and routes (`route_into_wg0`, each add a
  `rt_cache_flush`) after the `wg_up` ioctl returns and before the
  operation's wait; the handshake worker queued inside the ioctl runs
  either at the ioctl's return to user space (then its dst predates the
  routes and expires) or during the wait (then it survives: the eight
  single-trace runs above, where `w9_two_sends`'s retransmit hit). The
  mirror bumps the generation inside `wg_up`, before the send: the second
  order. Not recorded by anything, so not modelable fail-closed as is.
  Proposed fix (the coordinator's call, a guest change): for a successful
  flag-changing `wg_up`, the guest waits `QUEUE_WAIT_US` **before**
  `route_into_wg0` (its existing wait, moved; no added time), making the
  first order deterministic; the mirror then applies the table changes
  after the send workers and the idle timers of that operation
  (`Env.wgUp` queues them, the post-operation hook in `Syscalls.syscall`
  applies them). A send to an off-loopback endpoint at `wg_up` then gets
  `-ENETUNREACH` in both, as the first order gives.

  **Decision [AGENT, coordinator, 2026-10-12]:** the fixture order is made
  deterministic as proposed: the guest's existing post-up wait moves
  before `route_into_wg0` (no added time), and the mirror applies the
  table changes after that operation's send workers and idle timers
  (`World.routesPending`, `Env.routeIntoWg0`). Reason: a scheduling race
  the records cannot show (the handshake worker queued inside the ioctl
  ran at the ioctl's return in one run and during the wait in eight
  others), resolved as a fixture choice rather than a placement the check
  reruns. Recorded in `docs/decisions.md`.

### 14.3c Final validation on the W9 build, with the fixture order [AGENT 2026-10-12]

- `evaluator.check --suite handwritten,wireguard --out .artifacts/check/w9-suites-3`:
  **pass, 190/190**, 8983 operand pairs, no chunk retries, the `e_*`
  traces included; trace time after `wg_up` max 3.747 s of 4.5 s
  (`d3_retransmit_gives_up`, margin 16.7%): the moved wait adds no time.
- Mutants (`scripts/wg-mutants.py`, the `w9_` subset, no other outcome):
  W9-M1 rejected (2 semantic), M2 (8 hidden), M5 (1 semantic), M8 (1
  semantic), M10 (1 semantic); M3 and M9 survived the first run (the
  initiation's dst is expired by the up's route adds, so no send hit)
  and are rejected (10 hidden each) on the two session traces above.
  **7/7 rejected.**
- Unit and replay tests: 111 OK. `lake build leanux-model` OK.
- The ten `w9_*` traces pass alone; `s2_index_collision` and
  `w9_inject_to_alias` pass after the repeatable and witness fixes.

### 14.3d `wg_set_mtu` and the tables (the W integration) [AGENT 2026-10-12]

On the integration branch the claim point's `w4_set_mtu_0` failed at
operation 5 (a `wg_advance` whose persistent-keepalive send found Linux
refreshing the cache, site 151, where the mirror predicted a hit), in the
replay of the comparison child's records (chunk-006ba of the claim run,
`model-cmp`). Those records: two resets at operation 0 (jiffies 4294924046,
the peer's creation and its endpoint), the up's refresh at operation 1
(4294924087), at operation 3 the reset of the endpoint update (4294924251)
and the keepalive's refresh one jiffy later (4294924252), nothing at
operation 4 (`wg_set_mtu 0`), and operation 5's refresh (4294925757). With
the refresh after the reset and the generation unchanged, the mirror's
rule (14.1) hits at operation 5. Linux missed because `dev_set_mtu_ext`
calls the `NETDEV_CHANGEMTU` notifiers for a changed MTU (dev.c:9090-9091
returns 0 before them for the same one), and `fib_netdev_event` runs
`fib_sync_mtu` and `rt_cache_flush` on **every** change
(fib_frontend.c:1519-1522), so every cached IPv4 dst fails `ipv4_dst_check`
afterwards; below `IPV4_MIN_MTU` (68) `inetdev_event` destroys the
`in_device` (devinet.c:1637-1643), taking the IPv4 address and, with it,
the routes via wg0; below `IPV6_MIN_MTU` (1280) `addrconf_ifdown` removes
the IPv6 addresses and routes (addrconf.c:3691-3695) and moves the sernum.
W4's `setMtu` modeled the device's own state (`inet4Dev`, `inet6Dev`) but
not W9's tables, which did not exist on its base. The rule, in
`Env.setMtu`: a successful `wg_set_mtu` to a different MTU bumps the IPv4
generation; below 68 it empties `addrs4` and drops the IPv4 default route;
below 1280 it empties `addrs6`, drops the IPv6 default route and bumps the
IPv6 generation; the same MTU leaves the tables alone; a later `wg_up`
re-adds them (`routeIntoWg0`). The records distinguish the two outcomes
(the mirror decides the hit from the recorded jiffies and the generation it
models), so no capture was needed: the mirror at c868631 reproduces the
failure on the comparison child's records, the fixed one decides
`send4.cache_miss` at operation 5 and consumes the refresh. The coverage
child of the same chunk agreed by timing: there the reset and the refresh
of operation 3 fell in the same jiffy (4294922240), and the same-jiffy rule
(14.3b) misses at operation 5 whatever the MTU did; only a send after the
MTU change that would otherwise hit shows the gap.

### 14.4 Not done

- **W8b** (the device up at the exit: `linkwatch_event` armed, the
  deactivated queue's `tx_dropped`, the timers' and keepalive sends'
  `-ENONET`, the two-table routing of section 3.4), the generator's `netns`
  class, and listing `wg_socket_init` with the refcount operand exclusions
  (section 3.3): see 14.5 for what W8a built.
- The generator classes (`routing`, `netns`); the control suite for the
  datagram routed into wg0; W9-R; the stretch items W9-S1/S2.

### 14.5 W8a: the exit with the device down [AGENT 2026-10-12]

Built on the W9 oracle (`313c2cc9…`), no kernel change.

| Run | Result |
|---|---|
| unit and replay tests | 111 OK |
| `w8_down_exit_up` alone | pass, 54 operand pairs: the `cleanup_net` section in `wg_netns_close`, `wg_up` `-ENONET`, `wg_observe` null with `-EBADF` |
| the four `w8_*` traces | pass, 4/4, 223 operand pairs |
| `--suite handwritten,wireguard` | see the commit |

What was built (sections 3.1-3.4): the fixture mode `"net_fixture":
"foreign-creator"` (wire `net` 3: D and C, wg0 created from C with
`IFLA_NET_NS_FD` naming D, the listeners, the injector at 8 and the pin at
9 in C, the sender and the generic-netlink socket in D, the fixture row
`reserved` 0-9); `wg_netns_close` (opcode 22); per-trace arming (the `T`
line's seventh field, a bit per dispatch entry; `cleanup_net` and
`linkwatch_event` join `DISPATCH_SYMBOLS` at 12-13, `cleanup_net` armed by
foreign-creator traces only); the namespace pins; the mirror's
`wgNetnsPreExit`, `socketInit`'s live `-ENONET`, `setDevice`'s live `-EPERM`
(`.setDevNoNet`), the closed listeners' `-EBADF` and null datagrams; the
FS mirror closes fixture sockets (`sock_close` a cut) and the pin (its
dentry's eviction queues `cleanup_net`); `wg_netns_pre_exit` listed in
`kcov.json`.

Deviations [AGENT]:
- **The pins live in a holder process**, not the batch: a pin held by the
  batch is inherited by every later child, where it shifts the fixture and
  widens the descriptor table (an operand of every close). The batch forks
  the holder once; a trace process sends its pid and waits for the ack.
  The handshake runs over AF_UNIX socket pairs, not pipes: a pipe's buffers
  are charged to the user's `pipe_bufs`, an operand of every pipe trace's
  `alloc_pipe_info` (`too_many_pipe_buffers_soft`), so two batch pipes
  shifted every pipe trace's operands by 32 (the W batch's claim point: 581
  `too_many_pipe_buffers_soft` operand mismatches).
- **The close order is injector, listeners, then the pin**, the reverse of
  3.2's: a UDP socket's `put_net` is RCU-deferred, and a `cleanup_net`
  queued from an RCU callback would write no queue record (kind 307 is
  recorded in the task's context only), so the pin's synchronous put must
  be the last. The settle in between is a spin on `CLOCK_MONOTONIC_COARSE`
  through the vDSO, not a sleep: a `nanosleep` inside the window records
  its clock reads, and the coarse clock's vDSO path needs no clocksource (a
  TSC spin at `/proc/cpuinfo`'s rate failed a whole batch on a boot whose
  TSC calibration had failed, the claim point's `cpu_mhz`).
- **The parked descriptors sit at 40-43**, not above the table: a `dup2`
  above `NR_OPEN_DEFAULT` would grow the trace process's table to 256,
  visible as `file_close_fd_locked`'s operand.
- **`linkwatch_event` is not armed in W8a**: its delay is
  `linkwatch_nextevent - jiffies`, a global the previous child's run moves
  (audit M2's caveat), so its section could land after the wait; for a down
  device only `operstate` changes, which nothing observes. W8b decides.
- **Inside the section** the records are the pre-exit's, one `dst_cache_reset_ts`
  from `sit0`'s unregister (`ipip6_tunnel_uninit`, a cut consumer) and
  `cleanup_net`'s own `cond_resched` (an ambient site, 152), and, under
  load only, `default_device_exit_batch`'s `cond_resched`
  (net/core/dev.c:12174, the device layer's pernet `exit_batch` run by
  `ops_exit_list` at net_namespace.c:178; an ambient site, 427, declared
  2026-10-14 after two traces met it in a loaded claim-point run and passed
  alone). The allocations are below the cut (A).
- **The check accepts repeated decisions inside `wg_netns_close`**: four
  close system calls in one operation.
- **`wg_socket_init` stays unlisted** (3.3's operand exclusions not built):
  the `-ENONET` arm is data, witnessed by `wg_open.socket_init_error`.
- The one-off mutant for the new section rule, W8-M1 (`wg_netns_pre_exit`
  keeps `creating_net`), is run once and reported in the commit, then
  dropped (AGENTS.md, gates and speedbumps).

### 14.6 The generator classes, and the re-entry probe [AGENT 2026-10-12]

- `routing_trace` (`evaluator/generate.py`, `ROUTING_SHARE` 0.05 of the
  WireGuard suite): the alias endpoint, two sends through the cache with
  the retransmit advance, the default route deleted before any lookup, the
  unroutable endpoint off loopback, the address then route deletion with a
  failing transmission, the response injected to the alias or to wg0's
  address, a session with two data sends (optionally IPv6 with a
  `wg_delroute 4` between them), and the IPv6 deletions; each from a
  steered initiation at `wg_up`. 200/200 pass the domain filter.
- `netns_trace` (`NETNS_SHARE` 0.03): the foreign-creator fixture with
  wg0 configured and down, `wg_netns_close`, then an up (`-ENONET`), a port
  (`-EPERM`), a peer, a delete, or all four. 200/200 pass the domain filter.
- **W9-R is not built.** The probe `corpus/w9-controls/w9_reentry_no_peer`
  (the endpoint 192.0.2.1, a transmission after the up's routes exist) shows
  the re-entry's footprint in the send worker's section on the W9 oracle:
  after the dst cache's refresh (kind 306), a kind-1 draw at the ICMP
  credit, two kind-110 identifiers (the outer datagram's, the ICMP's) and
  two kind-101 records at two chains, no NET_RX section, then the arm
  record; `tx_errors` 1 at the observation. The mirror stops `unsupported`
  at `socket.c:80`, now a domain control (`scripts/wg-w9-controls.py`):
  the stop is checked, never a silent delivery. A transmission at `wg_up`
  does not reach the re-entry: the up's routes follow the operation's wait
  (14.3b), so that send fails `-ENETUNREACH` on both sides.
