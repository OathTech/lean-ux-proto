# W4 + W7: transmit shapes and bulk queues — design, 2026-10-06

Status: **proposed** [AGENT], for the user's decisions in section 13. The
census ([2026-10-06-wireguard-census.md](2026-10-06-wireguard-census.md))
lists W4 (transmit shapes, M) and W7 (bulk and multi-item queues, L) as
in-reach workstreams toward the user's goal of 2026-10-06, 100% of reasonable
single-CPU WireGuard. P5 (concurrency recheck arms) and P9 (NAPI budget
exhaustion) stay excluded; section 10 re-derives P9 under W7's multi-item
polls, since the census argued it from "at most one packet per poll".

Line numbers are in the unpatched `.deps/linux` (6.12.110) unless a file is
named as patched. The kernel is `kernel/config-x86_64-net-choice`: one CPU,
`CONFIG_PREEMPT_NONE`, `HZ=250`, `CONFIG_IO_URING=y` (`:201`), `NR_CPUS=1`
(`:290`). Mirror references are to `task/census` (= `main` + the census) and
`task/d3-int`/`task/e-b` where named. The base for implementation is the
integrated D3+L+A+E tip (section 12).

Two premises of the task brief changed under verification and are stated
up front:
- **The `ip_idents_reserve` record is not the ident.** Site `.ipIdentReserve`
  (`Leanux/Kernel/Defs.lean:322`, `route.c:482`, 4 bytes) records
  `delta = get_random_u32_below(now - old)` (`route.c:481-482`); the ident is
  `atomic_add_return(segs + delta, p_id) - segs` (`:488`) over a per-bucket
  counter seeded with `get_random_bytes` at boot (`route.c:3720`). So an
  unconnected `IP_PMTUDISC_DONT` sender's fragment ident cannot be
  reconstructed from existing records. Section 3.6 gives the two routes: a
  **connected** sender socket (its ident seed is a capturable draw) or a
  kernel capture of the ident (option K1).
- **`Env.runWorker`'s commuting assumption does not survive multi-item
  queues** (`Leanux/Env.lean:200-217`: "each rest is a worker's final empty
  ring or queue poll"). With several items a tx worker that yields back into
  an encrypt worker higher on the mirror's stack resumes to a non-empty
  queue. Section 5.4 makes this fail-closed first and gives the step-worker
  restructuring as the full fix.

## 1. Target

**W4 — transmit shapes.** Every `wg_xmit` arm the IP stack can reach on one
CPU, with its bytes checked at the fixture's listener:
- UDP GSO: one `sendmsg` with `UDP_SEGMENT` arrives at `wg_xmit` as one GSO
  skb; `skb_gso_segment` splits it; the segments are **one staged list** and
  **one ring item** (device.c:176-204, 215, 218).
- The staged-queue trim, `> MAX_STAGED_PACKETS` (device.c:211-214), reachable
  with two or three GSO transmissions and no session.
- The padding arms of `calculate_skb_padding` (send.c:141-160): `!mtu`
  (`:145`), `len > mtu` (`:154-155`), the `min` clamp (`:157-158`), via a route
  MTU below the device MTU, `SIOCSIFMTU` and `IFLA_MTU` at creation.
- `Device.mtu` as mirror state in place of `WG.DEVICE_MTU`
  (`Leanux/WG/Send.lean:48`), read by `wg_xmit` (device.c:173), the keepalive
  (send.c:232) and `wg_open`'s IPv6 test (device.c:34, 47).
- Multicast and link-local destinations, whose source, TTL and hop limit the
  fixture determines (today `Env.xmitBytesUnknown`, `Env.lean:100`, and
  `checksumHelp`'s `unsupported`, `:158`).
- Transmit fragmentation: one `sendto` with `IP_PMTUDISC_DONT` above the MTU
  gives **two `wg_xmit` calls** in one system call.

**W7 — bulk and multi-item queues.** The crypt rings and per-peer
`prev_queue`s holding several items at once, produced by io_uring batches
with no drain point between sends (the E measurement,
`task/e-dos:docs/2026-10-05-e-probe-results.md`): the workers' multi-item
loops, the `peeked` state of `prev_queue`, a `DEAD` break mid-list, several
peers' polls in one `net_rx_action`, the `cond_resched` placements, and the
far end: `-ENOSPC` and `-EPIPE` on full queues (1024 items).

## 2. Kernel mechanisms, verified

### 2.1 UDP GSO through `wg_xmit`

- **Sender side.** `UDP_SEGMENT` as a cmsg (`udp.c:1081-1085`) or socket
  option (`:2810-2814`). `udp_send_skb` (`udp.c:984-1014`): `hlen +
  min(datalen, gso_size) > cork->fragsize` → `-EMSGSIZE` (`:988-991`);
  `datalen > gso_size * UDP_MAX_SEGMENTS` → `-EINVAL` (`:992-995`,
  `UDP_MAX_SEGMENTS = 128`, `include/linux/udp.h:111`); `datalen > gso_size`
  sets `gso_size`, `SKB_GSO_UDP_L4`, `gso_segs = DIV_ROUND_UP(datalen,
  gso_size)` and goes to `csum_partial` (`:1005-1012`) — the super-skb is
  `CHECKSUM_PARTIAL` with the pseudo-header sum (`udp4_hwcsum`, `:905-912`).
  IPv6 is symmetric (`net/ipv6/udp.c:1294-1319`). `cork->fragsize` is the
  route MTU (1420 here; `ip_output.c:1307-1308`), so `gso_size ≤ 1392` on
  IPv4 and `≤ 1372` on IPv6.
- **Stack to device.** `__ip_finish_output` → `ip_finish_output_gso` when
  `skb_is_gso` (`ip_output.c:308-309`); each segment fits the MTU, so no
  fragmentation. `__dev_queue_xmit`: wg0 is `IFF_NO_QUEUE` (device.c:291), so
  `q->enqueue` is NULL and the skb goes through `validate_xmit_skb`
  (`dev.c:4510-4541`). `netif_skb_features` keeps the GSO features
  (`gso_features_check`, `dev.c:3598-3649`: `gso_segs ≤ gso_max_segs`,
  `len < gso_max_size`), wg0 advertises `NETIF_F_GSO_SOFTWARE` (device.c:
  277-279; `netdev_features.h:213-214` includes `NETIF_F_GSO_UDP_L4`), so
  `netif_needs_gso` is false (`dev.c:3780`) and **the GSO skb reaches
  `wg_xmit` intact**. The `CHECKSUM_PARTIAL` help at `dev.c:3799-3808` is not
  taken (`NETIF_F_HW_CSUM`).
- **Inside `wg_xmit`.** `skb_is_gso` → `skb_gso_segment(skb, 0)`
  (device.c:179) → `__skb_gso_segment(skb, 0, true)` (`gso.c:88-131`;
  `skb_needs_check` false for `CHECKSUM_PARTIAL`, `:66-70`) →
  `inet_gso_segment` (`af_inet.c:1369-1470`) → `udp4_ufo_fragment` →
  `__udp_gso_segment` for `SKB_GSO_UDP_L4` (`udp_offload.c:506-507`,
  `:326-482`). With **features = 0**:
  - `skb_segment` (`skbuff.c`): `sg = 0`, `csum = 0` (`:4763-4764`), so every
    segment is linear (`hsize = len`, `:4881-4882`) and
    `ip_summed = CHECKSUM_NONE` with the payload sum in `SKB_GSO_CB->csum`
    (`:4913-4923`, `:5007-5020`).
  - `__udp_gso_segment` sets each segment's `uh->len` and adjusts the
    pseudo-header sum (`:421-422`, `:447-453`); since the segments are not
    `CHECKSUM_PARTIAL`, `uh->check = gso_make_checksum(seg, ~check) ?:
    CSUM_MANGLED_0` (`:439-441`, `:457-458`) — **a complete UDP checksum per
    segment, in software**. The last segment may be shorter (`:447-450`).
  - `inet_gso_segment` writes the IPv4 ids: `iph->id = htons(id++)` per
    segment from the super-skb's id (`af_inet.c:1451-1454`), `tot_len` and
    the header checksum (`:1456-1457`). The super-skb's id comes from
    `__ip_make_skb` → `ip_select_ident` (`ip_output.c:1465`, `ip.h:591-595`
    → `:559-589`): for the fixture's **unconnected, `IP_PMTUDISC_DO`**
    sender, `DF && !ignore_df` → **`id = 0`** (`ip.h:583-584`; `ignore_df`
    from `ip_sk_ignore_df`, `:462-467`). So the segments carry ids 0, 1, …,
    n−1: deterministic, no hidden input. IPv6 segments have no id.
  - Consequence for the mirror: a GSO segment's `encrypt_packet` takes the
    **false** arm of `skb->ip_summed == CHECKSUM_PARTIAL` (send.c:187), where
    every D2 packet took the true arm. Both arms of `.encChecksumPartial`
    (`Data.lean:81`) become reachable.
- `IS_ERR(segs)` (device.c:181-183: `err_peer`, ICMP, `tx_errors`) needs an
  allocation failure inside `skb_segment` — stream A's domain (section 9).
- The walk (device.c:189-204): `skb_share_check` per segment (never shared
  here), `skb_dst_drop`, `PACKET_CB(skb)->mtu = mtu` with the **one** `mtu`
  computed at `:173` for the whole list.

### 2.2 The staged trim without a session

`wg_xmit` trims **before** adding (device.c:207-214, the comment says why:
"so we don't remove GSO segments that are in excess"): `while (qlen > 128)
{ dequeue oldest; tx_dropped++ }`, then `skb_queue_splice_tail`. Without a
keypair, `wg_packet_send_staged_packets` puts the packets back at the head
(send.c:393-408) and queues an initiation (`:413`, rate-limited by
`REKEY_TIMEOUT`, a `.birthdateExpired` read per call). So:
- xmit 1, 128 segments: trim loop `128 > 128` false; staged = 128;
- xmit 2, 128 segments: `128 > 128` false; staged = 256;
- xmit 3, any size n: 128 iterations drop the oldest 128 (`tx_dropped += 128`),
  then staged = 128 + n.

Two GSO transmissions reach 256 staged; the third takes the loop. When the
offline response completes the session, the flush is **one ring item of
128 + n packets** through the encrypt and tx workers (W7's multi-packet item
on the send side). With a small `gso_size` (8 bytes) the 129 ciphertexts are
48 bytes each. The D2 reason for excluding the trim ("129 transmissions × the
100 ms wait", D2 §8) no longer applies.

### 2.3 Padding arms: route MTU, `SIOCSIFMTU`, `IFLA_MTU`

`PACKET_CB(skb)->mtu = skb_valid_dst(skb) ? dst_mtu(skb_dst(skb)) : dev->mtu`
(device.c:173). `dst_mtu` → `ipv4_mtu` → `ip_dst_mtu_maybe_forward(dst,
false)` (`route.c:1366-1369`, `ip.h:469-495`): `rt_pmtu` if set and
unexpired (`:481-487`), else **`RTAX_MTU` of the route** (`:490-492`), else
`dev->mtu` (`:494`).

- **Route MTU below the device MTU** (the `len > mtu` and clamp arms).
  A route `… dev wg0 mtu 1300` gives `dst_mtu = 1300`. The sender must still
  build a 1420-byte packet: with **`IP_PMTUDISC_PROBE`**, `ip_sk_use_pmtu`
  is false (`ip.h:457-460`), so `cork->fragsize = dev->mtu = 1420`
  (`ip_output.c:1307-1308`) and `ip_skb_dst_mtu = dev->mtu`
  (`ip.h:511-525`, the `:523` branch), so `__ip_finish_output` does not
  fragment (`:311`) and DF is set (`:1441-1442`). `wg_xmit` then sees
  `len = 1420 > mtu = 1300`: `last_unit = 1420 % 1300 = 120`,
  `padded_size = min(1300, 128) = 128`, padding 8; ciphertext 1420 + 8 + 32.
  IPv6 is symmetric (`ip6_output.c:1401-1405`, `ip6_route.h:269-281`,
  `IPV6_PMTUDISC_PROBE`). A route with `mtu lock` is not needed: `RTAX_MTU`
  is read regardless (`ip.h:490`); `lock` only guards against PMTU updates.
- **`SIOCSIFMTU`** → `dev_set_mtu_ext` → `dev_validate_mtu`
  (`dev.c:9085-9122`, `:9061-9075`) → `__dev_set_mtu` writes `dev->mtu`
  (`:9048-9058`; wg has no `ndo_change_mtu`) → `NETDEV_CHANGEMTU`. wg never
  sets `min_mtu` (device.c:274-307 sets only `mtu` and `max_mtu`;
  `alloc_netdev_mqs` sets none), so **`dev_validate_mtu` accepts 0** (`:9065`
  is `new_mtu < 0 || new_mtu < dev->min_mtu`). Consequences:
  - `< 1280`: `addrconf_notify` runs `addrconf_ifdown(dev, 1)`
    (`addrconf.c:3691-3695`): wg0's IPv6 is gone until the MTU is raised
    again (`:3704-3711`, `ipv6_add_dev`).
  - `< 68`: `inetdev_event` runs `inetdev_destroy` (`devinet.c:1637-1643`):
    wg0's IPv4 address and routes are gone.
  - With MTU 0 and a keepalive (`PACKET_CB(skb)->mtu = skb->dev->mtu`,
    send.c:232), `calculate_skb_padding` takes the **`!mtu` arm**
    (send.c:145-146, `.padNoMtu`, `Decision.lean:943`), and a `wg_down` /
    `wg_up` afterwards takes **both `if (dev_v4)` and `if (dev_v6)` false**
    in `wg_open` (device.c:39, 47). A probe must confirm `ip link set wg0 mtu
    0` is accepted on this kernel (section 12); the fixture's routes do not
    survive it, so this class ends the trace.
  - A normal lowering (say 1000, DO sender) changes `cork->fragsize`,
    `MAX_XMIT_PAYLOAD*`, the padding and `-EMSGSIZE` boundary.
- **`IFLA_MTU` at creation** (L's `wg_create`, `task/e-b:harness/guest.c:976-
  986`): `rtnl_create_link` validates and sets `dev->mtu` before
  `register_netdevice` (`rtnetlink.c:3517-3526`); `NETDEV_REGISTER` creates
  the `inet6_dev` only if `dev->mtu >= IPV6_MIN_MTU` (`addrconf.c:3683-3688`,
  and `ipv6_add_dev` refuses below, `:381-382`), while `inetdev_init` always
  runs (`devinet.c:1576-1580`). So a device created with MTU 1279 enters
  `wg_open` with `dev_v6 == NULL`: the false arm of `.openHasInet6`
  (`Device.lean:45`, constant true today).

### 2.4 Multicast and link-local transmit

- **wg0 has no link-local address.** `__dev_open` calls `ndo_open`
  (`dev.c:1552`) and `dev_open` raises `NETDEV_UP` only afterwards
  (`:1588-1593`); `wg_open` sets `addr_gen_mode = IN6_ADDR_GEN_MODE_NONE`
  (device.c:47-48) on the `inet6_dev` created at registration (default
  `EUI64`, `ipv6_devconf_dflt`, `addrconf.c:296`, copied at `:392`);
  `addrconf_dev_config` at `NETDEV_UP` (`:3489-3524`) only rewrites
  `EUI64 → RANDOM` (`:3518-3521`) and `addrconf_addr_gen` adds nothing for
  `NONE` (`:3482-3485`). **D2 §2's "wg0 gets a random link-local address" is
  wrong**; its exclusion of `fe80::/10` destinations stands for a different
  reason (no deterministic source). A probe (`ip -6 addr show wg0`) confirms
  this once (section 12).
- **Link-local destinations** become deterministic when the fixture adds
  `fe80::1/64` to wg0 (`route_into_wg0`): a datagram to `fe80::2` via wg0
  selects `fe80::1`. The peer's allowed IPs must cover it.
- **Multicast.** `ff02::1` via wg0 (scope id = wg0's ifindex or
  `IPV6_MULTICAST_IF`): hop limit `IPV6_DEFAULT_MCASTHOPS = 1`
  (`include/net/ipv6.h:53`, `:905`; `af_inet6.c:223`); IPv4 `224.0.0.1` with
  `mc_ttl = 1` (`af_inet.c:364`; `ip_output.c:1452-1453`). The source is
  wg0's global address (no link-local exists; with `fe80::1` added, source
  selection prefers it for a link-local-scope destination — the fixture
  decides which, and the bytes check it). The **loopback copy**:
  - IPv4: `ip_mc_output` clones to `dev_loopback_xmit` when `sk_mc_loop`
    (`ip_output.c:382-400`) — D3 already models this as a NET_RX section
    before `wg_xmit` (`task/d3-int:Leanux/Env.lean:90-93`,
    `xmitMulticastLoop`).
  - IPv6: `ip6_finish_output2` loops only when wg0 is a member
    (`ipv6_chk_mcast_addr`, `ip6_output.c:86-99`). Every `inet6_dev` joins
    `ff01::1` and `ff02::1` (`addrconf.c:466-471`), plus the solicited-node
    group of each address. So `ff02::1` loops, `ff02::1234` does not. D3's
    `unsupported` for IPv6 multicast (`Env.lean:93`) becomes an exact
    membership set over the fixture's addresses.
  - Nothing receives the copy (no socket on `SEND_PORT`), and multicast
    destinations draw no ICMP error. Setting `IP(V6)_MULTICAST_LOOP = 0` on
    the sender for a control class flips the `sk_mc_loop` arm.

### 2.5 Transmit fragmentation (`IP_PMTUDISC_DONT`)

`ip_sk_ignore_df` is true for `DONT` and `WANT` (`ip.h:462-467`), so
`maxnonfragsize = IP_MAX_MTU` (`ip_output.c:999`) and a 2000-byte payload is
accepted. `__ip_append_data` builds the datagram as a head skb plus
`frag_list` members (`__ip_make_skb`, `:1412-1429`); since
`length + fragheaderlen > mtu`, `csummode` stays `CHECKSUM_NONE` (`:1011-
1016`) and `udp_send_skb` computes the UDP checksum in software over the
whole datagram (`udp.c:1030-1031`; the `frag_list` branch of `udp4_hwcsum`,
`:913-930`). DF is clear (`:1440-1445`) and the ident is drawn
(`:1465` → `ip.h:585-587` → `__ip_select_ident`, section 3.6).
`__ip_finish_output`: `skb->len > mtu` → `ip_fragment` (`:311-312`) →
`ip_do_fragment` (`:589-590`), the `frag_list` fast path (`:816-847`):
`ip_fraglist_init` sets `MF` on the head (`:605-622`), each `output()` call
(`:870`) is `ip_finish_output2` → `dev_queue_xmit` → **`wg_xmit`**, and
`ip_fraglist_prepare` copies the head's IP header to the next fragment
(`memcpy`, `:636`: same id), sets offset/`MF` (`:641-644`) and marks it
`CHECKSUM_NONE` (`:632`). So one `sendto` is **two `wg_xmit` calls inside
the system call**, both `CHECKSUM_NONE` (the false arm of send.c:187 again),
the second without a UDP header. `wg_allowedips_lookup_dst` reads only the
destination; both fragments go to the peer.

IPv6 (`IPV6_PMTUDISC_DONT`): `ip6_fragment` (`ip6_output.c:873-`), the
`frag_list` path (`:932`), one `output()` per fragment (`:977`); the
Fragment header's id is `ipv6_select_ident` (`:923`) →
`__ipv6_select_ident` = `get_random_u32_above(0)` (`output_core.c:14-19`) =
`1 + get_random_u32_below(U32_MAX)` (`random.h:98-103`), a draw the generic
hook records (kind 110; section 3).

### 2.6 The queues (W7)

- **Rings.** `wg_packet_queue_init(…, MAX_QUEUED_PACKETS)` (device.c:348-
  356; `messages.h:53` = 1024) is a `ptr_ring` of 1024 slots
  (`ptr_ring.h:487-489`); `__ptr_ring_produce` returns `-ENOSPC` when the
  producer slot is occupied (`:104-107`), i.e. when 1024 items are in the
  ring; `wg_queue_enqueue_per_device_and_peer` maps that to **`-EPIPE`**
  (`queueing.h:174-175`). Each ring is **per device**.
- **`prev_queue`** (per peer). `wg_prev_queue_enqueue` fails when `count` is
  already `MAX_QUEUED_PACKETS` (`queueing.c:72-78`, `atomic_add_unless`);
  mapped to **`-ENOSPC`** (`queueing.h:167-168`), **tested before** the ring
  produce. `wg_prev_queue_dequeue` (`queueing.c:80-106`): the stub arm
  (`:84-90`), the "more remain" arm (`:91-95`, `count--`), the concurrency
  arm `tail != head → NULL` (`:96-97`, P5), the re-stub of the last item
  (`:98-104`) and the final `NULL` (`:105`, P5). `wg_prev_queue_peek`
  returns the `peeked` slot if set (`queueing.h:143-149`; `.prevQueuePeeked`,
  `Decision.lean:986`, constant false today), and `drop_peeked` clears it
  (`:152-155`). `count` is decremented at dequeue, so a peeked item is not
  counted.
- **Accounting.** An item is in the ring iff `UNCRYPTED` and not yet consumed
  by the crypt worker; it stays in the `prev_queue` until the tx worker or
  the poll peeks it. Hence, **for one peer, `prev_queue.count ≥ ring
  occupancy`** at all times, and the 1025th item of a session hits
  `-ENOSPC` first (`queueing.h:167`), never `-EPIPE`. **`-EPIPE` needs two
  peers** sharing the device ring: e.g. 600 items for A and 425 for B fill
  the ring while each `prev_queue` holds fewer than 1024. The same holds for
  the decrypt ring and `rx_queue` (receive.c:526-533).
- **`-EPIPE` handling.** Send: `wg_queue_enqueue_per_peer_tx(first, DEAD)`
  (send.c:322-323), the tx worker frees the list (`:277-278`). Receive:
  `wg_queue_enqueue_per_peer_rx(skb, DEAD)` (receive.c:528-529) **inside the
  NET_RX softirq**: `napi_schedule` with `in_net_rx_action` set only adds the
  NAPI to `sd->poll_list` (`dev.c:4665-4669`), and `net_rx_action` polls it
  in the **same run** (`:7074-7083`: the recheck of `poll_list` after the
  list empties). The poll peeks the queue head, which is `UNCRYPTED`, and
  completes with `work_done = 0`.
- **`-ENOSPC` handling.** Send: `create_data` puts the keypair and peer and
  frees the list (send.c:326-330), no counter. Receive: `err` → puts and
  `dev_kfree_skb` (receive.c:534-539), no counter.

### 2.7 io_uring batches have no drain point

`io_submit_sqes`'s loop (`io_uring/io_uring.c:2282-2316`) has no
`cond_resched`; the one at `:2621` is in `io_cqring_wait`, which the fixture
does not enter (`min_complete = 0`, `task/e-b:harness/guest.c:769`). Under
`CONFIG_PREEMPT_NONE`, `__local_bh_enable_ip`'s `preempt_check_resched`
(`softirq.c:414`) is a no-op, and the UDP send path's `might_sleep` does not
reschedule. Each send to loopback runs its NET_RX inline at the sender's
`local_bh_enable` (`loopback_xmit` → `netif_rx`; `raise_softirq_irqoff`
does not wake ksoftirqd when `in_interrupt()`, which holds with BH disabled,
`softirq.c:695-710`; the pending softirq runs at `__local_bh_enable_ip`,
`:402-408`). So **K sends in one `io_uring_enter` are K inline NET_RX
sections in one system call, and no kworker runs until the call returns**
(E measured 1024 crossing a queue depth of 512 by this route; the 1025-item
case is probe P-A, section 12). The staged `wg_xmit` path is the same: each
send's `wg_xmit` runs inline (`__dev_queue_xmit`, `dev.c:4527-4559`) and
`create_data` only queues work (`queue_work_on`, `queueing.h:176`).

### 2.8 The workers' loops and the NAPI placement with several items

- **Decrypt worker** (receive.c:493-507): per item `ptr_ring_consume_bh`
  (`:499`; its `spin_unlock_bh` runs any pending softirq), `decrypt_packet`
  (one `.birthdateExpired` read, `:253`), `wg_queue_enqueue_per_peer_rx`
  (state, `napi_schedule`, `:503`), `cond_resched` if `need_resched`
  (`:504-505`, a resched record when it switches).
- **NAPI placement is pinned per item.** `napi_schedule` from the worker
  raises NET_RX and wakes ksoftirqd (`dev.c:4668-4669`, `softirq.c:708-709`).
  The pending softirq then runs at the latest at the next
  `local_bh_enable`, i.e. at the next item's `ptr_ring_consume_bh`
  (`softirq.c:402-408`; `do_softirq`, `:467-483`, has no ksoftirqd-running
  skip in 6.12; `invoke_softirq` at irq exit runs inline too, `:444-465`).
  So between item i's `napi_schedule` and item i+1's decrypt, the poll runs
  exactly once (order a, b or c of D2 §5), seeing items ≤ i `CRYPTED` and
  item i+1 `UNCRYPTED` — **in the `rx_queue` already** (all K were enqueued
  at `consume_data`), so the poll **peeks it and stops with `peeked`
  set** (`queueing.h:147-148`, receive.c:451-453). Every placement within
  the gap yields the same poll; the next poll returns the `peeked` item
  (`queueing.h:145-146`). The D2 hooks (loop head and after the enqueue,
  `RxData.lean:107,122`) therefore stay valid without a wider search
  (section 5.3).
- **Encrypt worker** (send.c:287-309) and **tx worker** (`:262-285`): the
  encrypt worker's `cond_resched` (`:306-307`) yields to the tx kworker when
  `need_resched` (D1 saw both directions; the resched record and the tx
  section start record the choice). The tx worker sends the `CRYPTED`
  prefix and stops at the first `UNCRYPTED` item, **leaving it peeked**
  (`:269-272`). Whether that happens is scheduling, and it is recorded.
- **Two peers in one `net_rx_action`.** From the worker path, impossible: the
  pending NET_RX is serviced before the next item (above). From the softirq
  path: `-EPIPE` inside `wg_packet_receive` for two peers in one softirq —
  a UDP GSO datagram to wg0's port fans its segments to `wg_receive` one by
  one in one NET_RX (`udp.c:2275-2280`, `udp.h:459-492`; E §4), so with the
  decrypt ring at 1023, segments 2 and 3 addressed to A and B both take
  `-EPIPE` and both NAPIs join `poll_list`, polled in order after the
  backlog poll (`dev.c:7090-7091`). Needs two sessions and a full ring: the
  stretch tier of section 7.
- **Budget (P9).** A poll processes at most the items `CRYPTED` since the
  previous softirq run: one from the worker path (above), or two when an irq
  exit lands between item i+1's `atomic_set_release` and its
  `napi_schedule`. `NAPI_POLL_WEIGHT = 64` (`netdevice.h:2632`, peer.c:57) is
  unreachable; `netdev_budget = 300` and the 2-jiffy limit (`hotdata.c:13-
  15`, `dev.c:7097-7101`) likewise. P9 stays out (section 10).

## 3. Hidden inputs

| Input | Site | Status | Used by |
|---|---|---|---|
| GSO segment ids | none: `id = 0` for the DO, unconnected sender (`ip.h:583-584`), then `id++` (`af_inet.c:1453`) | computed | W4 GSO bytes |
| GSO segment UDP checksums | none: software (`udp_offload.c:439-441`) | computed | W4 GSO bytes |
| IPv4 fragment ident, **connected** sender | `__ip4_datagram_connect`, `datagram.c:76`: `atomic_set(&inet->inet_id, get_random_u16())` | **new `HiddenSite` `.inetIdSeed`** (2 bytes, mirror) at the existing generic hook (kind 102); consumed by the mirror's `wg_connect` op; `ip_select_ident_segs` then reads `inet_id` (`ip.h:567-581`): id, id+1, … | W4 fragmentation |
| IPv4 fragment ident, unconnected `DONT` sender | `.ipIdentReserve` records `delta` only (`route.c:481-482`); the bucket counter is boot-random (`:3720`) | **not reconstructible**: stays `.cut`; the class is `unsupported` unless option K1 | — |
| IPv6 fragment id | `ipv6_select_ident` → `get_random_u32_above(0)` (`output_core.c:18`; kind 110 via `get_random_u32_below`) | **new `HiddenSite` `.ipv6FragId`** (4 bytes, mirror): id = record + 1. Confirm the consumer frame resolves to `output_core.c` (the static `__ipv6_select_ident` is inlined) before relying on it | W4 IPv6 fragmentation |
| `wg_xmit`'s `mtu` | route/device, fixture facts | environment (`Env.xmitPackets`), checked by padding bytes | W4 |
| wg0's IPv6 presence | `dev->mtu ≥ 1280` at registration / after `CHANGEMTU` | mirror state `Device.inet6Dev` | W4 `wg_open` |
| Scheduling: encrypt/tx/decrypt yields | kind 302 resched records (`.reschedEncrypt/.reschedTx/.reschedDecrypt`, `Defs.lean`) | existing, now per item | W7 |
| Scheduling: NAPI placement | NET_RX section records (kinds 300/301) | existing; pinned per item (2.8) | W7 |
| Ordering of several queued units | section start records | existing | W7 |

**Kernel-change options (need user approval; the design does not depend on
them):**
- **K1.** Record the ident at `__ip_select_ident` (`route.c:505`, after
  `ip_idents_reserve`) as a hidden site. Lifts the unconnected-`DONT`
  fragmentation class and would make `.ipIdentReserve`'s outer-datagram
  cut exact too (the wg outer IP header is not observed today, so that part
  pays nothing now).
- **K2.** Record `work_done` at the poll's `napi_complete_done`
  (receive.c:488) or the `state` the poll observes per iteration. Turns the
  "pinned per item" argument of 2.8 into a checked fact. Recommended only if
  the W7 corpus shows placements the argument does not cover (the
  `napi_orders.py` extension of section 8 reports them).
- The census's `handshake_queue_len` capture (P12) is not needed here.

## 4. W4 in the mirror and the environment

**Interface commit** (`Leanux/WG/Types.lean`, `Leanux/Kernel/Defs.lean`,
`Leanux/Kernel/Decision.lean`):
- `Device.mtu : Nat := 1420` (`wg_setup`, device.c:296) and
  `Device.inet6Dev : Bool := true`; `WG.DEVICE_MTU` is removed and its three
  readers (`Send.lean:255`, `Env.lean:75-76`, `Device.lean:42`) read the
  state. L's `wg_create` sets `mtu` from `IFLA_MTU` and `inet6Dev := mtu ≥
  1280`.
- `Packet.csum : Option (Nat × Nat)` already encodes `CHECKSUM_PARTIAL`
  (`Types.lean:134-137`); GSO segments and fragments carry `none`.
- New decisions, in `Decision.lean`'s `d name file line [true] [false]`
  form: `wg_xmit.gso_error` (device.c:181), `wg_xmit.staged_trim_iter`
  (`:211`, replacing the `unsupported` at `Device.lean:92-93`),
  `wg_open.has_inet` already exists (`.openHasInet`), `wg_prev_queue_dequeue.*`
  (section 5.1). `.xmitNotGso`, `.xmitWalk`, `.encChecksumPartial`,
  `.padOverMtu`, `.padClamped`, `.padNoMtu`, `.openHasInet6` gain their second
  outcome.
- New `HiddenSite`s `.inetIdSeed`, `.ipv6FragId` (section 3), both at the
  existing random hook; new sites follow E's precedent (`.cookieNonce`).

**`Device.lean`:**
- `wgXmit (family addr : Nat) (pkts : List Packet) (mtu : Nat)`: the GSO
  branch (`.xmitNotGso` false → `skb_gso_segment`, `.xmitGsoError` with
  `envOk .skbSegment` from A, `dev_kfree_skb`), the walk over `pkts`
  (`.xmitWalk` n+1 iterations, `.xmitShareFailed` false), `PACKET_CB->mtu :=
  mtu` on each; the trim as the real loop with `txDropped += 1` per
  iteration; the splice. `wg_xmit` returns once per call; fragmentation is
  two calls (below).
- `wgOpen`: `.openHasInet` from `Device.inet4Dev` (false only after an MTU
  below 68), `.openHasInet6` from `Device.inet6Dev`.
- `setMtu (mtu : Nat) : M Int` for `SIOCSIFMTU`: `dev_set_mtu` is a cut
  (its validation against `max_mtu`, device.c:297, is mirrored as a
  decision); on success `Device.mtu := mtu`, `inet6Dev := mtu ≥ 1280`,
  `inet4Dev := mtu ≥ 68`. The address and route teardown below those
  thresholds is a fixture consequence the environment records (the sender's
  later `sendto` into wg0 is `unsupported` after it).

**`Send.lean` / `Data.lean`:** `sendKeepalive` reads `Device.mtu`;
`calculateSkbPadding` is unchanged (its arms exist); `encryptPacket`'s
`.encChecksumPartial` takes `inner.csum.isSome` as today, now false for GSO
segments and fragments.

**`Env.lean`:**
- `xmitPackets (family addr : Nat) (payload : List UInt8) (opts : XmitOpts) :
  M (List (List Packet) × Nat)` replaces `xmitPacket`: the outer list is the
  `wg_xmit` calls of one `sendto`/`sendmsg` (one, or two for a fragmented
  datagram), the inner list the packets of one call (the GSO segments, or
  one packet), and the `mtu` `wg_xmit` computes. `XmitOpts` carries
  `gsoSize`, `pmtudisc ∈ {DO, DONT, PROBE}`, `connected`, and the fixture's
  route MTU for the destination (from the trace's `net_fixture`, section 6).
  It computes:
  - GSO: segment i's IPv4 header (`id = i`, `tot_len`, header checksum), UDP
    header (`len`, the complete checksum, `CSUM_MANGLED_0` for 0), payload
    slice; `csum := none`. The stack's `-EMSGSIZE`/`-EINVAL` conditions
    (2.1) are the operation's result with no `wg_xmit`.
  - Fragmentation (`DONT`, length > route MTU): the datagram's UDP checksum
    over the whole payload; fragment 1 (`MF`, 1400 payload bytes on IPv4),
    fragment 2 (offset 175); the id from `.inetIdSeed` (connected) — the
    unconnected case is `unsupported "an unconnected sender's fragment
    ident (route.c:488 over a boot-random bucket)"`. IPv6: the Fragment
    header with `.ipv6FragId`.
  - `PROBE` with a route MTU: a full-size packet with `mtu` = route MTU.
  - Multicast/link-local: source, TTL/hop limit per 2.4; `xmitBytesUnknown`
    shrinks to destinations the fixture does not determine.
- `xmitMulticastLoop` (from d3-int) gains the IPv6 membership set
  `{ff01::1, ff02::1} ∪ solicitedNode(wg0's addresses)`.
- `MAX_XMIT_PAYLOAD*` become functions of `Device.mtu` and the route MTU.
- `fixtureSend`'s cut list is unchanged (a connected sender draws no
  `ip_idents_reserve`; the cut is lax).

## 5. W7 in the mirror and the environment

### 5.1 `prev_queue` as data

```lean
structure PrevQueue (α) where
  items : List α := []      -- enqueued, not yet dequeued (= count)
  tailIsStub : Bool := true -- queue->tail == STUB
  peeked : Option α := none
```
`enqueue` fails when `items.length ≥ MAX_QUEUED_PACKETS` (queueing.c:74).
`dequeue` mirrors queueing.c:80-106 with decisions
`wg_prev_queue_dequeue.tail_is_stub` (`:84`), `.stub_empty` (`:85`),
`.more_remain` (`:91`), `.tail_not_head` (`:96`, outcome true is P5:
`unsupported`), `.restub_next` (`:100`): with `tailIsStub` and `items = []`
→ none; with `items = [x]` → re-stub, return `x`; with two or more → return
the head, `tailIsStub := false`. `peek` and `dropPeeked` as queueing.h:143-
155 (`.prevQueuePeeked` both outcomes). `Peer.txQueue : PrevQueue (List
DataPacket)`, `Peer.rxQueue : PrevQueue RxPacket` replace the lists
(`Types.lean:219,222`). `wg_prev_queue_dequeue` is added to
`correspondence/kcov.json`'s function set (not present today).

### 5.2 Multi-item queues

- `enqueuePerDeviceAndPeer` (`Send.lean:126-144`) drops the two one-item
  `unsupported`s (`:133`, `:140`); the `-ENOSPC`/`-EPIPE` branches are already
  decisions (`.enqueuePeerQueueFull`, `.enqueueRingFull`). The receive twin
  (`Receive.lean:174-183`) likewise; `consumeData`'s `.dataEpipe` arm
  (`Receive.lean:213`, `invariant "unreachable"`) becomes
  `enqueuePerPeerRx pkt .dead`.
- `txWorker` (`Data.lean:184-206`) and `rxPoll` (`RxData.lean:276-318`): peek
  through `PrevQueue`; an `UNCRYPTED` head ends the loop with it peeked (the
  `unsupported`s at `Data.lean:194` and `RxData.lean:288` go). `rxPoll`'s
  budget arm stays `unsupported` (P9, section 10).
- `encryptWorker`/`decryptWorker` already loop over the ring
  (`Data.lean:101-129`, `RxData.lean:104-124`); `MAX_QUEUED_PACKETS + 1`
  bounds remain.
- NAPI: `Kernel.napiPollList : List PeerId` in `napi_schedule` order replaces
  the per-peer `napiScheduled` flag as the softirq's worklist (the flag
  stays as `NAPI_STATE_SCHED`); `Env.napiSoftirq` (`Env.lean:457-466`) polls
  the list in order and drops its `unsupported` at `:462`. A NAPI scheduled
  inside `wgReceive` (the `-EPIPE` arm) is polled in the same `runWorker
  .netRx` body, after the receive (2.6).

### 5.3 Scheduling: recorded, searched, argued

| Placement | Evidence | Mirror |
|---|---|---|
| A worker yields at `cond_resched` and another unit with queued work runs | resched record + the unit's section start | `Env.condResched` (`Env.lean:238-262`), generalized to run **any** of encrypt/tx/decrypt whose start is next and whose queue is non-empty (today only encrypt and tx) |
| The poll runs in ksoftirqd (a) | resched record, top-level NET_RX section | existing |
| The poll runs inline / at irq exit (b/c) | nested NET_RX section start between the worker's records | existing hooks; per 2.8 the gap pins the item and both hooks agree, so **no new search** |
| An irq exit between `atomic_set_release` and `napi_schedule` of item i+1 | nested NET_RX section after item i+1's clock read | the poll processes two items; the hook after the enqueue covers it (the order of records tells) |
| A unit resumes above the mirror's stack with work pending | a resched record followed by no runnable section start, while an open worker has queued work | **fail-closed** (5.4) |

`evaluator/napi_orders.py` is extended to count, per trace, the number of
polls per decrypt-worker run, the items per poll, and the (a)/(b/c) split;
the W7 corpus must show polls with the `peeked` arm taken and at least one
two-item poll if it occurs, else the mutant that ignores the peeked slot
(W7-M3) is reported inconclusive, as D2 did for D2-M12.

### 5.4 The commuting assumption

`runWorker` (`Env.lean:200-217`) lets a worker that switched away finish in
the mirror at once, leaving its section stop pending, because "each rest is
a worker's final empty ring or queue poll". With several items that is
false in one case: the tx worker yields at send.c:282-283 (tick-driven;
D1 saw one tx yield in 1334 traces) while the encrypt worker, open higher
on the mirror's stack, still has ring items; Linux resumes the encrypt
worker, which crypts more items before the tx worker resumes; the mirror's
tx worker would resume to the old queue. The same shape arises for the
decrypt worker vs. ksoftirqd only if `net_rx_action` yielded mid-poll, which
it does not.

- **Phase 1 (required):** `condResched` detects "yield with no runnable
  section start while another open worker has queued work" and returns
  `unsupported "a worker resumed above the mirror's stack with work
  pending"`. A `napi_orders.py` counter reports how often it occurs on the
  existing D1/D2 corpus records (no VM run needed: a `.reschedTx` record
  inside an open encrypt section with items left).
- **Phase 2 (if phase 1 loses many bulk traces):** the four units become
  step functions (`encryptStep`, `txStep`, `decryptStep`, `rxPollStep`,
  each one loop iteration) and the environment interleaves steps by the
  records. The mirror code per step is the C's loop body unchanged; only
  the loop driver moves to the environment. This is the thin layer's
  natural shape and is the recommendation if phase 1's counter exceeds a
  few percent of bulk traces.

### 5.5 The batch operation

`wg_batch` (generalizing E-B's `wg_flood`, `task/e-b:harness/guest.c:700-
775`, opcode 18): a list of items, each `inject {family, port, message}` or
`xmit {packet, payload, opts}`, all on `SEND_FD`, prepared as SQEs before
the window (`flood_prep`'s pattern), one `io_uring_enter`, then a wait.
In the environment (`Env.batch`): for each item in order, `fixtureSend` and
`runWorker .netRx (wgReceive …)` for an inject (plus any `-EPIPE` poll), or
`wgXmit` for an xmit — no worker runs between items (2.7); after the loop,
the deferred units run as the records order them: `runDecryptWorker` and
`runCryptWorkers` (which already follow section starts), with `afterXmit`'s
rule that a call queuing both crypt work and a handshake is `unsupported`
(`Env.lean:321-329`) relaxed to "ordered by their section starts". The
guest's wait after a batch is a trace parameter (`wait_ms`, default 100,
measured in P-A); a worker outliving it shows as missing section records
(the `opened` count check from D1).

## 6. Harness

- **Ops** (`harness/trace.py` FIELDS, `harness/wg.py`, `harness/guest.c`):
  - `wg_xmit` gains optional `gso_size` (cmsg `UDP_SEGMENT`), `pmtudisc`
    (`do` default, `dont`, `probe`; set per op with `IP_MTU_DISCOVER` /
    `IPV6_MTU_DISCOVER` before the send and restored after), `connected`
    (a second dual-stack sender `SEND2_FD`, bound to `SENDER_PORT + 1`,
    `connect()`ed **inside the window** so `.inetIdSeed` is recorded, then
    `send()`), `multicast_loop` (`IP(V6)_MULTICAST_LOOP`), and a payload up
    to 65507 bytes (`MAX_PAYLOAD` raised; `wg.py:357-362`'s MTU bound becomes
    a per-`pmtudisc` rule).
  - `wg_set_mtu {mtu}`: `SIOCSIFMTU` via `SEND_FD`'s ioctl (as `wg_up` uses
    `SIOCSIFFLAGS`, `guest.c:926-931`).
  - `wg_create` gains `mtu` (`IFLA_MTU`).
  - `net_fixture` (already an optional trace field, `trace.py:73`) gains
    `routes: [{dst, mtu}]`, `link_local: "fe80::1/64"`, `allowed_ips` for the
    peer config is unchanged (the generator adds `224.0.0.0/4`, `ff00::/8`,
    `fe80::/64` where a class needs them).
  - `wg_batch {items: [...], wait_ms}`: section 5.5. `MAX_PAYLOAD` (32768,
    `guest.c:32`) and `line` (`:75`) grow to hold 1025 messages;
    `SO_RCVBUFFORCE` (8 MiB) on both listeners and `SEND_FD`, since the
    default `rmem_default` (`sock.c:287`, 212992) holds about 270 small
    datagrams and the bulk tiers deliver up to 1025.
  - `wg_observe` for bulk: the listener drain (`guest.c:563-600`) reports
    every datagram as today; for the full-ring tier the generator uses
    keepalive data messages (32 bytes, 48 as ciphertext) so the observe line
    stays under a few hundred KiB; the message counters (bytes 8-16) show
    which item was dropped.
  - KCOV capacity: `CAPACITY` is 64K words on `main` (`guest.c:31`) and
    already 1M words on `task/e-b` (`guest.c:37`, raised for the flood). A
    1025-item batch at roughly 300 PCs per message fits the PC child, but
    the comparisons child (four words per record, `trace.py:52`) may not. A
    per-trace `kcov_capacity` (bulk: 4M words = 32 MiB, both the task and
    the remote area; the VM has 256 MiB) replaces the constant;
    `validate_coverage` already fails a full buffer. P-A measures the
    actual record volume.
- **`harness/noise.py`:** GSO segment and fragment builders (headers,
  checksums, ids) anchored to the mirror's `Env.xmitPackets` by `#guard`
  vectors and to Linux by the A1 bytes; batches of data messages under a
  session with counter lists.
- **Generator** (`scripts/wg-w47-corpus.py`, classes; the corpus
  `corpus/wireguard/w4_*.json`, `w7_*.json`):
  - `w4_gso_{4,6}_{n}`: after a session, one GSO xmit of n ∈ {2, 3, 128}
    segments, `gso_size` ∈ {8, 1392 or 1372, a non-divisor so the last
    segment is short}; expect n ciphertexts.
  - `w4_gso_trim`: no session; two GSO xmits of 128, a third of 1; expect
    `tx_dropped = 128`; then the offline response flushes 129.
  - `w4_route_mtu_probe_{4,6}`: route MTU 1300, `PROBE`, payload 1392/1372;
    the modulo arm and the clamp.
  - `w4_set_mtu_{1000,1279,1280,0}`: `wg_set_mtu` then xmits and a keepalive
    (`wg_set` with `persistent_keepalive`), `wg_down`/`wg_up` for the
    `wg_open` arms; `_0` ends with the keepalive.
  - `w4_create_mtu_1279`: L's `wg_create` with `IFLA_MTU`, `wg_up`.
  - `w4_frag_{4,6}_connected`: `connected`, `DONT`, payload 2000; expect two
    ciphertexts. `w4_frag_4_unconnected` is a **domain control**: expected
    `unsupported`.
  - `w4_mcast_{4,6}`, `w4_mcast_6_nomember`, `w4_mcast_noloop`,
    `w4_linklocal_6`: 2.4.
  - `w7_multi_rx_{2,4,8}`: a batch of n data messages under a session
    (valid; one tampered in `_dead`); `w7_multi_tx_{2,4,8}`: a batch of n
    xmits; `w7_mixed`: injects and xmits in one batch (encrypt and decrypt
    workers both queued).
  - `w7_full_rx_1025`, `w7_full_tx_1025`: the `-ENOSPC` arms (keepalive
    messages / 1-byte payloads), `rx_bytes`/counters as observables.
  - `w7_epipe_rx`, `w7_epipe_tx`, `w7_two_napi`: **stretch** — two sessions
    (two steered handshakes; `STEER_MAX = 64` entries suffice), the ring
    at 1024, and for `w7_two_napi` a GSO datagram to wg0's port carrying
    data messages for A and B.
  - Isolation: bulk traces one per chunk (as E's under-load traces), since
    their wall time is a large share of the 4.5 s bound (`TRACE_BOUND_MS`,
    `task/d3-int:Leanux/Env.lean:55`).

## 7. Observables

- **A1 bytes** at the listener: every GSO segment's ciphertext (ids,
  lengths, the software UDP checksum, `CSUM_MANGLED_0`), both fragments
  (same id, `MF`/offset, `CHECKSUM_NONE` so no `skb_checksum_help`
  rewrite), padding under the route MTU, multicast/link-local sources and
  hop limits (inside the ciphertext).
- **Counters** (`wg_observe` stats, `guest.c:557-559`): `tx_dropped` at the
  trim (128), `tx_errors` for `IS_ERR(segs)`; the dump's `rx_bytes`
  (`32 × accepted` for keepalive batches) and `tx_bytes`.
- **Bulk membership:** the set of message counters that arrived (the
  `-ENOSPC`/`-EPIPE` item is missing; the DEAD list is missing whole).
- **Inner datagrams** at `SEND_FD` for valid payload batches.
- **A2 control flow and operands:** the new arms of section 4 and 5.1-5.2;
  the trim's iteration count; `wg_prev_queue_dequeue`'s arms;
  `.prevQueuePeeked` true; `.encChecksumPartial` false.
- **Section and resched records:** per-item yields, the pinned poll
  placements, two NAPIs in one NET_RX section.

## 8. Evidence: what pays for itself

Mutants rejected only on W4/W7 traces (each names the trace that rejects
it):
- **W4-M1** GSO segment ids not incremented (all 0) — `w4_gso_4_3` bytes.
- **W4-M2** the GSO last segment padded to `gso_size` — `w4_gso_*` with a
  non-divisor.
- **W4-M3** segment checksum left as the pseudo-header partial — bytes.
- **W4-M4** `skb_checksum_help` applied to a `CHECKSUM_NONE` packet — bytes
  (the field would change) and the `.encChecksumPartial` operand.
- **W4-M5** trim before splice replaced by trim after (drops the new
  segments) — `w4_gso_trim`'s `tx_dropped` and the flushed counters.
- **W4-M6** trim at `≥ 128` — `w4_gso_trim` (`tx_dropped` 129 vs 128).
- **W4-M7** `mtu` from `dev->mtu` instead of `dst_mtu` — `w4_route_mtu_probe`
  padding bytes.
- **W4-M8** `last_unit %= mtu` dropped — same trace (padding 8 vs clamp).
- **W4-M9** keepalive padded with `Device.mtu` ignored (`!mtu` arm) —
  `w4_set_mtu_0` A2 operands (bytes equal: honest).
- **W4-M10** `wg_open`'s `dev_v6` constant true — `w4_create_mtu_1279` A2.
- **W4-M11** fragment 2 given a UDP header / wrong offset — `w4_frag_*`
  bytes.
- **W4-M12** fragment ident not from `.inetIdSeed` (0) — bytes; the
  **control** `w4_frag_4_unconnected` must be `unsupported`, not a pass.
- **W4-M13** IPv6 multicast loop modelled for a non-member group —
  `w4_mcast_6_nomember` (an extra NET_RX section expected: section
  mismatch).
- **W7-M1** `-ENOSPC` tested after the ring produce — `w7_full_tx_1025` A2
  (and the `-EPIPE` decision taken).
- **W7-M2** the 1025th item sent anyway — `w7_full_*` counters.
- **W7-M3** `peeked` ignored (re-dequeue) — `w7_multi_rx_4`: the peeked
  item is lost (`rx_bytes`, inner datagrams), A2 `.prevQueuePeeked`.
- **W7-M4** `tailIsStub` never reset (the re-stub arm skipped) — A2 on
  `w7_multi_*` (the dequeue decisions).
- **W7-M5** the tx worker continuing past an `UNCRYPTED` head — a hidden
  mismatch on the trace where the encrypt worker yielded (recorded), else
  inconclusive, reported.
- **W7-M6** DEAD break not breaking (remaining packets encrypted) — `w7_multi_tx_dead` (needs A's `skbCowHead` steer on the k-th call; else this mutant waits for A).
- **W7-M7** polls serving one peer when two are pending — `w7_two_napi`
  (stretch).
- **W7-M8** `-EPIPE` item not marked DEAD on receive — `w7_epipe_rx`
  (stretch): the poll would deliver it.
- **W7-M9** the scheduler ignoring per-item resched records (D1-M15's
  bulk form) — any `w7_multi_*` trace with a yield.

Controls: `w4_frag_4_unconnected` (`unsupported`), the phase-1 commuting
detector on a synthetic record stream (a `.reschedTx` with the encrypt
queue non-empty must be `unsupported`), and the measurement probes of
section 12 re-run on any new kernel.

## 9. Out of scope (fail-noisy), and why

| Item | Why |
|---|---|
| P5 arms: `wg_prev_queue_dequeue`'s `tail != head` (queueing.c:96-97, 105), concurrent producer mid-enqueue | SMP or in-region preemption |
| P9: a poll using its budget (receive.c:483-488), `net_rx_action`'s squeeze | at most two items per poll on one CPU (2.8) |
| Unconnected `DONT` fragmentation; `IP_PMTUDISC_WANT`/`OMIT`/`INTERFACE` | the ident over a boot-random bucket (3); K1 would lift it |
| More than 128 GSO segments, `gso_size + 28 > fragsize` | the stack returns `-EINVAL`/`-EMSGSIZE` before `wg_xmit` (`udp.c:988-995`) |
| GSO plus fragmentation (`DONT` with `gso_size`) | `cork->gso_size` sets `mtu = IP_MAX_MTU` (`ip_output.c:992`), no fragments; nothing new |
| `IS_ERR(skb_gso_segment)`, `encrypt_packet` failures mid-list without A | allocation failures: stream A's capture and steering |
| IPv6 extension headers, IPv4 options on transmit | W6 |
| `-EPIPE`, two NAPIs in one `net_rx_action` | the stretch tier (two sessions); the mirror arms are built, the traces follow |
| Phase 2 step workers | only if phase 1's detector fires often (5.4) |
| A second device sharing nothing | W13 (rings are per device) |
| Receive-side rcvbuf drops at `SEND_FD` | avoided by `SO_RCVBUFFORCE`; a trace that overflows it is `unsupported` by the delivery predicate, not modelled |
| Timers firing during a bulk run | D3's bound; bulk traces are sized inside it (P-A) |

## 10. P9 re-derived

The census excluded NAPI budget exhaustion because "a poll sees at most one
packet on one CPU". W7 changes "one" to "the items `CRYPTED` since the
previous softirq run". Section 2.8 shows that is one from the worker path
(the pending softirq is serviced at the next `ptr_ring_consume_bh`,
`softirq.c:402-408`) or two at an irq exit inside `wg_queue_enqueue_per_peer_rx`.
Sixty-four needs sixty-four worker iterations without a `local_bh_enable`,
which the worker loop does not have. The `-EPIPE` poll inside NET_RX
processes zero. P9 stays excluded, with this argument replacing the
census's.

## 11. Risks

- **Low — W4 bytes.** Every W4 fact is checked by ciphertext bytes; a wrong
  segment checksum, id or padding fails noisily on the first trace.
- **Medium — the environment's stack model** (GSO segmentation, fragment
  geometry, source selection). Each fact is verified once by a trace before
  the generator relies on it (D2's method); the `#guard` vectors tie
  `noise.py` and `Env.xmitPackets`.
- **Medium — W7 timing on TCG.** Unknown until P-A: the per-send cost of
  io_uring + loopback + `wg_receive` under KCOV, 1024 AEADs in the worker,
  1024 loopback deliveries in the tx worker, and the record volume. If a
  1025-item batch does not fit the bound, the full-ring tier shrinks to the
  mirror arms with a domain `unsupported` and the multi-item tiers (2-8)
  carry W7.
- **Medium — the commuting assumption** (5.4). Phase 1 is fail-closed; the
  cost is lost traces, measured before phase 2 is decided.
- **Low — the pinned-placement argument** (2.8) rests on `softirq.c:402-408`
  and `:467-483`; K2 would make it a checked fact if the extended
  `napi_orders.py` ever reports a placement outside the argument.
- **Fixture state changes** (`wg_set_mtu` below 1280/68) remove addresses
  and routes; the generator keeps those classes terminal.
- **Observe volume** for 1025-item traces: the line and JSON sizes; bounded
  by using keepalive messages for the full-ring tier.

## 12. Execution plan

Base: the integrated D3+L+A+E tip (D3 for `Env.timing`, `wg_advance`,
`xmitMulticastLoop`; L for `wg_create` and `Device` ownership; A for the
`envOk`/alloc steering sites `skbCowHead`, `skbCowDataTx`
(`task/a1:Leanux/Kernel/Defs.lean:264-267`); E for `wg_flood`'s io_uring
plumbing and the chunk isolation). Worktrees and branches as in D1-D3; one
signoff at the end for the merge (no kernel change unless K1/K2 is
approved).

**Probes first (gating, throwaway, `harness/probes/w47_*.c`):**
- **P-A** bulk feasibility: 1025 io_uring sends of data messages to wg0's
  port and 1025 xmits into wg0, under KCOV with a 2M-word area: wall time
  from `enter` to idle workers, whether every item queued before any worker
  ran (`-ENOSPC` observed exactly once), record counts, observe size. Also
  128-segment GSO xmit timing.
- **P-B** fixture facts: `ip -6 addr show wg0` after `wg_up` (no `fe80`
  expected); `ip link set wg0 mtu 0` accepted; `ip -6 maddr show wg0`
  (membership set); a `PROBE` send over a `mtu 1300` route reaching
  `wg_xmit` unfragmented (one ciphertext of 1460 bytes).
- **P-C** (offline, no VM): the phase-1 counter over the existing D1/D2
  check runs' `hidden.jsonl`.

**Interface commit** (on `task/w47`): `Device.mtu`, `inet4Dev`, `inet6Dev`;
`PrevQueue`; `Kernel.napiPollList`; the new decisions and hidden sites; the
op schemas (`wg_xmit` options, `wg_set_mtu`, `wg_create.mtu`, `net_fixture`
routes, `wg_batch`, `kcov_capacity`, `wait_ms`); `DEVICE_MTU` removed.

**Streams and file ownership:**
- **T — transmit shapes (W4):** `Leanux/Env.lean` (`xmitPackets`,
  multicast membership, `setMtu` consequences), `Leanux/WG/Device.lean`
  (`wgXmit` GSO/trim/`wgOpen`), `Leanux/WG/Send.lean` (`sendKeepalive`),
  `harness/noise.py` (segment/fragment builders), `harness/guest.c` W4 ops
  and fixture (`route_into_wg0`, `SEND2_FD`, sockopts).
- **B — bulk (W7):** `Leanux/WG/Send.lean` (`enqueuePerDeviceAndPeer`),
  `Leanux/WG/Data.lean` (`txWorker`), `Leanux/WG/RxData.lean` (`rxPoll`,
  `enqueuePerPeerRx`), `Leanux/WG/Receive.lean` (`consumeData` arms),
  `Leanux/Env.lean` (`batch`, `napiSoftirq`, `condResched` generalization,
  the phase-1 detector), `harness/guest.c` `wg_batch` (from `wg_flood`),
  `kcov_capacity`.
- **H — harness, generator, corpus, evidence:** `scripts/wg-w47-corpus.py`,
  `corpus/wireguard/w4_*`, `w7_*`, `scripts/wg-mutants.py` patterns W4-M*
  and W7-M*, `evaluator/napi_orders.py` extension, the probes and their
  results note.

**Integration:** the full check with bulk traces one per chunk, the W4/W7
mutants and controls, the phase-1 counter report, the report and signoff.
Phase 2 (step workers) and the stretch tier are separate decisions after
integration.

## 13. Decisions for the user

1. **The fragment-ident route.** Build fragmentation on a **connected**
   sender (`.inetIdSeed`, no kernel change) and leave the unconnected
   `DONT` class `unsupported`; or approve **K1** (capture the ident at
   `route.c:505`) and cover both. Recommendation: the connected sender now;
   K1 only if the outer-header bytes ever become an observable.
2. **K2** (record the poll's `work_done`): not recommended now; revisit if
   the extended `napi_orders.py` reports a placement the argument of 2.8
   does not cover.
3. **The commuting assumption:** phase 1 (fail-closed detector) is required;
   phase 2 (step workers) is a restructuring of four mirror loops, decided
   on P-C's and the W7 corpus's counts.
4. **The full-ring tier (1025 items)** depends on P-A. If it does not fit
   the 4.5 s bound on TCG, keep the `-ENOSPC` arms as built mirror code with
   the domain `unsupported`, and carry W7 on the 2-8-item tiers.
5. **The stretch tier** (`-EPIPE`, two NAPIs; two sessions): build the
   mirror arms in B (cheap), schedule the traces after integration.
6. **`wg_set_mtu 0`** and its address teardown: include as a terminal class
   (it reaches three otherwise unreachable arms), or exclude as unreasonable.
7. **The D2 correction** (wg0 has no link-local address): record it in D2's
   note at integration.

## 14. Verified claims (file:line index)

- device.c: `wg_open` 31-62 (`dev_v4` 33/39, `dev_v6` 34/47-48, peers 54-58);
  `wg_xmit` 137-234 (mtu 173, GSO 176-187, walk 189-204, trim 206-216,
  `err_icmp` 225-229, `tx_errors` 231); `wg_setup` 274-307 (features 277-279,
  `IFF_NO_QUEUE` 291, mtu 296, `max_mtu` 297); queues 348-356.
- send.c: `keep_key_fresh` 124-139; `calculate_skb_padding` 141-160;
  `encrypt_packet` 162-219 (187-189); keepalive 221-240 (232); tx worker
  262-285; encrypt worker 287-309; `create_data` 311-331; staged 342-414.
- queueing.h: 59-65, 143-155, 157-178, 180-203. queueing.c: 72-78, 80-106.
  messages.h: 51-53. ptr_ring.h: 49-52, 104-117, 158-166, 487-489.
- receive.c: `decrypt_packet` 242-292 (253); `rx_poll` 438-491; decrypt
  worker 493-507; `consume_data` 509-540; `wg_packet_receive` 574-577.
- udp_offload.c: 326-482, 484-507. af_inet.c: 1369-1470 (1410-1411, 1439-
  1457). skbuff.c `skb_segment`: 4763-4764, 4881-4882, 4913-4923, 5007-5020.
  gso.c: 66-73, 88-131. netdev_features.h: 213-214. loopback.c: 79, 177-179.
- dev.c: `gso_features_check` 3598-3649; `validate_xmit_skb` 3764-3820;
  `__dev_queue_xmit` 4453-4588 (4510-4559); `____napi_schedule` 4637-4669;
  `net_rx_action` 7052-7115; `__dev_open` 1541-1552 (`ndo_open` 1552),
  `dev_open` 1588-1593; `__dev_set_mtu` 9048-9058; `dev_validate_mtu`
  9061-9075; `dev_set_mtu_ext` 9085-9122. netdevice.h: 2632. hotdata.c:
  13-15. peer.c: 57.
- softirq.c: `__local_bh_enable_ip` 384-415 (402-408, 414); `invoke_softirq`
  444-465; `do_softirq` 467-483; `raise_softirq_irqoff` 695-710.
- ip_output.c: `__ip_finish_output` 296-315; `ip_mc_output` 367-424;
  `ip_fragment` 583-603; `ip_fraglist_init/prepare` 605-648;
  `ip_do_fragment` 768-941; `__ip_append_data` 992-1016; `ip_setup_cork`
  1307-1311; `__ip_make_skb` 1397-1470.
- ip.h: 39, 457-467, 469-495, 511-525, 559-595, 833. route.c: 469-489,
  491-506, 1366-1369, 3718-3722. datagram.c: 76. random.h: 98-103.
  output_core.c: 14-19, 47. ip6_output.c: 86-99, 209-215, 873-977, 1401-
  1405. ip6_route.h: 269-281.
- udp.c: 897-930, 984-1031, 1081-1085, 2275-2280, 2810-2814. udp.h (linux):
  111. udp.h (net): 459-492. ipv6/udp.c: 1294-1319.
- addrconf.c: 296, 381-382, 392, 466-471, 3445-3487, 3489-3524, 3683-3711.
  devinet.c: 1576-1580, 1637-1643. rtnetlink.c: 2987-2992, 3517-3526.
  af_inet.c: 364. af_inet6.c: 223. ipv6.h: 53, 905. sock.c: 287, 1355, 3585.
- io_uring.c: 2282-2316, 2621.
- Mirror: `Leanux/WG/Send.lean` 31-48, 126-144, 250-256; `Data.lean` 51-58,
  69-93, 101-129, 184-206; `RxData.lean` 104-124, 276-318; `Receive.lean`
  174-183, 213; `Device.lean` 43-55, 65-97; `Env.lean` (census) 100, 125-144,
  152-163, 200-217, 238-262, 266, 273-292, 321-329, 457-466, 471-474, 480-
  495; `task/d3-int:Env.lean` 55, 62-64, 90-93; `Types.lean` 134-137, 219,
  222-223, 298, 304; `Defs.lean` 262, 322-323; `Decision.lean` 943-944, 986;
  `task/a1:Defs.lean` 264-267; `harness/guest.c` (main) 31-32;
  `task/e-b:harness/guest.c` 37-38, 45, 52-53, 59, 557-559, 563-600,
  700-775, 821-825, 926-931, 969-974, 1050;
  `task/e-b:harness/trace.py` 19-48, 52, 73, 101; `harness/wg.py` 332-370;
  `evaluator/check.py` 696-703; `evaluator/napi_orders.py`.
