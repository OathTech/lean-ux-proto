# W4 + W7: transmit shapes and bulk queues — design, 2026-10-06

Status: **proposed, revision v2** [AGENT], for the user's decisions in
section 13. Revision v2 (2026-10-06) answers a critical audit; section 15
gives each finding's disposition, and the body below is corrected in place
(the v1 text is in the commit history of `task/w47-design`). The census
([2026-10-06-wireguard-census.md](2026-10-06-wireguard-census.md)) lists W4
(transmit shapes, M) and W7 (bulk and multi-item queues, L) as in-reach
workstreams toward the user's goal of 2026-10-06, 100% of reasonable
single-CPU WireGuard. P5 (concurrency recheck arms) stays excluded. P9 (NAPI
budget exhaustion) is **reachable on one CPU** in the stretch tier (section
10, corrected in v2); its treatment is decision 13.5.

Line numbers are in the unpatched `.deps/linux` (6.12.110) unless a file is
named as patched. The kernel is `kernel/config-x86_64-net-choice`: one CPU,
`CONFIG_PREEMPT_NONE`, `HZ=250`, `CONFIG_IO_URING=y` (`:201`), `NR_CPUS=1`
(`:290`), `CONFIG_IP_MULTICAST` off (`:686`, so no `CONFIG_IP_MROUTE`),
`CONFIG_IPV6_MULTIPLE_TABLES` off (`:724`). Mirror references are to
`task/census` (= `main` + the census; section 14 gives the `main` line for
each `Decision.lean` reference) and `task/d3-int`/`task/e-b` where named.
The base for implementation is the integrated D3+L+A+E tip (section 12).

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
  queues** (`Leanux/Env.lean:200-217`; `task/d3-int:Leanux/Env.lean:236-245`:
  "each rest is a worker's final empty ring or queue poll"). The breakage is
  generic (v2, M7): **any** yield by a unit nested on the mirror's stack
  while an outer open worker still has queued items, since Linux may resume
  the outer worker first and the mirror cannot. Section 5.4 makes this
  fail-closed first, in the generic form, and gives the step-worker
  restructuring as the full fix.

## 1. Target

**W4 — transmit shapes.** Every `wg_xmit` arm the IP stack can reach on one
CPU, with its bytes checked at the fixture's listener:
- UDP GSO: one `sendmsg` with `UDP_SEGMENT` arrives at `wg_xmit` as one GSO
  skb; `skb_gso_segment` splits it; the segments are **one staged list** and
  **one ring item** (device.c:176-204, 215, 218).
- The staged-queue trim, `> MAX_STAGED_PACKETS` (device.c:211-214), reachable
  with two or three GSO transmissions and no session.
- The padding arms of `calculate_skb_padding` (send.c:141-160) not yet
  taken: `len > mtu` (`:154-155`, `.padOverMtu` true) via a route MTU below
  the device MTU, and `!mtu` (`:145`, `.padNoMtu` true, only with a device
  MTU of 0: decision 13.6). The `min` clamp (`:157-158`, `.padClamped`) is
  **already two-outcome** since D2 (inner lengths 1404-1420, D2 §6; v2, M8).
  `SIOCSIFMTU` and `IFLA_MTU` at creation move the device MTU and the
  `wg_open` arms.
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
    → `:559-589`, **`segs = 1`** for UDP): for the fixture's **unconnected,
    `IP_PMTUDISC_DO`** sender, `DF && !ignore_df` → **`id = 0`**
    (`ip.h:583-584`; `ignore_df` from `ip_sk_ignore_df`, `:462-467`). So the
    segments carry ids 0, 1, …, n−1: deterministic, no hidden input. For the
    **connected** sender `SEND2_FD` (section 3, v2 M2) the branch at
    `ip.h:568-581` runs first regardless of DF: `id = atomic_add_return(1,
    &inet_id)`, so one datagram consumes one `inet_id` value whatever its
    segment count, and its segments carry `id, id+1, …`. IPv6 segments have
    no id.
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
- xmit 1, 128 segments: the trim test is `0 > 128`, false (the queue is
  empty before the splice); staged = 128;
- xmit 2, 128 segments: `128 > 128` false; staged = 256;
- xmit 3, any size n: `256 > 128`: 128 iterations drop the oldest 128
  (`tx_dropped += 128`), then staged = 128 + n.

Two GSO transmissions reach 256 staged; the third takes the loop. When the
offline response completes the session, the flush is **one ring item of
128 + n packets** through the encrypt and tx workers (W7's multi-packet item
on the send side). With a small `gso_size` (8 bytes) each segment is a
36-byte inner packet, padded to 48, so the 129 data messages are **80 bytes**
each (16-byte header, 48 bytes of ciphertext, 16-byte tag). The D2 reason
for excluding the trim ("129 transmissions × the 100 ms wait", D2 §8) no
longer applies. A 128-segment GSO send needs `gso_size ≤ 511` (section 6).

### 2.3 Padding arms: route MTU, `SIOCSIFMTU`, `IFLA_MTU`

`PACKET_CB(skb)->mtu = skb_valid_dst(skb) ? dst_mtu(skb_dst(skb)) : dev->mtu`
(device.c:173). `dst_mtu` → `ipv4_mtu` → `ip_dst_mtu_maybe_forward(dst,
false)` (`route.c:1366-1369`, `ip.h:469-495`): `rt_pmtu` if set and
unexpired (`:481-487`), else **`RTAX_MTU` of the route** (`:490-492`), else
`dev->mtu` (`:494`).

- **Route MTU below the device MTU** (the `len > mtu` arm, `.padOverMtu`
  true). A route `… dev wg0 mtu 1300` gives `dst_mtu = 1300`. The sender
  must still build a 1420-byte packet: with **`IP_PMTUDISC_PROBE`**,
  `ip_sk_use_pmtu` is false (`ip.h:457-460`), so `cork->fragsize = dev->mtu
  = 1420` (`ip_output.c:1307-1308`) and `ip_skb_dst_mtu = dev->mtu`
  (`ip.h:511-525`, the `:523` branch), so `__ip_finish_output` does not
  fragment (`:311`). **DF is set** for `PROBE` (`:1441-1442`) and
  `ignore_df` is false (`ip_sk_ignore_df`: `pmtudisc < DO || == OMIT`,
  `ip.h:462-467`; `PROBE = 3`), so the unconnected sender's **id is 0**
  (`ip.h:583-584`); from `SEND2_FD` it is the next `inet_id` (v2, m7).
  `wg_xmit` then sees `len = 1420 > mtu = 1300`: `last_unit = 1420 % 1300 =
  120`, `padded_size = min(1300, 128) = 128`, padding 8; ciphertext 1420 + 8
  + 32. **The clamp is not taken here** (`128 < 1300`; v2, M8): with route
  MTU 1300 the clamp needs inner lengths 1297-1300 (IPv4 payloads
  1269-1272), and D2 already covers both of its outcomes at the device MTU,
  so no such class is needed. IPv6 is symmetric (`ip6_output.c:1401-1405`,
  `IPV6_PMTUDISC_PROBE`); its `dst_mtu` is `ip6_mtu` (`ipv6/route.c:3272`)
  → `ip6_dst_mtu_maybe_forward` (`ip6_route.h:269-281`): `RTAX_MTU` if set,
  else **`idev->cnf.mtu6`**, which `NETDEV_CHANGEMTU` copies from `dev->mtu`
  (`addrconf.c:3697-3700`; v2, m3). A route with `mtu lock` is not needed:
  `RTAX_MTU` is read regardless (`ip.h:490`); `lock` only guards against
  PMTU updates.
- **`SIOCSIFMTU`** → `dev_set_mtu_ext` → `dev_validate_mtu`
  (`dev.c:9085-9122`, `:9061-9075`) → `__dev_set_mtu` writes `dev->mtu`
  (`:9048-9058`; wg has no `ndo_change_mtu`) → `NETDEV_CHANGEMTU`. wg never
  sets `min_mtu` (device.c:274-307 sets only `mtu` and `max_mtu`;
  `alloc_netdev_mqs` sets none), so **`dev_validate_mtu` accepts 0** (`:9065`
  is `new_mtu < 0 || new_mtu < dev->min_mtu`). Consequences:
  - `< 1280`: `addrconf_notify` runs `addrconf_ifdown(dev, 1)`
    (`addrconf.c:3691-3695`): wg0's `inet6_dev`, addresses and IPv6 routes
    are gone until the MTU is raised again (`:3704-3711`, `ipv6_add_dev`).
  - `< 68`: `inetdev_event` runs `inetdev_destroy` (`devinet.c:1637-1643`):
    wg0's `in_device`, IPv4 address and routes are gone; a later valid MTU
    re-creates the `in_device` empty (`:1586-1588`).
  - **The fixture must follow** (v2, M5). `route_into_wg0`
    (`task/e-b:harness/guest.c:486-527`, run at every `wg_up`, `:1037`) adds
    `10.255.254.1/32` and `fd00:ffff::1/128` by `RTM_NEWADDR` with
    `NLM_F_EXCL` and the default routes, and `rtnl_request` (`:469-478`)
    fails the trace on any errno other than the expected one: `0` on the
    first up, `-EEXIST` for IPv4 afterwards (the address survives a down),
    `0` for IPv6. Below 1280 the IPv6 add is **`-EINVAL`**
    (`inet6_addr_add` → `addrconf_add_dev` → `ipv6_find_idev` →
    `ipv6_add_dev`, `addrconf.c:381-382`); below 68 the IPv4 add is
    `-ENOBUFS` while the `in_device` is absent (`devinet.c:888`) and **`0`,
    not `-EEXIST`**, once a valid MTU has re-created it empty. So the
    fixture takes wg0's MTU (`SIOCGIFMTU` on `SEND_FD`, before the window)
    and expects, per family, the kernel's refusal below the family's floor
    (the exact errnos of the address and route adds are fixed by probe P-B,
    section 12, and any other value fails the trace: the refusal is itself a
    check of the teardown the mirror's `inet4Dev`/`inet6Dev` state records).
    Classes that lower the MTU are **terminal for the affected family**;
    classes that raise it back above 1280 stay terminal too (the addresses
    and routes are not re-added inside a trace).
  - With MTU 0 and a keepalive (`PACKET_CB(skb)->mtu = skb->dev->mtu`,
    send.c:232), `calculate_skb_padding` takes the **`!mtu` arm**
    (send.c:145-146, `.padNoMtu`, `Decision.lean:943` on `task/census`,
    `:1026` on `main`), and a `wg_down` / `wg_up` afterwards takes **both
    `if (dev_v4)` and `if (dev_v6)` false** in `wg_open` (device.c:39, 47).
    `dev_validate_mtu` accepts 0 (`:9065`; wg sets no `min_mtu`,
    device.c:290-297) and the keepalive's 32-byte message pads to 0 bytes
    either way (`ALIGN(32, 16) − 32`), so the arm is observable only by A2.
    Whether this class exists is decision 13.6; v1's "ends with the
    keepalive" (section 6) and "a `wg_down`/`wg_up` afterwards" (here) were
    inconsistent, and the class, if built, is `wg_set_mtu 0`, the
    keepalive, `wg_down`, `wg_up` (with the MTU-aware fixture expecting the
    refusals above), then `wg_observe`.
  - A lowering that keeps IPv6 (say 1300, DO sender) changes
    `cork->fragsize`, `MAX_XMIT_PAYLOAD*`, the padding and the `-EMSGSIZE`
    boundary for both families; 1000 would also drop IPv6 (above).
- **`IFLA_MTU` at creation** (L's `wg_create`, `task/e-b:harness/guest.c:976-
  986`): `rtnl_create_link` validates and sets `dev->mtu` before
  `register_netdevice` (`rtnetlink.c:3517-3526`); `NETDEV_REGISTER` creates
  the `inet6_dev` only if `dev->mtu >= IPV6_MIN_MTU` (`addrconf.c:3683-3688`,
  and `ipv6_add_dev` refuses below, `:381-382`), while `inetdev_init` always
  runs (`devinet.c:1576-1580`). So a device created with MTU 1279 enters
  `wg_open` with `dev_v6 == NULL`: the false arm of `.openHasInet6`
  (`Device.lean:45`, constant true today). Its first `wg_up`'s
  `route_into_wg0` then meets `-EINVAL` on the IPv6 add (above), which the
  MTU-aware fixture expects; the trace continues IPv4-only. This is the
  recommended route to `.openHasInet6` false (decision 13.6).

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
  `IPV6_MULTICAST_IF`; the `ff00::/8 dev wg0` route exists from the
  fixture's IPv6 address add, `addrconf_add_dev`, `addrconf.c:2579-2581`):
  hop limit `IPV6_DEFAULT_MCASTHOPS = 1` (`include/net/ipv6.h:53`, `:905`;
  `af_inet6.c:223`). IPv4 `224.0.0.1` with `mc_ttl = 1` (`ip_output.c:
  1452-1453`): the fixture's sender is an **AF_INET6** socket (`guest.c:
  821-826`), so its IPv4 side comes from `inet6_create` (`af_inet6.c:
  237-238`, `MC_LOOP` and `mc_ttl = 1`), not `af_inet.c:364` (v2, M3). The
  source is wg0's global address (no link-local exists; with `fe80::1`
  added, source selection prefers it for a link-local-scope destination —
  the fixture decides which, and the bytes check it). The **loopback copy**
  is decided by a **membership set per family** (v2, M3):
  - IPv4: `__mkroute_output` sets `RTCF_LOCAL` on a multicast route only when
    `ip_check_mc_rcu` finds the `in_device` a member (`route.c:2581-2587`),
    and only `RTCF_LOCAL` selects `dst.output = ip_mc_output` (`:2647-2652`;
    the `CONFIG_IP_MROUTE` branch is not built). `ip_mc_output` then clones
    to `dev_loopback_xmit` when `sk_mc_loop` (`ip_output.c:382-400`). The
    `in_device` joins **only `224.0.0.1`** (`ip_mc_up`, `igmp.c:1796`). So
    `224.0.0.1` loops and `224.0.0.2` or `239.1.1.1` does not. **D3's
    `xmitMulticastLoop` loops for any `224/4`** (`task/d3-int:Leanux/
    Env.lean:90-93`): latent, since D3's corpus only ever sent to
    `224.0.0.1` (41 operations), and fail-noisy, since a send to `224.0.0.2`
    would expect a NET_RX section Linux does not produce. Corrected here
    with the set `{224.0.0.1}` (decision 13.7).
  - IPv6: `ip6_finish_output2` loops only when wg0 is a member
    (`ipv6_chk_mcast_addr`, `ip6_output.c:86-99`). `ipv6_add_dev` joins
    `ff01::1` and `ff02::1` (`addrconf.c:468`, `:471`); `ff02::2` needs
    forwarding and `IFF_MULTICAST` (`:474-475`), which wg0 lacks; and
    **wg0 is `IFF_NOARP`** (device.c:290), so `addrconf_join_solict` returns
    before joining any solicited-node group (`addrconf.c:2246-2254`). The
    set is **exactly `{ff01::1, ff02::1}`** (v1's "plus the solicited-node
    group of each address" was wrong). So `ff02::1` loops, `ff02::1234` does
    not. D3's `unsupported` for IPv6 multicast (`Env.lean:93`) becomes this
    set.
  - `sk_mc_loop` dispatches on `sk_family` (`sock.c:761-777`): for the
    AF_INET6 sender it reads **`MC6_LOOP`** even for a v4-mapped send, so the
    no-loop control sets `IPV6_MULTICAST_LOOP = 0` for both families, and
    `IP_MULTICAST_LOOP = 0` on this sender does not change the loop (a cheap
    negative control, `w4_mcast_noloop_v4opt`, section 6). The
    `dev_recursion_level()` guard (`:763`) is 0 in system-call context.
  - Nothing receives the copy (no socket on `SEND_PORT`), and multicast
    destinations draw no ICMP error.

### 2.5 Transmit fragmentation (`IP_PMTUDISC_DONT`)

`ip_sk_ignore_df` is true for `DONT` and `WANT` (`ip.h:462-467`), so
`maxnonfragsize = IP_MAX_MTU` (`ip_output.c:999`) and a 2000-byte payload is
accepted. `__ip_append_data` builds the datagram as a head skb plus
`frag_list` members (`__ip_make_skb`, `:1412-1429`); since
`length + fragheaderlen > mtu`, `csummode` stays `CHECKSUM_NONE` (`:1011-
1016`) and `udp_send_skb` computes the UDP checksum in software over the
whole datagram: **`csum = udp_csum(skb)` then `csum_tcpudp_magic`**
(`udp.c:1030-1033`; `udp_csum` walks the `frag_list`). The `frag_list`
branch of `udp4_hwcsum` (`:913-930`) is the `CHECKSUM_PARTIAL` path and is
not taken (v2, m2). DF is clear (`:1440-1445`) and the ident is drawn
(`:1465` → `ip.h:585-587` → `__ip_select_ident`, or from `inet_id` for the
connected sender, `ip.h:568-581`; section 3).
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
`1 + get_random_u32_below(U32_MAX)` (`random.h:98-103`). **The record is
kind 104, not 110** (v2, C1): `U32_MAX` is a constant, so
`get_random_u32_below` takes its inline path (`random.h:60-85`), whose
`ceil > 2^16` arm calls the exported `get_random_u32()` (`:83`), which the
patch records as `100 + sizeof(u32)` (`kernel/patches/choice-stream.patch`,
`get_random_##type`, hunk at `random.c:536-549`); kind 110 is written only
by `__get_random_u32_below` (patch hunk at `random.c:565-590`), which a
constant ceil never reaches. With `ceil = 2^32 − 1`, `-ceil % ceil = 1`, so
the inline path rejects exactly a raw draw `r = 0` and redraws (another
kind-104 record at the same site), and returns `(ceil · r) >> 32 = r − 1`;
hence **`id = r`, the first non-zero record**. The consumer frame is the
inlined `__ipv6_select_ident` body, **`output_core.c:18`** (DWARF chain on
the built kernel: `random.h:87 → :102 → output_core.c:18 → :53`;
`__ipv6_select_ident` is absent from `System.map`), by the same rule that
names `.ipIdentReserve` route.c:482 (`harness/steer.py:26-28`,
`check.py:285-320`: the first frame outside the random/clock helpers).

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
case is probe P-A, section 12).

**The xmit path is the same only once the sender's `sk_sndbuf` is raised**
(v2, M1). An inject's skb is orphaned inline, at `loopback_xmit`'s
`skb_orphan` (`loopback.c:79`), so its `sock_wfree` charge is released
inside the send. A send **into wg0** keeps its charge: `wg_xmit` only drops
the dst (device.c:189-204), `encrypt_packet` reuses the skb, and the
ciphertext is orphaned only when the **tx worker** hands it to `lo` — after
the system call. The default `sk_sndbuf` is `sysctl_wmem_default =
SK_WMEM_MAX = 212992` (`sock.c:286`, `sock.h:2867-2869`), about 277 small
skbs (truesize 768); the next `sock_alloc_send_pskb` fails with `-EAGAIN`
for a non-blocking send (`sock.c:2918-2923`), io_uring's `io_send` returns
it under `IO_URING_F_NONBLOCK` (`io_uring/net.c:578-579`), and
`io_queue_async` (`io_uring.c:1913-1929`) poll-arms the request on
`POLLOUT` or punts it to io-wq — either way the send completes **after the
window**, outside this argument. So **`SO_SNDBUFFORCE` (8 MiB, giving
`sk_sndbuf = 16 MiB`, `sock.c:1328-1333`) is set on `SEND_FD` and
`SEND2_FD`** before the window; 1025 full-size xmits charge about 2.4 MiB.
With that, each send's `wg_xmit` runs inline (`__dev_queue_xmit`,
`dev.c:4527-4559`) and `create_data` only queues work (`queue_work_on`,
`queueing.h:176`). `wg_batch` reports the CQEs present when
`io_uring_enter` returns as part of its result (section 5.5), so a deferred
item fails on the result rather than as a later record mismatch.

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
  `RxData.lean:107,122`) therefore stay valid without a wider search for
  **control flow** (section 5.3). The **operand** ambiguity of the (c')
  placement (the poll before `wg_peer_put`, one peer reference higher;
  `task/d3-int:docs/2026-10-06-contended-host.md` §2) is a separate matter
  that **scales with the item count** (v2, C2): `Env.napiIrqExit`
  (`task/d3-int:Leanux/Env.lean:696-703`) counts every inline poll as one
  open choice, and `check.py` enumerates the `2^count` vectors only for
  `count ≤ NAPI_PLACEMENTS_MAX = 3` (`evaluator/check.py:811-845`), and only
  on an operand mismatch (`:924`). An n-item batch has n inline polls, so one
  (c') among them is unrecoverable for n > 3. The contended-host note saw
  (c') in three traces of a 1369-trace check, so a 1025-item trace would
  fail with high probability and an 8-item trace in about 2% of runs.
  Decision 13.2 gives the options.
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
  `napi_schedule`. But the poll also counts **`DEAD`** entries toward
  `work_done` (receive.c:456-459 `goto next`, `:483-484`; v2, M4), and the
  `-EPIPE` arm of `consume_data` (`:526-529`) marks an entry `DEAD` **in
  the softirq**, any number of times per `net_rx_action`. So
  `NAPI_POLL_WEIGHT = 64` (`netdevice.h:2632`, peer.c:57) **is reachable on
  one CPU**: section 10. `netdev_budget = 300` and the 2-jiffy limit
  (`hotdata.c:13-15`, `dev.c:7097-7101`) stay unreachable (at most 128
  segments per datagram).

## 3. Hidden inputs

| Input | Site | Status | Used by |
|---|---|---|---|
| GSO segment ids | none: `id = 0` for the DO, unconnected sender (`ip.h:583-584`), then `id++` (`af_inet.c:1453`) | computed | W4 GSO bytes |
| GSO segment UDP checksums | none: software (`udp_offload.c:439-441`) | computed | W4 GSO bytes |
| Connected sender's txhash | `__ip4_datagram_connect` → `sk_set_txhash` → `net_tx_rndhash` → `get_random_u32()` (`datagram.c:75`, `sock.h:2088-2099`), **before** the seed; a v4-mapped `connect()` on the dual-stack sender takes this path (`ipv6/datagram.c:157-161`, `:189-199`, then `goto out`), a native IPv6 `connect()` draws only this (`:268`) | **new `HiddenSite` `.txHash`** (kind 104, 4 bytes, role `.cut`: `sk_txhash` is not observed) at consumer frame **`include/net/sock.h:2092`** (DWARF chain on the built kernel: `sock.h:2092 → :2098 → datagram.c:75`; one site serves both families); consumed by `wg_connect` first (v2, M2) | W4 fragmentation |
| IPv4 fragment ident, **connected** sender | `__ip4_datagram_connect`, `datagram.c:76`: `atomic_set(&inet->inet_id, get_random_u16())` | **new `HiddenSite` `.inetIdSeed`** (2 bytes, mirror) at the existing generic hook (kind 102); consumed by the mirror's `wg_connect` op into **socket state `inet_id`** in Env; every datagram from `SEND2_FD`, GSO included, then takes `id = atomic_add_return(1, &inet_id)` (`ip.h:575-581`): the first id is **seed + 1**, the next seed + 2, … (v2, M2) | W4 fragmentation, any `SEND2_FD` send |
| IPv4 fragment ident, unconnected `DONT` sender | `.ipIdentReserve` records `delta` only (`route.c:481-482`); the bucket counter is boot-random (`:3720`) | **not reconstructible**: stays `.cut`; the class is `unsupported` unless option K1 | — |
| IPv6 fragment id | `ipv6_select_ident` → `get_random_u32_above(0)` (`output_core.c:18`): the inline `get_random_u32_below(U32_MAX)` calls `get_random_u32()`, **kind 104**, once per attempt (2.5; v2, C1) | **new `HiddenSite` `.ipv6FragId`** (kind 104, 4 bytes, mirror) at consumer frame **`net/ipv6/output_core.c:18`**: **id = the first non-zero record**; a zero record is followed by another at the same site (the mirror consumes until non-zero, and a zero record followed by anything else is a hidden mismatch) | W4 IPv6 fragmentation |
| `wg_xmit`'s `mtu` | route/device, fixture facts | environment (`Env.xmitPackets`), checked by padding bytes | W4 |
| wg0's IPv6 presence | `dev->mtu ≥ 1280` at registration / after `CHANGEMTU` | mirror state `Device.inet6Dev` | W4 `wg_open` |
| Scheduling: encrypt/tx/decrypt yields | kind 302 resched records (`.reschedEncrypt/.reschedTx/.reschedDecrypt`, `Defs.lean`) | existing, now per item | W7 |
| Scheduling: NAPI placement | NET_RX section records (kinds 300/301) | existing; pinned per item for control flow (2.8); the (c') operand choice is decision 13.2 | W7 |
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
  "pinned per item" argument of 2.8 into a checked fact. Not recommended
  (13.2); the W7 corpus's `napi_orders.py` extension (section 8) reports
  any placement the argument does not cover.
- **K3** (v2, C2 option iii). Record the (c') placement itself: a choice
  record in `wg_queue_enqueue_per_peer_rx` after `wg_peer_put`
  (queueing.h:201), so a nested NET_RX section's position relative to it
  tells before-put from after-put. A new hook against the user's
  "generic capture points, zero new hooks" preference; option (ii) of 13.2
  keeps the check without it.
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
  `.padOverMtu`, `.openHasInet6` gain their second outcome; `.padClamped`
  already has both (D2; v2, M8); `.padNoMtu` and `.openHasInet` only under
  decision 13.6. `wg_prev_queue_dequeue.*`'s tests are pointer compares
  (queueing.c:84, 85, 91, 96, 101), declared in the `d` form without a
  comparison, as `.prevQueuePeeked` is (so `operand_agreement` skips their
  operands, `check.py:742-747`); `queueing.c` joins `correspondence/
  kcov.json` `files` and `wg_prev_queue_dequeue` its `functions` (v2, M9;
  `operand_exclusions` entries are only needed if the check is extended to
  claim every recorded compare, which it does not do today).
- New `HiddenSite`s `.txHash` (`.cut`), `.inetIdSeed`, `.ipv6FragId`
  (section 3), all at the existing random hook; new sites follow E's
  precedent (`.cookieNonce`).

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

**`Leanux/Env/IpStack.lean`** (new, stream T; `Env.lean` keeps only the
hooks that call it, section 12):
- `xmitPackets (family addr : Nat) (payload : List UInt8) (opts : XmitOpts) :
  M (List (List Packet) × Nat)` replaces `xmitPacket`: the outer list is the
  `wg_xmit` calls of one `sendto`/`sendmsg` (one, or two for a fragmented
  datagram), the inner list the packets of one call (the GSO segments, or
  one packet), and the `mtu` `wg_xmit` computes. `XmitOpts` carries
  `gsoSize`, `pmtudisc ∈ {DO, DONT, PROBE}`, `connected`, and the fixture's
  route MTU for the destination (from the trace's `net_fixture`, section 6).
  It computes:
  - GSO: segment i's IPv4 header (`id = base + i`, where `base` is 0 for
    `SEND_FD` and the next `inet_id` for `SEND2_FD`; `tot_len`, header
    checksum), UDP header (`len`, the complete checksum, `CSUM_MANGLED_0`
    for 0), payload slice; `csum := none`. The stack's `-EMSGSIZE`/`-EINVAL`
    conditions (2.1) are the operation's result with no `wg_xmit`.
  - Fragmentation (`DONT`, length > route MTU): the datagram's UDP checksum
    over the whole payload (`udp_csum`, 2.5); fragment 1 (`MF`, 1400 payload
    bytes on IPv4), fragment 2 (offset 175); the id from `inet_id`
    (connected) — the unconnected case is `unsupported "an unconnected
    sender's fragment ident (route.c:488 over a boot-random bucket)"`. IPv6:
    the Fragment header with `.ipv6FragId`.
  - `PROBE` with a route MTU: a full-size packet with `mtu` = route MTU, DF
    set, id 0 (`SEND_FD`) or the next `inet_id` (`SEND2_FD`).
  - Multicast/link-local: source, TTL/hop limit per 2.4; `xmitBytesUnknown`
    shrinks to destinations the fixture does not determine.
- **Sender socket state** (v2, M2): `Sender.inetId : Option Nat` for
  `SEND2_FD`, set by `wg_connect` from `.inetIdSeed` (after consuming
  `.txHash`), incremented by every datagram it sends; `none` means
  unconnected (a send then takes the `SEND_FD` rules).
- **Multicast membership sets** (v2, M3): `xmitMulticastLoop` (from d3-int)
  loops iff the destination is in the family's set, `{224.0.0.1}` for IPv4
  and `{ff01::1, ff02::1}` for IPv6 (2.4), and `sk_mc_loop` is the sender's
  `MC6_LOOP` for both families (`XmitOpts.multicastLoop`, from
  `IPV6_MULTICAST_LOOP`). The IPv4 set replaces D3's "any `224/4`".
- `MAX_XMIT_PAYLOAD*` become functions of `Device.mtu` and the route MTU.
- `fixtureSend`'s cut list is unchanged (a connected sender draws no
  `ip_idents_reserve`; the cut is lax).

**Keepalives queued by `wg_set` and `wg_up`** (v2, M6; `Env.lean`, a hook
shared with stream B). Today `Env.runSendWorkers` → `requireNoCryptWork`
(`task/d3-int:Leanux/Env.lean:318-322`, `:338-339`; `Syscalls.lean:139-141`)
makes a keepalive sent from `wg_set persistent_keepalive` or `wg_up` under a
session `unsupported` ("crypt work queued in a system call"), which the MTU
classes of section 6 need. [AGENT] The `wg_set`/`wg_up` return path takes
`afterXmit`'s shape (`:355-362`): the crypt workers run during the guest's
`QUEUE_WAIT_US` wait, ordered by their section starts, with the
crypt-plus-handshake rule relaxed to "ordered by section starts" as in 5.5.
This lifts an existing `unsupported` without weakening any check (the
sections and resched records are the evidence, as for `wg_xmit`). The
alternative, driving the keepalive from the persistent-keepalive timer
through `wg_advance` (D3's `afterAdvance`), covers fewer paths and is not
taken.

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
  budget arm (`.rxPollBudgetDone`, `RxData.lean:311`, a real decision
  today) is handled by the environment per decision 13.5: either
  `net_rx_action`'s repoll (section 10) or an explicit `unsupported` at the
  poll site in `napiSoftirq`. Today a budget-exhausted poll would leave
  `napiScheduled` set and trip `runDecryptWorker`'s `invariant`
  (`task/d3-int:Leanux/Env.lean:710-711`): fail-noisy, but as a mirror
  error, not a domain exclusion.
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
| A unit resumes above the mirror's stack with work pending | a resched record in a nested unit while an outer open worker has queued work | **fail-closed** (5.4, generic) |
| The (c') placement of an inline poll (before `wg_peer_put`) | no record; only the poll's peer-refcount operands differ | a per-poll choice, n of them per n-item batch; enumerated today only for ≤ 3 (2.8, C2): **decision 13.2** |

`evaluator/napi_orders.py` is extended to count, per trace, the number of
polls per decrypt-worker run, the items per poll, and the (a)/(b/c) split;
the W7 corpus must show polls with the `peeked` arm taken and at least one
two-item poll if it occurs, else the mutant that ignores the peeked slot
(W7-M3) is reported inconclusive, as D2 did for D2-M12.

### 5.4 The commuting assumption

`runWorker` (`Env.lean:200-217`) lets a worker that switched away finish in
the mirror at once, leaving its section stop pending, because "each rest is
a worker's final empty ring or queue poll". With several items that is
false **whenever a nested unit yields while an outer open worker still has
queued items** (v2, M7; v1 named only one instance). The shape: `condResched`
in worker O (say the encrypt worker, at send.c:306-307) runs the unit U
whose section start follows the resched record (say the tx worker) nested
inside O's `runWorker`; U yields in turn (send.c:282-283, tick-driven; D1
saw one tx yield in 1334 traces); Linux may now resume O, which crypts more
items before U resumes, while the mirror's U, already running to completion
inside O's call, sees O's old queue. Every pairing of units with a
`cond_resched` is the same (`Worker.resched?`, `Defs.lean:356-360`:
receive, encrypt, tx, decrypt); the decrypt worker vs. ksoftirqd is exempt
only because `net_rx_action` does not yield mid-poll, so a poll run as a
unit never has a suspended outer with queued work.

- **Phase 1 (required, generic):** `runWorker` keeps the mirror's stack of
  open workers; at a resched record in unit U, after the runnable section
  starts are run, if U is nested and **any outer open worker on the stack
  has queued items** (the encrypt ring for `.encryptWorker`; `txWorkQueue`
  or a `CRYPTED` tx head for `.txWorker`; the decrypt ring for
  `.decryptWorker`), `condResched` returns `unsupported "a worker yielded
  below an open worker with queued work (the mirror's stack order)"`. The
  test does not name the unit kinds. Its control: a synthetic record stream
  with a `.reschedTx` inside an open encrypt section with items left must
  be `unsupported`, and the same stream with the encrypt ring empty must
  pass.
- **P-C's measure** (v2, M7): on the D1/D2 corpora every queue holds one
  item, so the detector's count there is zero by construction (vacuous).
  The offline measure is the **nesting proxy**: the number of resched
  records inside a nested unit's section (a yield whose enclosing block is
  itself inside another worker's section), per trace and per unit pair,
  from the existing check runs' records. That is the rate at which the
  scheduling precondition occurs; with multi-item queues each such yield is
  a phase-1 rejection whenever the outer has work.
- **Phase 2 (decided on the W7 corpus):** the four units become step
  functions (`encryptStep`, `txStep`, `decryptStep`, `rxPollStep`, each one
  loop iteration) and the environment interleaves steps by the records. The
  mirror code per step is the C's loop body unchanged; only the loop driver
  moves to the environment. This is the thin layer's natural shape and is
  the recommendation if phase 1's counter on the W7 corpus exceeds a few
  percent of bulk traces.

### 5.5 The batch operation

`wg_batch` (generalizing E-B's `wg_flood`, `task/e-b:harness/guest.c:700-
775`; wire opcode **allocated by the coordinator**, `OP_BATCH` below): a
list of items, each `inject {family, port, message}` or `xmit {packet,
payload, opts}`, on `SEND_FD` (or `SEND2_FD` for a connected xmit), prepared
as SQEs before the window (`flood_prep`'s pattern), one `io_uring_enter`,
then a wait. **Both senders carry `SO_SNDBUFFORCE` (8 MiB)** set before the
window (2.7; v2, M1). The operation's result includes the **CQEs present
when `io_uring_enter` returns**: their count and each `res`; the mirror
expects `submit` entries with `res` = the item's length (an inject's `-EPIPE`
or a stack `-EMSGSIZE` is a per-item result too). `wg_flood` (`:769`) does
not read its CQEs today; `wg_batch` subsumes it and the rule comes with it.
In the environment (`Leanux/Env/Batch.lean`, stream B, `Env.batch`): for
each item in order, `fixtureSend` and `runWorker .netRx (wgReceive …)` for
an inject (plus any `-EPIPE` poll), or `wgXmit` for an xmit — no worker
runs between items (2.7); after the loop, the deferred units run as the
records order them: `runDecryptWorker` and `runCryptWorkers` (which already
follow section starts), with `afterXmit`'s rule that a call queuing both
crypt work and a handshake is `unsupported` (`task/d3-int:Leanux/
Env.lean:355-362`) relaxed to "ordered by their section starts". The
guest's wait after a batch is a trace parameter (`wait_ms`), whose default
is an **output of P-A** (v2, m5) rather than the 100 ms assumed in v1; a
worker outliving it shows as missing section records (the `opened` count
check from D1).

## 6. Harness

- **Ops** (`harness/trace.py` FIELDS, `harness/wg.py`, `harness/guest.c`):
  - `wg_xmit` gains optional `gso_size` (cmsg `UDP_SEGMENT`), `pmtudisc`
    (`do` default, `dont`, `probe`; set per op with `IP_MTU_DISCOVER` /
    `IPV6_MTU_DISCOVER` before the send and restored after), `connected`
    (a second dual-stack sender `SEND2_FD`, bound to `SENDER_PORT + 1`,
    `connect()`ed **inside the window** so `.txHash` then `.inetIdSeed` are
    recorded, then `send()`), `multicast_loop` (**`IPV6_MULTICAST_LOOP`**,
    the bit `sk_mc_loop` reads on this AF_INET6 sender for both families,
    2.4), and a payload up to 65507 bytes (`MAX_PAYLOAD` raised;
    `wg.py:357-362`'s MTU bound becomes a per-`pmtudisc` rule).
  - `wg_set_mtu {mtu}`: `SIOCSIFMTU` via `SEND_FD`'s ioctl (as `wg_up` uses
    `SIOCSIFFLAGS`, `guest.c:926-931`).
  - `wg_create` gains `mtu` (`IFLA_MTU`; `task/l-m` has no `mtu` field yet).
  - **`route_into_wg0` becomes MTU-aware** (2.3; v2, M5): it reads wg0's MTU
    (`SIOCGIFMTU`) and expects, per family, the kernel's refusal below the
    family's floor (IPv6 add `-EINVAL` below 1280; IPv4 add `-ENOBUFS` below
    68, or `0` instead of `-EEXIST` once a valid MTU re-created the empty
    `in_device`; the route adds' errnos from P-B), failing the trace on any
    other value as today.
  - `net_fixture` (already an optional trace field, `trace.py:73`) gains
    `routes: [{dst, mtu}]`, `link_local: "fe80::1/64"`, `allowed_ips` for the
    peer config is unchanged (the generator adds `224.0.0.0/4`, `ff00::/8`,
    `fe80::/64` where a class needs them).
  - `wg_batch {items: [...], wait_ms}`: section 5.5; its result carries the
    CQEs. `MAX_PAYLOAD` (32768, `guest.c:32`) and `line` (`:75`) grow to hold
    1025 messages; `SO_RCVBUFFORCE` (8 MiB) on both listeners and `SEND_FD`,
    since the default `rmem_default` (`sock.c:287`, 212992) holds about 270
    small datagrams and the bulk tiers deliver up to 1025; **`SO_SNDBUFFORCE`
    (8 MiB) on `SEND_FD` and `SEND2_FD`** (2.7; v2, M1).
  - **Wire opcodes** for `wg_set_mtu`, `wg_batch` and `wg_connect` (if it is
    its own op rather than a `wg_xmit` flag) are placeholders `OP_SET_MTU`,
    `OP_BATCH`, `OP_CONNECT` here; the coordinator allocates them at the
    interface commit (`trace.py` `OPCODES`, 15-17 are L's and 18 is
    `wg_flood`).
  - `wg_observe` for bulk: the listener drain (`guest.c:563-600`) reports
    every datagram as today; for the full-ring tier the generator uses
    keepalive data messages (32 bytes, 48 as ciphertext) so the observe line
    stays under a few hundred KiB; the message counters (bytes 8-16) show
    which item was dropped.
  - KCOV capacity: `CAPACITY` is 64K words on `main` (`guest.c:31`) and
    already 1M words on `task/e-b` (`guest.c:37`, raised for the flood). A
    1025-item batch at roughly 300 PCs per message fits the PC child, but
    the comparisons child (four words per record, `trace.py:52`) may not. A
    per-trace `kcov_capacity` replaces the constant (both the task and the
    remote area; the VM has 256 MiB); `validate_coverage` already fails a
    full buffer. **Its bulk value is an output of P-A** (v2, m5), which
    measures the record volume per item in both children; v1's 4M words
    (32 MiB) is the upper bound P-A starts from, not the answer.
- **`harness/noise.py`:** GSO segment and fragment builders (headers,
  checksums, ids) anchored to the mirror's `Env.xmitPackets` by `#guard`
  vectors and to Linux by the A1 bytes; batches of data messages under a
  session with counter lists.
- **Generator** (`scripts/wg-w47-corpus.py`, classes; the corpus
  `corpus/wireguard/w4_*.json`, `w7_*.json`):
  - `w4_gso_{4,6}_{n}`: after a session, one GSO xmit; the (n, `gso_size`)
    pairs are **constrained by the 65507-byte payload bound** (v2, m4):
    n ∈ {2, 3} with `gso_size` ∈ {8, 1392 (IPv4) or 1372 (IPv6), a
    non-divisor so the last segment is short}, and n = 128 with `gso_size`
    ∈ {8, 511} only (128 segments need `gso_size ≤ 511`; at `gso_size`
    1392 the largest datagram gives 48 segments, 47 full and one of 83
    bytes, so a `w4_gso_4_48` class covers the largest-segment end). Expect
    n ciphertexts.
  - `w4_gso_trim`: no session; two GSO xmits of 128 (`gso_size` 8), a third
    of 1; expect `tx_dropped = 128`; then the offline response flushes 129
    80-byte messages.
  - `w4_route_mtu_probe_{4,6}`: route MTU 1300, `PROBE`, payload 1392/1372;
    **the `len > mtu` arm** (`.padOverMtu` true, padding 8). The clamp is
    not taken here and needs no class (2.3; v2, M8).
  - `w4_set_mtu_{1300,1279}`: `wg_set_mtu` then xmits and a keepalive
    (`wg_set` with `persistent_keepalive`, under a session: the keepalive
    rule of section 4), then `wg_down`/`wg_up` with the MTU-aware fixture:
    `_1300` keeps both families and moves the padding and `-EMSGSIZE`
    boundaries; `_1279` drops IPv6 (its later IPv6 xmits are not in the
    class) and reaches `.openHasInet6` false at the `wg_up`. Terminal.
    `w4_set_mtu_0` (the `!mtu` arm and `.openHasInet` false) exists only
    under decision 13.6: `wg_set_mtu 0`, the keepalive, `wg_down`, `wg_up`,
    `wg_observe`.
  - `w4_create_mtu_1279`: L's `wg_create` with `IFLA_MTU`, `wg_up` (IPv6
    add `-EINVAL` expected), IPv4 xmits.
  - `w4_frag_{4,6}_connected`: `connected`, `DONT`, payload 2000; expect two
    ciphertexts with id = seed + 1 (IPv4) or the first non-zero kind-104
    record (IPv6). `w4_frag_4_unconnected` is a **domain control**: expected
    `unsupported`. `w4_gso_4_connected` (a GSO send from `SEND2_FD`): ids
    seed + 1, seed + 2, … (M2's "including GSO").
  - `w4_mcast_{4,6}`, `w4_mcast_{4,6}_nomember` (`224.0.0.2`, `ff02::1234`:
    no NET_RX section; the IPv4 one is the trace that rejects D3's "any
    `224/4`"), `w4_mcast_noloop` (`IPV6_MULTICAST_LOOP = 0`, both families),
    `w4_mcast_noloop_v4opt` (`IP_MULTICAST_LOOP = 0` on the AF_INET6 sender:
    the copy still loops), `w4_linklocal_6`: 2.4.
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
  the trim's iteration count; `wg_prev_queue_dequeue`'s arms (control flow
  only: pointer compares); `.prevQueuePeeked` true; `.encChecksumPartial`
  false; `.padOverMtu` true.
- **Operation results:** `wg_batch`'s CQE count and `res` per item (5.5);
  the fixture's expected refusals at `wg_up` after an MTU change (2.3).
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
- **W4-M8** `last_unit %= mtu` dropped — same trace: without the modulo,
  `min(1300, ALIGN(1420, 16) = 1424) = 1300` and `1300 − 1420` is 0 in the
  mirror's `Nat` (Linux's unsigned wrap would be caught by `skb_put`), so
  the mutant pads 0 where Linux pads 8: bytes (v2, M8 corrects v1's
  "padding 8 vs clamp").
- **W4-M9** keepalive padded with `Device.mtu` ignored (`!mtu` arm) —
  `w4_set_mtu_0` A2 operands (bytes equal: honest); **only under 13.6**.
- **W4-M10** `wg_open`'s `dev_v6` constant true — `w4_create_mtu_1279` A2.
- **W4-M11** fragment 2 given a UDP header / wrong offset — `w4_frag_*`
  bytes.
- **W4-M12** fragment ident not from `inet_id` (0, or seed instead of
  seed + 1) — bytes; the **control** `w4_frag_4_unconnected` must be
  `unsupported`, not a pass.
- **W4-M13** multicast loop modelled for a non-member group —
  `w4_mcast_{4,6}_nomember` (an extra NET_RX section expected: section
  mismatch). The IPv4 trace rejects D3's current `xmitMulticastLoop`
  unmodified: a real defect this class alone finds.
- **W4-M14** the loop keyed on the IPv4 `MC_LOOP` bit — `w4_mcast_noloop_v4opt`
  (the mirror would expect no NET_RX section; Linux loops).
- **W4-M15** the IPv6 fragment id as record + 1 (v1's rule) or from a
  kind-110 site — `w4_frag_6_connected` bytes / hidden mismatch.
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
- **W7-M10** (stretch, under 13.5's repoll option) the poll continuing past
  `budget` or `napi_complete_done` called after a full poll —
  `w7_budget_dead` (section 10): the second NET_RX section is unexpected
  or missing.

Controls: `w4_frag_4_unconnected` (`unsupported`), the phase-1 commuting
detector on synthetic record streams (a `.reschedTx` inside an open encrypt
section with ring items must be `unsupported`; the same with the ring empty
must pass; and the same shape with the units swapped, a `.reschedEncrypt`
nested under an open tx section with a `CRYPTED` head, must be
`unsupported` — the generic form, v2 M7), `w4_mcast_noloop_v4opt`, and the
measurement probes of section 12 re-run on any new kernel.

## 9. Out of scope (fail-noisy), and why

| Item | Why |
|---|---|
| P5 arms: `wg_prev_queue_dequeue`'s `tail != head` (queueing.c:96-97, 105), concurrent producer mid-enqueue | SMP or in-region preemption |
| P9: a poll using its budget (receive.c:483-484) | **reachable** on one CPU via `-EPIPE` `DEAD` entries (section 10); stretch tier under 13.5, or excluded by choice with an explicit `unsupported` at the poll site |
| `net_rx_action`'s squeeze (`netdev_budget` 300, 2 jiffies) and `__do_softirq`'s restart limit | at most 128 segments per datagram: two polls of 64; `unsupported` beyond (fail-noisy) |
| A device MTU of 0 or below 68 (`.padNoMtu` true, `.openHasInet` false) | decision 13.6 |
| A batch item deferred by io_uring (`-EAGAIN`, poll-arm or io-wq) | avoided by `SO_SNDBUFFORCE`; a deferral fails on `wg_batch`'s CQE result (5.5) |
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
packet on one CPU", and v1 of this note kept it out by counting only
`CRYPTED` items: one from the worker path (the pending softirq is serviced
at the next `ptr_ring_consume_bh`, `softirq.c:402-408`) or two at an irq
exit inside `wg_queue_enqueue_per_peer_rx`. **Both arguments overlooked
`DEAD` entries** (v2, M4). `wg_packet_rx_poll` counts every non-`UNCRYPTED`
entry it drops: a `DEAD` one takes `goto next` (receive.c:456-459), is
freed, and still runs `if (++work_done >= budget) break` (`:483-484`). The
`-EPIPE` arm of `consume_data` (`:526-529`) produces `DEAD` entries in the
softirq, one per data message that finds the decrypt ring full while the
peer's `rx_queue` accepts it (2.6: this needs **two peers**, A's queue
short of 1024 while the ring holds B's items). A UDP GSO datagram to wg0's
port fans up to 128 data messages into one `net_rx_action` (`udp.c:
2275-2280`, `udp.h:459-492`; E §4), so:

- B's 1024-item batch fills the decrypt ring (no worker runs inside the
  call, 2.7); in the same `io_uring_enter`, one GSO datagram carrying
  **64 or more** data messages for A takes `-EPIPE` 64 times and A's NAPI
  joins `poll_list` at the first (`dev.c:4665-4669`);
- `net_rx_action` polls A after the backlog poll (`:7074-7083`): A's
  `rx_queue` head is a `DEAD` entry (nothing `UNCRYPTED` precedes it), the
  poll drops 64 and breaks at `work_done = 64` (**`.rxPollBudgetDone`
  true**, `RxData.lean:311`), `napi_complete_done` is not called;
- `napi_poll` puts A on `repoll` (`dev.c:6959-6975`), `net_rx_action`
  breaks out when `list` is empty with `repoll` non-empty, splices
  `repoll` back and re-raises NET_RX (`:7102-7110`); `__do_softirq`'s
  restart runs **a second `net_rx_action`** (a second NET_RX section),
  whose poll drops the rest (with 65 or more messages, at least one) and
  completes.

So P9 is reachable on one CPU, in the stretch tier (two sessions, a full
ring, a 64-segment GSO inject): class `w7_budget_dead`. Its mirror side is
the existing arm plus, in the environment, the repoll: `napiSoftirq` loops
while the polled NAPI stays scheduled, consuming one NET_RX section start
per poll, and reports `unsupported` beyond `__do_softirq`'s ten restarts
or if a section is missing (fail-noisy). `netdev_budget = 300` and the
2-jiffy limit stay unreachable (section 9). **Decision 13.5** chooses
between building this (recommended) and excluding P9 by choice, in which
case the exclusion is an explicit `unsupported "a poll exhausted its
budget (net_rx_action's repoll)"` at the poll site, not the `invariant`
that would fire today (5.2).

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
- **High until 13.2 is decided — the (c') operand ambiguity** scales with
  the item count (2.8, C2): with the enumeration bound of 3, most
  full-ring traces and about 2% of 8-item traces would fail on one open
  placement. Option (ii) keeps the operand check at two mirror runs per
  failing trace.
- **Medium — sender buffers** (2.7, M1): the xmit batches depend on
  `SO_SNDBUFFORCE`; P-A confirms every CQE is present at `io_uring_enter`'s
  return, and `wg_batch`'s result makes a deferral fail noisily thereafter.
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

**Probes first (gating, throwaway, `harness/probes/w47_*.c`), with
`SO_SNDBUFFORCE` on the senders (M1):**
- **P-A** bulk feasibility: 1025 io_uring sends of data messages to wg0's
  port and 1025 xmits into wg0, under KCOV: wall time from `enter` to idle
  workers, whether every item queued before any worker ran (`-ENOSPC`
  observed exactly once), **every CQE present at `io_uring_enter`'s return
  with `res` = length** (no `-EAGAIN` deferral), record counts per item in
  both children, observe size, and 128-segment GSO xmit timing. **Its
  outputs are `kcov_capacity`'s bulk value and `wait_ms`'s default** (v2,
  m5), and the full-ring tier's go/no-go (13.4).
- **P-B** fixture facts: `ip -6 addr show wg0` after `wg_up` (no `fe80`
  expected); `ip -6 maddr show wg0` and `ip maddr show wg0` (the membership
  sets `{ff01::1, ff02::1}` and `{224.0.0.1}`, M3); a `PROBE` send over a
  `mtu 1300` route reaching `wg_xmit` unfragmented (one ciphertext of 1460
  bytes); **the errnos of `route_into_wg0`'s four requests at MTU 1279 and,
  under 13.6, at MTU 0** (the IPv6 add `-EINVAL`, the IPv4 add `-ENOBUFS`,
  the route adds), and whether `ip link set wg0 mtu 0` is accepted.
- **P-C** (offline, no VM): the **nesting proxy** of 5.4 over the existing
  D1/D2 check runs' records (the phase-1 counter itself is zero there by
  construction, M7).

**Interface commit** (on `task/w47`, **only after D3+L+A+E are integrated**
on the base): `Device.mtu`, `inet4Dev`, `inet6Dev`; `PrevQueue`;
`Kernel.napiPollList`; `Sender.inetId`; the new decisions and hidden sites
(`.txHash`, `.inetIdSeed`, `.ipv6FragId`); the op schemas (`wg_xmit`
options, `wg_set_mtu`, `wg_create.mtu`, `net_fixture` routes, `wg_batch`
with its CQE result, `kcov_capacity`, `wait_ms`); the wire opcodes
allocated by the coordinator (placeholders until then, section 6);
`DEVICE_MTU` removed; the two new environment files created empty with
their hooks in `Env.lean`.

**Streams and file ownership** (the two streams meet in `Env.lean` only at
the hooks, so neither edits the other's file):
- **T — transmit shapes (W4):** **`Leanux/Env/IpStack.lean`** (new:
  `xmitPackets`, the membership sets, `Sender.inetId`, `setMtu`
  consequences; `Env.lean` hooks `xmitPackets`, `xmitMulticastLoop` and
  the `wg_set`/`wg_up` keepalive rule of section 4), `Leanux/WG/Device.lean`
  (`wgXmit` GSO/trim/`wgOpen`), `Leanux/WG/Send.lean` (`sendKeepalive`),
  `harness/noise.py` (segment/fragment builders), `harness/guest.c` W4 ops
  and fixture (`route_into_wg0` MTU-aware, `SEND2_FD`, sockopts).
- **B — bulk (W7):** `Leanux/WG/Send.lean` (`enqueuePerDeviceAndPeer`),
  `Leanux/WG/Data.lean` (`txWorker`), `Leanux/WG/RxData.lean` (`rxPoll`,
  `enqueuePerPeerRx`), `Leanux/WG/Receive.lean` (`consumeData` arms),
  **`Leanux/Env/Batch.lean`** (new: `batch`, `napiSoftirq` with the
  per-peer list and, under 13.5, the repoll, the `condResched`
  generalization, the generic phase-1 detector; `Env.lean` hooks `batch`
  and the worker runners), `harness/guest.c` `wg_batch` (from `wg_flood`,
  with the CQE result), `kcov_capacity`.
- **H — harness, generator, corpus, evidence:** `scripts/wg-w47-corpus.py`,
  `corpus/wireguard/w4_*`, `w7_*`, `scripts/wg-mutants.py` patterns W4-M*
  and W7-M*, `evaluator/napi_orders.py` extension, the probes and their
  results note.

**Integration:** the full check with bulk traces one per chunk, the W4/W7
mutants and controls, the phase-1 counter report, the report and signoff.
Phase 2 (step workers) and the stretch tier are separate decisions after
integration.

## 13. Decisions for the user

Items 1, 3, 4 and 7 are [AGENT] recommendations pending the user; items
2, 5 and 6 are **user decisions** with options, since one of their options
weakens or narrows a check.

1. **The fragment-ident route** — recommendation: the **connected** sender
   with no K1, with M2 applied (`.txHash` then `.inetIdSeed` at
   `wg_connect`; `inet_id` as socket state consumed by every `SEND2_FD`
   datagram, GSO included; first id = seed + 1). The unconnected `DONT`
   class stays `unsupported`; K1 only if the outer-header bytes ever become
   an observable.
2. **The (c') placement ambiguity under bulk (C2)** — **user decision.**
   The control-flow placement is pinned (2.8); only the poll's two
   peer-refcount compares (`kref_get_unless_zero` in the allowed-IPs
   lookup, `wg_peer_put`) differ, by one, and `check.py` enumerates
   placement vectors only for ≤ 3 open polls. Options:
   - **(i) `operand_exclusions`** for those two compares at the poll's call
     sites (the precedent form, `kcov.json`). Cost: **a check is lost** —
     the peer reference count as the poll sees it, which is how a mirror
     that drops or duplicates a `wg_peer_get`/`put` on the receive path
     would be caught (the outcome, "not zero", is the same either way).
     Nothing else changes.
   - **(ii) operand agreement partitioned per poll section** — keeps the
     check. The (c') choice of poll i changes only the operands inside
     poll i's NET_RX section (by the next item the put has happened in
     both placements), so the placements are independent across polls.
     The check runs the mirror **twice** per operand-mismatching trace
     (all-after-put and all-before-put), tags each mirror branch with the
     NET_RX section it ran in, partitions Linux's comparison records by the
     section blocks the remote stream already carries in the comparisons
     child (`pair_sections`, `check.py:224-240`, `:266`), and accepts each
     section under either run; the two runs must agree on every branch
     outside the NET_RX sections and on all observations, else the
     independence premise failed and the trace fails. Cost: one more
     mirror run and the section tagging, O(n) matching, no kernel change;
     `NAPI_PLACEMENTS_MAX` goes away. **Recommended** [AGENT]: it keeps
     the operand check at a cost that does not grow with n.
   - **(iii) a kernel record of the placement** (K3, section 3): exact and
     simple in the check, but a new hook against the user's zero-new-hooks
     preference, needing patch approval; and the next such ambiguity would
     need another.
   K2 (record `work_done`) is not recommended for any of these.
3. **The commuting assumption** — recommendation: phase 1 is required in
   the **generic form** (5.4: any nested yield under an outer open worker
   with queued items, not a named unit pair); P-C reports the nesting proxy
   on D1/D2; phase 2 (step workers) is decided on the W7 corpus's phase-1
   count.
4. **The full-ring tier (1025 items)** — recommendation: gate it on P-A
   **after `SO_SNDBUFFORCE`** (without it the xmit batch is deferred at
   about 277 items and P-A would measure the wrong thing). If it does not
   fit the 4.5 s bound on TCG, keep the `-ENOSPC` arms as built mirror code
   with the domain `unsupported`, and carry W7 on the 2-8-item tiers.
5. **The stretch tier and P9** — recommendation: build the stretch arms in
   B (`-EPIPE`, two NAPIs) and schedule the traces after integration.
   **P9 is a user decision** (section 10): (a) **stretch tier** — the
   `w7_budget_dead` class and `net_rx_action`'s repoll in `Batch.lean`
   (a loop over consecutive NET_RX sections while the NAPI stays scheduled,
   `unsupported` beyond ten restarts); cost: one class and about a dozen
   lines of environment, on the stretch tier's two-session setup; or (b)
   **excluded by choice**, as an explicit `unsupported` at the poll site
   when `work_done ≥ budget` (fail-noisy), with the reason "a 64-message
   GSO inject against a full ring with two sessions". **Recommended: (a)**
   [AGENT], since the user's bar is "exclude only for profound reasons"
   and this arm is a real single-CPU path with a cheap environment model.
6. **`wg_set_mtu 0`** — **user decision.** The coordinator's recommendation
   is to exclude it as an unreasonable configuration, cover
   `.openHasInet6` false via `IFLA_MTU` 1279 with the MTU-aware fixture,
   and document `.padNoMtu` true and `.openHasInet` false as excluded with
   that reason. **After verification I disagree, mildly** [AGENT]: the
   kernel accepts MTU 0 without complaint (`dev_validate_mtu`, no
   `min_mtu`), the two arms are real C branches `wg_open` and
   `calculate_skb_padding` were written for, the class is terminal, and
   once the fixture is MTU-aware (needed anyway for 1279) its extra cost is
   one more threshold (68) and the errnos P-B measures. "Unreasonable" is
   a judgment of taste, not a profound reason in the user's sense. Options:
   (a) **include** `w4_set_mtu_0` as a terminal class behind P-B
   (recommended, cheap to reverse); (b) **exclude** with the reason above,
   documented in section 9 — `.openHasInet6` false is covered by
   `w4_create_mtu_1279` either way. Both options leave `.openHasInet6`
   covered; only (a) covers `.padNoMtu` true and `.openHasInet` false.
7. **The D2/D3/E corrections** — recommendation: record at integration, in
   the owning notes: D2 §2 "wg0 gets a random link-local address" (wrong,
   2.4); D2's single named commuting case (generalized, 5.4); **D3's
   `xmitMulticastLoop` loops for any `224/4`** (latent; the set is
   `{224.0.0.1}`, 2.4); v1 of this note's kind-110 IPv6 id, `.padClamped`
   as a new outcome, the `w4_route_mtu_probe` clamp claim, and the
   "staged `wg_xmit` path is the same" sentence (all corrected in v2);
   E's `wg_flood` not reading its CQEs (harmless for loopback injects,
   subsumed by `wg_batch`).

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
- **Added in v2** (each read for the audit response):
  - random.h: `get_random_u32_below` 60-85 (the inline path, `:83`),
    `get_random_u32_above` 98-103. `kernel/patches/choice-stream.patch`:
    `get_random_##type` records `100 + sizeof` (hunk at random.c:536-549),
    kind 110 only in `__get_random_u32_below` (hunk at random.c:565-590).
    output_core.c: 14-19, 47-55. Built kernel (`.artifacts/kernel-net-
    choice`): `__ipv6_select_ident` and `ip_idents_reserve` absent from
    `System.map`; DWARF chains at the draws, `random.h:87 → :102 →
    output_core.c:18 → :53` and `sock.h:2092 → :2098 → datagram.c:75`.
    `harness/steer.py` 26-28 (`CHOICE_HELPERS`); `check.py` 285-320 (the
    consumer frame), 192 (`RANDOM_KINDS`).
  - datagram.c: `__ip4_datagram_connect` 75-76. sock.h: `net_tx_rndhash`,
    `sk_set_txhash` 2088-2099. ipv6/datagram.c: `__ip6_datagram_connect`
    141-161, 189-199, 268. ip.h: `ip_select_ident_segs` 559-589 (connected
    branch 568-581, `atomic_add_return`). ip_output.c: 1436-1445 (DF for
    `PROBE`), 1465 (`ip_select_ident`, segs 1). af_inet.c: 1439-1457 (the
    per-segment `id++`).
  - loopback.c: 79 (`skb_orphan`). sock.c: 282-286 (`sysctl_wmem_default`),
    761-777 (`sk_mc_loop`), 1328-1333 (`SO_SNDBUF[FORCE]`), 2918-2923
    (`sock_alloc_send_pskb`'s `-EAGAIN`). sock.h: 2867-2869 (`SK_WMEM_MAX`).
    io_uring/net.c: 578-579. io_uring/io_uring.c: `io_queue_async`
    1913-1929. `task/e-b:harness/guest.c`: `rtnl_request` 469-478,
    `route_into_wg0` 486-527 (called at `:1037`), `flood_prep`/`flood_enter`
    726-770 (CQEs not read), the sender 814-826.
  - addrconf.c: `ipv6_add_dev` 375-382, joins 466-475,
    `addrconf_join_solict` 2246-2254, `addrconf_add_dev` 2566-2581
    (`ff00::/8`), `inet6_addr_add` 3024-, `addrconf_notify` 3683-3711
    (`mtu6` 3697-3700). igmp.c: `ip_mc_up` 1789-1803, `ip_check_mc_rcu` 2724.
    route.c: `__mkroute_output` 2566-2587 (`RTCF_LOCAL`), 2647-2652
    (`dst.output = ip_mc_output`). ip_output.c: `ip_mc_output` 367-410.
    ip6_output.c: `ip6_finish_output2` 60-100. af_inet6.c: 223-224,
    237-238. device.c: 290 (`IFF_NOARP`), 296-297 (no `min_mtu`).
    devinet.c: `inetdev_event` 1570-1590 (re-creation at 1586-1588),
    1637-1643, 888 (`-ENOBUFS`). `kernel/config-x86_64-net-choice`: 686,
    724-725.
  - receive.c: `wg_packet_rx_poll` 438-491 (`DEAD` at 456-459, budget
    483-484), `wg_packet_consume_data` 509-540. dev.c: `napi_poll` 6959-6975,
    `net_rx_action` 7052-7115 (repoll splice and re-raise 7102-7110).
    ipv6/route.c: `ip6_mtu` 3272. udp.c: `udp_send_skb` 1018-1036.
    send.c: `calculate_skb_padding` 141-160, tx worker 262-285 (yield
    282-283), encrypt worker 287-309. queueing.c: 72-78, 80-106.
  - Mirror: `task/d3-int:Leanux/Env.lean` 90-93 (`xmitMulticastLoop`),
    236-245 (`runWorker`), 267-296 (`condResched`), 302-313, 318-322
    (`requireNoCryptWork`), 338-344 (`runSendWorkers`), 355-362
    (`afterXmit`), 671-680 (`napiSoftirq`), 696-703 (`napiIrqExit`),
    708-711 (`runDecryptWorker`); `task/d3-int:Leanux/Syscalls.lean`
    133-145 (`runSendWorkers` at 139-141); `task/d3-int:evaluator/check.py`
    224-240 (`pair_sections`), 255-275 (section records only in the remote
    stream, both children), 732-770 (`operand_agreement`), 811-845
    (`NAPI_PLACEMENTS_MAX`, `napi_placements`), 924;
    `task/d3-int:docs/2026-10-06-contended-host.md` §2, 166-180;
    `task/census:Leanux/Kernel/Defs.lean` 239-275, 356-360;
    `task/census:Leanux/WG/RxData.lean` 276-313 (`.rxPollBudgetDone` at
    311); `correspondence/kcov.json` `files` (queueing.h listed,
    queueing.c not), `functions` (164, `wg_packet_rx_poll` in,
    `wg_prev_queue_dequeue` out), `operand_exclusions` (one entry, the
    precedent form); `docs/2026-10-04-d2-data-plane.md` 324-328 (the
    clamp at inner lengths 1404-1420); `task/l-m:harness/guest.c` (no
    `IFLA_MTU`).
  - `Decision.lean` lines, `task/census` → `main`: `.openHasInet` 742 →
    825, `.openHasInet6` 743 → 826, `.xmitNotGso` 754 → 837, `.xmitWalk`
    755 → 838, `.padNoMtu` 943 → 1026, `.padOverMtu` 944 → 1027,
    `.encChecksumPartial` 948 → 1031, `.enqueuePeerQueueFull` 978 → 1061,
    `.enqueueRingFull` 979 → 1062, `.prevQueuePeeked` 986 → 1069,
    `.dataEpipe` 990 → 1073, `.rxPollBudgetDone` 1025 → 1108;
    `.padClamped` is declared at 231 on both.

## 15. Revision v2 — audit response

Each finding of the audit, verified against the sources named in section
14 before adoption; **adopted** means the body above is corrected in place.
Pushback is marked.

**C1 — the IPv6 fragment id is a kind-104 record.** Adopted (2.5, 3). The
arithmetic checks: the inline `get_random_u32_below(U32_MAX)` draws the
exported `get_random_u32()` (kind 104), rejects exactly `r = 0`, returns
`r − 1`, so the id is the first non-zero record. `.ipv6FragId`, the
`noise.py` builder and the `#guard` vectors use that rule. **Pushback on
the site:** the consumer frame is **output_core.c:18**, the inlined
`__ipv6_select_ident` body, not :47 — the check takes the first frame
outside the random/clock helpers (`steer.py:26-28`, `check.py:304`), which
is how the equally inlined `ip_idents_reserve` got route.c:482; the DWARF
chain on the built kernel confirms it (section 14). The table names :18.

**C2 — the NAPI placement ambiguity scales with the item count.** Adopted
(2.8, 5.3, 11) and **raised as decision 13.2** with the three options,
their costs, and (ii) recommended. Verified: `napiIrqExit` counts every
inline poll, `napi_placements` enumerates only for `count ≤ 3` and only on
an operand mismatch, and the comparisons child's remote stream carries the
section blocks (ii) needs. The base rate is the contended-host note's three
traces in a 1369-trace check. (ii) is formulated as two mirror runs with an
independence check, so its cost does not grow with n.

**M1 — xmit batches exhaust `sk_sndbuf`.** Adopted (2.7, 5.5, 6, 9, 11,
12, 13.4). Verified: the inject skb is orphaned inline at `loopback.c:79`,
the xmit skb keeps its charge to the tx worker; the default is 212992
(about 277 small skbs); `-EAGAIN` at `sock.c:2918-2923` → `net.c:578-579`
→ `io_queue_async`. **Pushback on the citation:** the deferral is
`io_queue_async` (`io_uring.c:1913-1929`, poll-arm or io-wq), not :1357
(`io_req_task_submit`'s `REQ_F_FORCE_ASYNC` arm). `SO_SNDBUFFORCE` on both
senders; 2.7's "the same" sentence is corrected; `wg_batch`'s result
carries the CQEs so a deferral fails on the result (as an operation result,
not a new checker).

**M2 — the connected sender draws a txhash first.** Adopted (2.1, 3, 4, 6,
13.1). Verified: `sk_set_txhash` at `datagram.c:75` before the seed at
`:76`; a v4-mapped `connect()` on the dual-stack sender takes exactly that
path and returns (`ipv6/datagram.c:157-161`, `:189-199`); a native IPv6
`connect()` draws the txhash only (`:268`); the UDP path calls
`ip_select_ident` with `segs = 1`, so a GSO datagram consumes one `inet_id`
and its segments count up from it; the first id is seed + 1. New site
`.txHash` (`.cut`) at the shared consumer frame `sock.h:2092`; `inet_id` is
socket state in `IpStack.lean`.

**M3 — the multicast membership sets.** Adopted (2.4, 4, 6, 8, 13.7).
Verified: `IFF_NOARP` (device.c:290) makes `addrconf_join_solict` return
early, so the IPv6 set is exactly `{ff01::1, ff02::1}` (v1's solicited-node
groups were wrong); IPv4 loops only through `RTCF_LOCAL`, which
`ip_check_mc_rcu` grants to members, and the `in_device` joins only
`224.0.0.1`; D3's `xmitMulticastLoop` (`task/d3-int:Env.lean:90-93`) loops
for any `224/4` — latent and fail-noisy, corrected to the set, with
`w4_mcast_4_nomember` as the trace that rejects the old code; the AF_INET6
sender's IPv4 side comes from `inet6_create` (`af_inet6.c:237-238`) and
`sk_mc_loop` reads `MC6_LOOP` for it, so the control uses
`IPV6_MULTICAST_LOOP` (and `w4_mcast_noloop_v4opt` shows `IP_MULTICAST_LOOP`
is a no-op there).

**M4 — P9 is reachable on one CPU.** Adopted (2.8, 5.2, 9, 10) and
**raised as decision 13.5** with (a) the stretch tier plus the repoll in
`Batch.lean` and (b) exclusion by choice as an explicit `unsupported`;
**(a) recommended**. Verified: `DEAD` entries take `goto next` and still
count (`receive.c:456-459`, `483-484`); the `-EPIPE` arm marks entries
`DEAD` in the softirq; two peers are needed (2.6's accounting); a
64-message GSO inject suffices; the repoll is a second `net_rx_action`
after `dev.c:7102-7110`. Precision: 64 entries take the arm (the 64th
`++work_done >= budget`); the 65th gives the repoll an item.

**M5 — the MTU classes conflict with `route_into_wg0`.** Adopted (2.3, 6,
12). Verified: `rtnl_request` fails on any unexpected errno; below 1280 the
IPv6 add is `-EINVAL` (`ipv6_add_dev`); below 68 the IPv4 add is `-ENOBUFS`
while the `in_device` is absent and `0` (not `-EEXIST`) once a valid MTU
re-created it; the fixture becomes MTU-aware and **expects the kernel's
refusal** (the errnos fixed by P-B), which also checks the teardown the
mirror's `inet4Dev`/`inet6Dev` record. The 2.3/section-6 inconsistency
about MTU 0 is resolved (the class, if any, is set-MTU, keepalive, down,
up, observe). Classes that raise the MTU back stay terminal. v1's "normal
lowering (say 1000)" would itself have dropped IPv6; it is now 1300.

**M6 — a keepalive from `wg_set`/`wg_up` under a session is unsupported.**
Adopted (section 4). Verified: `Syscalls.lean:139-141` → `runSendWorkers`
→ `requireNoCryptWork` (`:318-322`, `:339`). [AGENT] The `afterXmit` shape
is taken for `wg_set`/`wg_up` (the crypt workers run in the guest's wait,
ordered by section starts); this lifts an `unsupported` without weakening
a check, so it is not a user decision. The timer-driven alternative is
noted and not taken.

**M7 — the commuting breakage is generic.** Adopted (premises, 5.4, 8, 12,
13.3). Verified against `runWorker`/`condResched` (`task/d3-int:Env.lean:
236-296`): the mirror runs the nested unit to completion inside the outer's
call, so any nested yield under an outer open worker with queued items is
the same hazard. Phase 1 keeps a stack of open workers and tests it
generically; P-C over D1/D2 is vacuous (one-item queues) and is replaced by
the nesting proxy; phase 2 is decided on the W7 corpus. Controls cover
both unit orders.

**M8 — `.padClamped` is already two-outcome.** Adopted (1, 2.3, 4, 6, 8,
13.7). Verified: D2's inner lengths 1404-1420 cover the clamp
(`d2-data-plane.md:324-328`, `.padClamped` at `Decision.lean:231`); with
route MTU 1300 and len 1420, `min(1300, 128)` does not clamp. The claim is
dropped; the new outcomes are `.padOverMtu` true (and `.padNoMtu` true only
under 13.6). The payload 1269-1272 variant is noted as not new coverage.
W4-M8's rejection is restated with the actual arithmetic.

**M9 — `queueing.c` in `kcov.json`.** Adopted with a precision (section
4). `queueing.c` joins `files` and `wg_prev_queue_dequeue` joins
`functions` (verified absent). **Pushback on the mechanism:** its tests are
pointer compares, and the precedent for those is a decision declared in
the `d` form without a comparison (`.prevQueuePeeked`), which
`operand_agreement` skips (`check.py:742-747`); `operand_exclusions` is the
precedent for a *declared* comparison with an unmodelable operand at one
call site. The note uses the `d` form and keeps `operand_exclusions` as the
fallback if the check is ever extended to claim every recorded compare.

**m1** adopted (2.2): xmit 1 tests `0 > 128`; the data messages are 80
bytes (v1's 48 was the padded plaintext). **m2** adopted (2.5): `udp_csum`
+ `csum_tcpudp_magic` at `udp.c:1030-1033`. **m3** adopted (2.3): the IPv6
`dst_mtu` falls back to `idev->cnf.mtu6` (`ip6_mtu` → `ip6_dst_mtu_maybe_
forward`), synced at `NETDEV_CHANGEMTU`. **m4** adopted (2.2, 6) with a
correction: at `gso_size` 1392 the 65507-byte payload gives **48**
segments (47 full plus one of 83 bytes), not 47; 128 segments need
`gso_size ≤ 511`; the cross product is constrained accordingly. **m5**
adopted (5.5, 6, 12): `kcov_capacity` and `wait_ms` are P-A outputs.
**m6** adopted (header, 2.3, 14): the header already said `task/census`,
but section 14 gave bare numbers; the `main` lines are now listed. **m7**
adopted (2.3, 4): `PROBE` sets DF, `ignore_df` is false, the unconnected id
is 0 and the connected one is the next `inet_id`.

**Section 13** adopted as recommendations pending the user (1, 3, 4, 7)
and as user decisions with options and a recommendation (2, 5, 6). On 6,
after verification, this revision **disagrees mildly** with excluding MTU
0 and says so in place, recommending inclusion as a terminal class behind
P-B; the user decides.

**Execution plan** adopted (12): the interface commit only after D3+L+A+E
are integrated; stream T in `Leanux/Env/IpStack.lean`, stream B in
`Leanux/Env/Batch.lean`, meeting in `Env.lean` only at the hooks; wire
opcodes as placeholders until the coordinator allocates them.
