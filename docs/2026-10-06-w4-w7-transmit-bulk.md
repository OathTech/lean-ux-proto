# W4 + W7: transmit shapes and bulk queues — design, 2026-10-06

Status: **decided, revision v3** (2026-10-07). Revision v2 (2026-10-06)
answered a critical audit (section 15); revision v3 applies the user's
decisions of 2026-10-07 (section 13, with provenance) and the **WireGuard
boundary rule** — [USER 2026-10-07] "we should stop at the boundary of
wireguard (unless this breaks important things)": the IP stack is modeled
only where it drives WireGuard code paths or is needed to predict
WireGuard's observable behaviour. Section 16 gives, per class, the
WireGuard line, decision or outcome it alone reaches, the kept minimal set,
and what is excluded as beyond the boundary (fail-noisy `unsupported`).
The body below is corrected in place; sections marked *record only* keep
verified kernel facts for classes no longer built. The census
([2026-10-06-wireguard-census.md](2026-10-06-wireguard-census.md)) lists W4
(transmit shapes, M) and W7 (bulk and multi-item queues, L) as in-reach
workstreams toward the user's goal of 2026-10-06, 100% of reasonable
single-CPU WireGuard. P5 (concurrency recheck arms) stays excluded. P9
(NAPI budget exhaustion) is **reachable on one CPU** and is built in the
stretch tier (section 10; decision 13.5(a)).

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

**W4 — transmit shapes** (v3: every `wg_xmit` arm **WireGuard code** can
take on one CPU, with its bytes checked at the fixture's listener; the IP
stack only as far as those arms and their bytes need it):
- UDP GSO: one `sendmsg` with `UDP_SEGMENT` arrives at `wg_xmit` as one GSO
  skb; `skb_gso_segment` splits it; the segments are **one staged list** and
  **one ring item** (device.c:176-204, 215, 218). **Kept**, IPv4, equal
  segments: `.xmitNotGso` false, `.xmitGsoError` false and the n-iteration
  walk are WireGuard lines no other class reaches (16.1).
- The staged-queue trim, `> MAX_STAGED_PACKETS` (device.c:211-214), reachable
  with two or three GSO transmissions and no session. **Kept** (16.1).
- The padding arms of `calculate_skb_padding` (send.c:141-160) not yet
  taken: `len > mtu` (`:154-155`, `.padOverMtu` true) via a route MTU below
  the device MTU — **kept**, IPv4 — and `!mtu` (`:145`, `.padNoMtu` true,
  only with a device MTU of 0) — **kept**, decision 13.6(a). The `min` clamp
  (`:157-158`, `.padClamped`) is **already two-outcome** since D2 (inner
  lengths 1404-1420, D2 §6; v2, M8). `SIOCSIFMTU` moves the device MTU and
  the `wg_open` arms; `IFLA_MTU` at creation is **dropped** (16.1: nothing
  `wg_set_mtu 0` does not reach).
- `Device.mtu` as mirror state in place of `WG.DEVICE_MTU`
  (`Leanux/WG/Send.lean:48`), read by `wg_xmit` (device.c:173), the keepalive
  (send.c:232) and `wg_open`'s IPv6 test (device.c:34, 47). **Kept**: the
  data flow `dev->mtu → PACKET_CB->mtu → padding` is checked by
  `w4_set_mtu_1300`'s bytes.
- Multicast and link-local destinations: **excluded, beyond the WireGuard
  boundary** (16.1: `wg_xmit` sees ordinary packets; the loop copy, source,
  TTL and hop limit are IP-stack behaviour). Only the IPv4 membership set
  `{224.0.0.1}` is kept, because the existing corpus's no-peer `wg_xmit`s to
  `224.0.0.1` (`evaluator/generate.py:302`) need it to predict their NET_RX
  section (2.4, M3). IPv6 multicast stays `unsupported`.
- Transmit fragmentation (`IP_PMTUDISC_DONT`, two `wg_xmit` calls in one
  system call): **excluded, beyond the WireGuard boundary** (16.1: the two
  calls take only lines GSO already takes; the ident draws are IP-stack
  hidden inputs). K1 is deferred under the boundary rule.

**W7 — bulk and multi-item queues.** The crypt rings and per-peer
`prev_queue`s holding several items at once, produced by io_uring batches
with no drain point between sends (the E measurement,
`task/e-dos:docs/2026-10-05-e-probe-results.md`): the workers' multi-item
loops, the `peeked` state of `prev_queue`, a `DEAD` break mid-list, the
`cond_resched` placements, the far end — `-ENOSPC` and `-EPIPE` on full
queues (1024 items) — and the poll's budget arm (P9, 13.5(a)). This is
WireGuard queue behaviour and stays in scope; v3 drops only "several
peers' polls in one `net_rx_action`" (16.2: an environment arm with no
WireGuard line of its own) and the n = 4 and `rx_dead` instances.

## 2. Kernel mechanisms, verified

### 2.1 UDP GSO through `wg_xmit`

*v3 scope:* kept for **IPv4 with a `gso_size` that divides the payload**;
IPv6 GSO and a short last segment are beyond the WireGuard boundary (no
WireGuard line of their own, 16.1) and are `unsupported` in `xmitPackets`
(fail-noisy). The IPv6 and last-segment facts below stay as record.

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
    segments carry ids 0, 1, …, n−1: deterministic, no hidden input. For a
    **connected** sender (record only: not built in v3, section 3) the branch at
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

*v3 scope:* kept are the IPv4 route-MTU class and `SIOCSIFMTU` to 1300 and
to 0 (16.1). The IPv6 route MTU (`mtu6`), `IFLA_MTU` at creation and
`SIOCSIFMTU` to 1279 are dropped: each reaches only lines `w4_set_mtu_0`
or the IPv4 class already reaches. The MTU-aware fixture is needed for
the MTU-0 class's `wg_up` only.

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
  (`ip.h:583-584`); a connected sender, not built in v3, would take the
  next `inet_id` instead (v2, m7).
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

*v3 scope — record only, except the IPv4 membership set.* Multicast and
link-local destinations reach no WireGuard line of their own (`wg_xmit`
sees an ordinary packet; the peer lookup reads only the destination), and
the loop copy, source selection, TTL and hop limit are IP-stack behaviour:
**excluded, beyond the WireGuard boundary** (16.1). What is kept: the IPv4
set `{224.0.0.1}` in `xmitMulticastLoop`, because the existing corpus's
no-peer `wg_xmit`s to `224.0.0.1` (`evaluator/generate.py:302`, 41
operations) need it to predict their NET_RX section, replacing D3's "any
`224/4`"; IPv6 multicast and `fe80::/10` destinations stay `unsupported`
(fail-noisy). The D2 §2 correction (no link-local address on wg0) stands.

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

*v3 scope — record only.* Inner fragmentation reaches no WireGuard line
that GSO does not: two ordinary `wg_xmit` calls, `CHECKSUM_NONE` packets
(`.encChecksumPartial` false, GSO's too), a second packet without a UDP
header that WireGuard never parses. The ident draws (`inet_id`, the
connected sender's txhash, the IPv6 Fragment id) are IP-stack hidden
inputs. **Excluded, beyond the WireGuard boundary** (16.1): `xmitPackets`
answers `unsupported "a fragmented datagram (beyond the WireGuard
boundary)"` for `DONT` above the route MTU, and the connected sender,
`SEND2_FD` and `wg_connect` are not built. **Outer** fragmentation (the
ciphertext datagram exceeding `lo`'s 65536-byte MTU) would need wg0's MTU
raised to within about 60 bytes of 65535; it happens after
`udp_tunnel_xmit_skb` (`ip_fragment` with `ignore_df = 1`, no ICMP) with no
WireGuard line, and is excluded on the same rule; the listener's
`recvfrom` sees the reassembled datagram either way. K1 is deferred under
the boundary rule. The facts below stay as record.

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
`sk_sndbuf = 16 MiB`, `sock.c:1328-1333`) is set on `SEND_FD`** before
the window; 1025 full-size xmits charge about 2.4 MiB.
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
| Connected sender's txhash | `__ip4_datagram_connect` → `sk_set_txhash` → `net_tx_rndhash` → `get_random_u32()` (`datagram.c:75`, `sock.h:2088-2099`), **before** the seed; a v4-mapped `connect()` on the dual-stack sender takes this path (`ipv6/datagram.c:157-161`, `:189-199`, then `goto out`), a native IPv6 `connect()` draws only this (`:268`) | **v3: not built** (beyond the WireGuard boundary, with the connected sender). Record: it would be a `.cut` site (kind 104, 4 bytes) at consumer frame `include/net/sock.h:2092` (DWARF chain `sock.h:2092 → :2098 → datagram.c:75`), consumed by `wg_connect` first (v2, M2) | — |
| IPv4 fragment ident, **connected** sender | `__ip4_datagram_connect`, `datagram.c:76`: `atomic_set(&inet->inet_id, get_random_u16())` | **v3: not built.** Record: a mirror site `.inetIdSeed` (kind 102, 2 bytes) into socket state `inet_id`, consumed once per datagram, GSO included, first id seed + 1 (`ip.h:575-581`; v2, M2) | — |
| IPv4 fragment ident, unconnected `DONT` sender | `.ipIdentReserve` records `delta` only (`route.c:481-482`); the bucket counter is boot-random (`:3720`) | **not reconstructible**: stays `.cut`; the class is `unsupported` (fragmentation is beyond the boundary; K1 deferred) | — |
| IPv6 fragment id | `ipv6_select_ident` → `get_random_u32_above(0)` (`output_core.c:18`): the inline `get_random_u32_below(U32_MAX)` calls `get_random_u32()`, **kind 104**, once per attempt (2.5; v2, C1) | **v3: not built.** Record: a mirror site `.ipv6FragId` (kind 104, 4 bytes) at consumer frame `net/ipv6/output_core.c:18`, id = the first non-zero record, a zero record redrawn at the same site | — |
| `wg_xmit`'s `mtu` | route/device, fixture facts | environment (`Env.xmitPackets`), checked by padding bytes | W4 |
| wg0's IPv6 presence | `dev->mtu ≥ 1280` at registration / after `CHANGEMTU` | mirror state `Device.inet6Dev` | W4 `wg_open` |
| Scheduling: encrypt/tx/decrypt yields | kind 302 resched records (`.reschedEncrypt/.reschedTx/.reschedDecrypt`, `Defs.lean`) | existing, now per item | W7 |
| Scheduling: NAPI placement | NET_RX section records (kinds 300/301) | existing; pinned per item for control flow (2.8); the (c') operand choice is decision 13.2 | W7 |
| Ordering of several queued units | section start records | existing | W7 |

**Kernel-change options (need user approval; the design does not depend on
them):**
- **K1.** Record the ident at `__ip_select_ident` (`route.c:505`, after
  `ip_idents_reserve`) as a hidden site. Would lift the unconnected-`DONT`
  fragmentation class and make `.ipIdentReserve`'s outer-datagram cut exact
  (the wg outer IP header is not observed today, so that part pays nothing
  now). **Deferred under the boundary rule** [AGENT 2026-10-07, delegated]:
  the ident is an IP-stack input to a class that is itself excluded.
- **K2.** Record `work_done` at the poll's `napi_complete_done`
  (receive.c:488) or the `state` the poll observes per iteration. Turns the
  "pinned per item" argument of 2.8 into a checked fact. Not recommended
  (13.2); the W7 corpus's `napi_orders.py` extension (section 8) reports
  any placement the argument does not cover.
- **K3** (v2, C2 option iii). Record the (c') placement itself: a choice
  record in `wg_queue_enqueue_per_peer_rx` after `wg_peer_put`
  (queueing.h:201), so a nested NET_RX section's position relative to it
  tells before-put from after-put. A new hook against the user's
  "generic capture points, zero new hooks" preference. **Moot**: option
  (ii) of 13.2 was approved [USER 2026-10-07] and keeps the check without
  it.
- The census's `handshake_queue_len` capture (P12) is not needed here.

## 4. W4 in the mirror and the environment

**Interface commit** (`Leanux/WG/Types.lean`, `Leanux/Kernel/Defs.lean`,
`Leanux/Kernel/Decision.lean`):
- `Device.mtu : Nat := 1420` (`wg_setup`, device.c:296), `Device.inet4Dev :
  Bool := true` and `Device.inet6Dev : Bool := true`; `WG.DEVICE_MTU` is
  removed and its three readers (`Send.lean:255`, `Env.lean:75-76`,
  `Device.lean:42`) read the state. v3: `wg_create` does not take
  `IFLA_MTU` (dropped, 16.1); only `setMtu` moves the three fields.
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
- **No new `HiddenSite`** (v3): `.txHash`, `.inetIdSeed` and `.ipv6FragId`
  belonged to the fragmentation classes, which are beyond the boundary
  (section 3, record only). The GSO ids and checksums are computed, not
  drawn.

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
  `gsoSize`, `pmtudisc ∈ {DO, PROBE}` and the fixture's route MTU for the
  destination (from the trace's `net_fixture`, section 6). v3: it models
  exactly what the kept classes need and answers `unsupported` (fail-noisy,
  "beyond the WireGuard boundary") to the rest:
  - GSO, **IPv4, `gsoSize` dividing the payload**: segment i's IPv4 header
    (`id = i`, `tot_len`, header checksum), UDP header (`len`, the complete
    checksum, `CSUM_MANGLED_0` for 0), payload slice; `csum := none`. The
    stack's `-EMSGSIZE`/`-EINVAL` conditions (2.1) are the operation's
    result with no `wg_xmit`. IPv6 GSO and a non-dividing `gsoSize`:
    `unsupported`.
  - `PROBE` with a route MTU, **IPv4**: a full-size packet with `mtu` = route
    MTU, DF set, id 0. IPv6: `unsupported`.
  - `DONT`, a connected sender, a datagram above the route MTU:
    `unsupported` (2.5).
  - Multicast/link-local: unchanged from D3 — `xmitBytesUnknown` for
    multicast destinations with no fixture-determined bytes, `unsupported`
    for IPv6 multicast and `fe80::/10`.
- **The IPv4 multicast membership set** (v2, M3; v3 kept for the existing
  corpus): `xmitMulticastLoop` (from d3-int) loops iff the IPv4 destination
  is in `{224.0.0.1}` (2.4), replacing D3's "any `224/4`"; IPv6 keeps D3's
  `unsupported`. No kept trace distinguishes the two IPv4 rules (the
  generator only ever sends to `224.0.0.1`); the correction is to the
  kernel's rule and costs nothing, and a future non-member send would fail
  noisily under either (a section mismatch).
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
  the list in order. v3: its `unsupported "NAPI polls of several peers in
  one softirq"` (`:462`; `task/d3-int:Env.lean:676`) **stays**, since
  `w7_two_napi` is dropped (16.2) and every kept class schedules one
  peer's NAPI per softirq (in `w7_budget_dead` B's items are `UNCRYPTED`
  in the ring and schedule nothing). A NAPI scheduled inside `wgReceive`
  (the `-EPIPE` arm) is polled in the same `runWorker .netRx` body, after
  the receive (2.6).

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
payload, opts}` or `inject_gso {messages}`, all on `SEND_FD`, prepared
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
  - `wg_xmit` gains optional `gso_size` (cmsg `UDP_SEGMENT`; v3: IPv4 only,
    dividing the payload — `validate_trace` refuses the rest, fail-noisy)
    and `pmtudisc` (`do` default, `probe`; set per op with `IP_MTU_DISCOVER`
    before the send and restored after; v3: no `dont`), and a payload up to
    the GSO classes' need (`MAX_PAYLOAD` raised to 2784 for `w4_gso_4_2`;
    `wg.py:357-362`'s MTU bound becomes a per-`pmtudisc` rule). v3 drops
    `connected` (no `SEND2_FD`, no `wg_connect`) and `multicast_loop`.
  - `wg_set_mtu {mtu}`: `SIOCSIFMTU` via `SEND_FD`'s ioctl (as `wg_up` uses
    `SIOCSIFFLAGS`, `guest.c:926-931`).
  - `wg_create` is unchanged (v3: no `IFLA_MTU`).
  - **`route_into_wg0` becomes MTU-aware for the MTU-0 class only** (2.3;
    v2 M5, v3 narrowed): it reads wg0's MTU (`SIOCGIFMTU`) and, below 68,
    expects the kernel's refusal of all four requests (IPv6 add `-EINVAL`;
    IPv4 add `-ENOBUFS` while the `in_device` is absent; the route adds'
    errnos from P-B), failing the trace on any other value as today. No
    kept class brings wg0 up with an MTU in [68, 1280).
  - `net_fixture` (already an optional trace field, `trace.py:73`) gains
    `routes: [{dst, mtu}]` for the route-MTU class; v3 drops `link_local`
    and the multicast `allowed_ips` additions.
  - `wg_batch {items: [...], wait_ms}`: section 5.5; its result carries the
    CQEs; an item may be `inject_gso {messages}` (a UDP GSO datagram of
    equal-size data messages to wg0's port, E §4's fan-out) for
    `w7_budget_dead`. `MAX_PAYLOAD` (32768, `guest.c:32`) and `line` (`:75`)
    grow to hold 1025 messages; `SO_RCVBUFFORCE` (8 MiB) on both listeners
    and `SEND_FD`, since the default `rmem_default` (`sock.c:287`, 212992)
    holds about 270 small datagrams and the bulk tiers deliver up to 1025;
    **`SO_SNDBUFFORCE` (8 MiB) on `SEND_FD`** (2.7; v2, M1).
  - **Wire opcodes** for `wg_set_mtu` and `wg_batch` are placeholders
    `OP_SET_MTU` and `OP_BATCH` here; the coordinator allocates them at the
    interface commit (`trace.py` `OPCODES`, 15-17 are L's and 18 is
    `wg_flood`). v3: no `OP_CONNECT`.
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
  - **P-A's result** [AGENT 2026-10-12, task/w7-harness, the W9 oracle,
    `scripts/wg-w7-tier-probe.py`]: the trace `corpus/w7-tier/w7_ring_wrap`
    (a session, a 1-item `xmit` batch, a 1024-item one, observe, get) is
    the measurement. At the 1024-item batch the PC child writes 668,793
    task and 855,131 remote words, the comparison child 384,517 task and
    512,276 remote records (1,538,068 and 2,049,104 words): 1M words
    overflows there (`empty_or_full_kcov`), 2M would leave 2 % headroom,
    so `CAPACITY` (`guest.c`) and `KCOV_CAPACITY` (`trace.py`) are 4M
    words, 32 MiB per area, one constant rather than a per-trace value.
    The rows stay small because they are deduplicated (805 and 827 PCs,
    30,176 and 14,518 records at that operation; 3.3 MB for the trace's
    two children), so the chunk's 16 MiB output limit and the one-bulk-
    trace-per-chunk rule stand unchanged. The kernel's own work is cheap:
    `io_uring_enter` returns all 1024 completions (`res` 1 each) in
    0.12 s and the workers finish inside a 600 ms wait. What exceeded the
    4.5 s bound was the guest: its sort-based deduplication (2.3 s in the
    PC child, 7 s in the comparison child at that operation), replaced by
    a hash-table pass in area order with the same rows, and the serial
    console (about 0.5 MB/s under TCG against 2.4 MB of rows for the
    comparison child at that operation), so a bulk trace's rows are now
    held in memory and written after its last operation. With both, the
    children end 2.91 s and 3.02 s after `wg_up` with `wait_ms` 200 and
    1000; **1000 ms is the full-ring tier's `wait_ms` default** (600 ms
    sufficed for the workers). The tier is go.
  - **What Linux does at the wrap** (the same probe; the mirror did not
    run): every send completes at the socket; the device counters after
    the batch read `tx_packets` 1025 and `tx_bytes` 65652 = the initiation
    (148) + the staged keepalive (32) + 1023 data messages of 64 bytes,
    `tx_errors` 0 and `tx_dropped` 0, and `wg_get` reports the peer's
    `tx_bytes` 65652. So **1023 of the 1025 items went out and two were
    dropped silently**, not the one the ring counterexample (17.16 on
    `task/rings`) predicts; the PCs the 1024-item batch executes beyond
    the 1-item one include the producer's wrap (`ptr_ring.h:115`), the
    failed produce's unlock, `wg_packet_create_data`'s `-EPIPE` arm
    (`send.c:323`, the DEAD enqueue at `queueing.h:185,188`) and
    `wg_packet_tx_worker`'s dead-packet `kfree_skb_list` (`send.c:278`),
    in all four runs. The second drop is for the ring stream to explain
    against the section records (the remote area holds 2048 kind-300/301
    records and 28 kind-302 reschedules at that operation).
- **`harness/noise.py`:** the IPv4 GSO segment builder (headers, checksums,
  ids 0…n−1) anchored to the mirror's `Env.xmitPackets` by `#guard` vectors
  and to Linux by the A1 bytes; batches of data messages under a session
  with counter lists, and the GSO inject datagram of equal-size messages.
  v3: no fragment builders.
- **Generator** (`scripts/wg-w47-corpus.py`, classes; the corpus
  `corpus/wireguard/w4_*.json`, `w7_*.json`):
  v3: **the minimal set** of section 16 — 5 W4 classes and 11 W7 classes
  (v2 had 35 and 15). Each W4 class names the WireGuard line, decision or
  outcome it alone reaches (16.1).
  - `w4_gso_4_2`: after a session, one IPv4 GSO xmit, `gso_size` 1392,
    payload 2784 (two full-size segments); expect two ciphertexts with ids
    0 and 1. Reaches `.xmitNotGso` false, `.xmitGsoError` false and a
    two-iteration `.xmitWalk` under a session, and anchors the GSO
    geometry on the smallest instance before `w4_gso_trim` depends on it.
  - `w4_gso_trim`: no session; two GSO xmits of 128 (`gso_size` 8, payload
    1024), a third of 1; expect `tx_dropped = 128`; then the offline response
    flushes 129 80-byte messages. Alone reaches the trim loop
    (`.xmitStagedTrimIter` true, device.c:211-214) and the `tx_dropped`
    counter; 128 segments need `gso_size ≤ 511` (v2, m4).
  - `w4_route_mtu_probe_4`: route MTU 1300 via `net_fixture.routes`,
    `PROBE`, payload 1392 (len 1420): alone reaches **the `len > mtu` arm**
    (`.padOverMtu` true, send.c:154-155, padding 8). The clamp is not taken
    here and needs no class (2.3; v2, M8).
  - `w4_set_mtu_1300`: `wg_set_mtu 1300` under a session, then an IPv4 xmit
    of a 1300-byte packet and a keepalive (`wg_set` with
    `persistent_keepalive`: the keepalive rule of section 4), `wg_observe`.
    Alone checks the data flow `dev->mtu → PACKET_CB->mtu` at both read
    sites (device.c:173, send.c:232) with a value other than 1420: the
    xmit pads to 1300 (0 bytes) where a constant 1420 would pad to 1312
    (12 bytes). Both families stay up.
  - `w4_set_mtu_0` [AGENT 2026-10-07, delegated, 13.6(a)]: `wg_set_mtu 0`
    under a session, the keepalive (**`.padNoMtu` true**, send.c:145-146),
    `wg_down`, `wg_up` (**`.openHasInet` false and `.openHasInet6` false**,
    device.c:39, 47; the MTU-aware fixture expects the four refusals),
    `wg_observe`. Terminal. The three outcomes are reached by no other kept
    class; P-B confirms the kernel accepts MTU 0 and fixes the errnos.
  - `w7_multi_rx_{2,8}`: a batch of n valid data messages under a session.
    n = 2 alone reaches `wg_prev_queue_dequeue`'s "more remain" arm
    (queueing.c:91-95) and `.prevQueuePeeked` true (the poll between items
    leaves item 2 peeked, 2.8); n = 8 is the instance where per-item yields
    and two-item polls occur (W7-M3, M5, M9 are conclusive only with one).
  - `w7_multi_tx_{2,8}`: a batch of n xmits under a session: the tx-side
    twins (`tx_queue`'s dequeue arms, the tx worker stopping at an
    `UNCRYPTED` head with it peeked, send.c:269-272).
  - `w7_multi_tx_dead` (with stream A's `skbCowHead` steer on the k-th
    call): alone reaches the encrypt worker's `DEAD` break mid-list
    (send.c:299-302) and the tx worker's `kfree_skb_list` of a multi-skb
    `DEAD` item (`:277-278`), which D2 mirrored but never exercised
    (`d2-sprint.md:294`).
  - `w7_mixed`: injects and xmits in one batch (encrypt and decrypt workers
    both queued): the one class where `Batch.lean` orders two different
    deferred units by their section starts.
  - `w7_full_rx_1025`, `w7_full_tx_1025` (gated on P-A, 13.4): the
    `-ENOSPC` arms (`.enqueuePeerQueueFull` true, queueing.c:74) on each
    side; keepalive messages / 1-byte payloads; `rx_bytes`/counters as
    observables.
  - `w7_epipe_rx`, `w7_epipe_tx`: **stretch** — two sessions (two steered
    handshakes; `STEER_MAX = 64` entries suffice), the ring at 1024: the
    `-EPIPE` arms (`.enqueueRingFull` true; `.dataEpipe` true with the
    in-softirq poll of a single `DEAD` entry; send.c:322-323's `DEAD` list).
  - `w7_budget_dead` [AGENT 2026-10-07, delegated, 13.5(a)]: **stretch** —
    B's 1024-item batch fills the decrypt ring, then one `inject_gso` of 64
    data messages for A in the same `io_uring_enter`: `.rxPollBudgetDone`
    true and `net_rx_action`'s repoll (section 10).
  - Dropped in v3 (16.1, 16.2): `w4_gso_{4,6}_3`, every IPv6 GSO class, the
    non-divisor `gso_size` classes, `w4_gso_{4,6}_128`, `w4_gso_4_48`,
    `w4_route_mtu_probe_6`, `w4_set_mtu_1279`, `w4_create_mtu_1279`,
    `w4_frag_{4,6}_connected`, `w4_frag_4_unconnected`, `w4_gso_4_connected`,
    `w4_mcast_{4,6}`, `w4_mcast_{4,6}_nomember`, `w4_mcast_noloop`,
    `w4_mcast_noloop_v4opt`, `w4_linklocal_6`; `w7_multi_rx_4`,
    `w7_multi_rx_dead`, `w7_multi_tx_4`, `w7_two_napi`.
  - Isolation: bulk traces one per chunk (as E's under-load traces), since
    their wall time is a large share of the 4.5 s bound (`TRACE_BOUND_MS`,
    `task/d3-int:Leanux/Env.lean:55`).

## 7. Observables

- **A1 bytes** at the listener: every GSO segment's ciphertext (ids,
  lengths, the software UDP checksum, `CSUM_MANGLED_0`; `CHECKSUM_NONE` so
  no `skb_checksum_help` rewrite), padding under the route MTU and under
  a device MTU of 1300, the 32-byte keepalive at MTU 0. v3: no fragments,
  no multicast/link-local sources.
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
it). v3: the W4 list follows the kept classes (16.1); mutants whose only
rejecting trace was dropped are listed as dropped, so that nothing claims
evidence the corpus no longer carries.
- **W4-M1** GSO segment ids not incremented (all 0) — `w4_gso_4_2` bytes
  (and `w4_gso_trim`'s 128).
- **W4-M2** the GSO last segment padded to `gso_size` — **dropped** (needs a
  non-divisor `gso_size`, beyond the boundary).
- **W4-M3** segment checksum left as the pseudo-header partial —
  `w4_gso_4_2` bytes.
- **W4-M4** `skb_checksum_help` applied to a `CHECKSUM_NONE` packet — bytes
  (the field would change) and the `.encChecksumPartial` operand.
- **W4-M5** trim before splice replaced by trim after (drops the new
  segments) — `w4_gso_trim`'s `tx_dropped` and the flushed counters.
- **W4-M6** trim at `≥ 128` — `w4_gso_trim` (`tx_dropped` 129 vs 128).
- **W4-M7** `mtu` from `dev->mtu` instead of `dst_mtu` —
  `w4_route_mtu_probe_4` padding bytes.
- **W4-M8** `last_unit %= mtu` dropped — same trace: without the modulo,
  `min(1300, ALIGN(1420, 16) = 1424) = 1300` and `1300 − 1420` is 0 in the
  mirror's `Nat` (Linux's unsigned wrap would be caught by `skb_put`), so
  the mutant pads 0 where Linux pads 8: bytes (v2, M8 corrects v1's
  "padding 8 vs clamp").
- **W4-M9** keepalive padded with `Device.mtu` ignored (`!mtu` arm) —
  `w4_set_mtu_0` A2 operands (bytes equal: honest).
- **W4-M10** `wg_open`'s `dev_v6` (or `dev_v4`) constant true —
  `w4_set_mtu_0` A2 at the `wg_up`.
- **W4-M11** fragment 2 given a UDP header / wrong offset — **dropped**
  (fragmentation is beyond the boundary).
- **W4-M12** fragment ident not from `inet_id` — **dropped** (same).
- **W4-M13** multicast loop modelled for a non-member group — **dropped**:
  no kept trace sends to a non-member group, so the `{224.0.0.1}`
  correction (2.4) is a kernel-rule fix without a rejecting trace, stated
  as such; a future non-member send fails noisily under either rule.
- **W4-M14** the loop keyed on the IPv4 `MC_LOOP` bit — **dropped** (same).
- **W4-M15** the IPv6 fragment id as record + 1 or from a kind-110 site —
  **dropped** (same as M11).
- **W4-M16** (v3) `Device.mtu` constant 1420 after `wg_set_mtu` —
  `w4_set_mtu_1300` bytes: a 1300-byte packet pads 0 under the device's
  MTU and 12 under the constant (`min(1420, 1312) − 1300`).
- **W7-M1** `-ENOSPC` tested after the ring produce — `w7_full_tx_1025` A2
  (and the `-EPIPE` decision taken).
- **W7-M2** the 1025th item sent anyway — `w7_full_*` counters.
- **W7-M3** `peeked` ignored (re-dequeue) — `w7_multi_rx_2`: the peeked
  item is lost (`rx_bytes`, inner datagrams), A2 `.prevQueuePeeked`.
- **W7-M4** `tailIsStub` never reset (the re-stub arm skipped) — A2 on
  `w7_multi_*` (the dequeue decisions).
- **W7-M5** the tx worker continuing past an `UNCRYPTED` head — a hidden
  mismatch on the trace where the encrypt worker yielded (recorded), else
  inconclusive, reported.
- **W7-M6** DEAD break not breaking (remaining packets encrypted) — `w7_multi_tx_dead` (needs A's `skbCowHead` steer on the k-th call; else this mutant waits for A).
- **W7-M7** polls serving one peer when two are pending — **dropped** with
  `w7_two_napi` (16.2); the environment keeps its `unsupported` for two
  pending NAPIs, so the arm is fail-noisy rather than modeled.
- **W7-M8** `-EPIPE` item not marked DEAD on receive — `w7_epipe_rx`
  (stretch): the poll would deliver it.
- **W7-M9** the scheduler ignoring per-item resched records (D1-M15's
  bulk form) — any `w7_multi_*` trace with a yield.
- **W7-M10** (stretch, under 13.5's repoll option) the poll continuing past
  `budget` or `napi_complete_done` called after a full poll —
  `w7_budget_dead` (section 10): the second NET_RX section is unexpected
  or missing.

Controls: the phase-1 commuting detector on synthetic record streams (a
`.reschedTx` inside an open encrypt section with ring items must be
`unsupported`; the same with the ring empty must pass; and the same shape
with the units swapped, a `.reschedEncrypt` nested under an open tx section
with a `CRYPTED` head, must be `unsupported` — the generic form, v2 M7);
**domain controls for the boundary** (v3): one trace each for a `dont`
xmit above the route MTU, an IPv6 `gso_size` xmit, and a non-dividing
`gso_size`, expected `unsupported` (so the exclusions are fail-noisy in the
mirror, not silently absorbed by the harness); the per-section operand
agreement of 13.2 on a synthetic two-poll trace whose Linux operands take
(c') in the second poll only (must pass under the two-run rule, and must
fail if the two runs disagree outside the NET_RX sections); and the
measurement probes of section 12 re-run on any new kernel.

## 9. Out of scope (fail-noisy), and why

| Item | Why |
|---|---|
| P5 arms: `wg_prev_queue_dequeue`'s `tail != head` (queueing.c:96-97, 105), concurrent producer mid-enqueue | SMP or in-region preemption |
| P9: a poll using its budget (receive.c:483-484) | **built** in the stretch tier (`w7_budget_dead`, section 10; 13.5(a)) |
| `net_rx_action`'s squeeze (`netdev_budget` 300, 2 jiffies) and `__do_softirq`'s restart limit | at most 128 segments per datagram: two polls of 64; `unsupported` beyond (fail-noisy) |
| A device MTU of 0 (`.padNoMtu` true, `.openHasInet` false) | **built** as the terminal class `w4_set_mtu_0` (13.6(a)); MTUs in [1, 68) and [68, 1280) reach nothing it does not and are not generated |
| A batch item deferred by io_uring (`-EAGAIN`, poll-arm or io-wq) | avoided by `SO_SNDBUFFORCE`; a deferral fails on `wg_batch`'s CQE result (5.5) |
| **Beyond the WireGuard boundary** (v3, [USER 2026-10-07]; each `unsupported` in the mirror, fail-noisy): inner fragmentation (`DONT` above the route MTU, any sender), the connected sender and its ident/txhash draws, the IPv6 Fragment id, outer fragmentation, IPv6 GSO, a non-dividing `gso_size`, the IPv6 route MTU (`mtu6`), `IFLA_MTU` at creation, device MTUs other than 1300 and 0, multicast classes (IPv4 non-member, IPv6, the loop controls), link-local destinations | no WireGuard line, decision or outcome of their own (16.1); the IP-stack facts stay as record in 2.1, 2.3-2.5 |
| Unconnected `DONT` fragmentation; `IP_PMTUDISC_WANT`/`OMIT`/`INTERFACE` | the ident over a boot-random bucket (3); K1 deferred under the boundary rule |
| More than 128 GSO segments, `gso_size + 28 > fragsize` | the stack returns `-EINVAL`/`-EMSGSIZE` before `wg_xmit` (`udp.c:988-995`) |
| GSO plus fragmentation (`DONT` with `gso_size`) | `cork->gso_size` sets `mtu = IP_MAX_MTU` (`ip_output.c:992`), no fragments; nothing new, and beyond the boundary |
| `IS_ERR(skb_gso_segment)`, `encrypt_packet` failures mid-list without A | allocation failures: stream A's capture and steering |
| IPv6 extension headers, IPv4 options on transmit | W6 |
| `-EPIPE`, the budget arm | the stretch tier (two sessions); the mirror arms are built, the traces follow integration |
| Two NAPIs in one `net_rx_action` | v3: dropped (16.2) — an environment arm with no WireGuard line of its own; `napiSoftirq` keeps its `unsupported` for two pending NAPIs |
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
2-jiffy limit stay unreachable (section 9). **Decided 13.5(a)** [AGENT
2026-10-07, delegated]: built, in `Batch.lean`, on the stretch tier. The
GSO inject that fans the 64 messages is the one receive-side IP-stack
mechanism v3 keeps (E §4's `udp_rcv_segment` fan-out), since without it
the arm is unreachable on one CPU.

## 11. Risks

- **Low — W4 bytes.** Every W4 fact is checked by ciphertext bytes; a wrong
  segment checksum, id or padding fails noisily on the first trace.
- **Low — the environment's stack model** (v3: IPv4 GSO segmentation with
  equal segments, the route MTU, the device MTU's teardown flags; no
  fragment geometry, no source selection). Each fact is verified once by a
  trace before the generator relies on it (D2's method: `w4_gso_4_2`
  before `w4_gso_trim`); the `#guard` vectors tie `noise.py` and
  `Env.xmitPackets`.
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
- **Medium — the per-section operand agreement** (13.2, option (ii)
  approved [USER 2026-10-07]): the (c') ambiguity no longer bounds the
  item count, but the check change is new code in `check.py` (section
  tagging of mirror branches, section partition of Linux's comparison
  records, the two-run independence test). Its control (section 8) and the
  D2/D3 replays (every recorded trace must still agree, with
  `NAPI_PLACEMENTS_MAX` gone) bound the risk; if the independence test
  ever fails on a real trace, the placement is not independent and the
  trace fails noisily rather than passing.
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
  m5), and the full-ring tier's go/no-go (13.4). Done 2026-10-12 as a
  Linux-only run of the tier's first trace on the standard guest rather
  than a throwaway C probe; the results are in section 12.
- **P-B** fixture facts (v3, narrowed): `ip maddr show wg0` (the IPv4 set
  `{224.0.0.1}`, M3); a `PROBE` send over a `mtu 1300` route reaching
  `wg_xmit` unfragmented (one ciphertext of 1460 bytes); whether `ip link
  set wg0 mtu 0` is accepted, and **the errnos of `route_into_wg0`'s four
  requests at MTU 0** (the IPv6 add `-EINVAL`, the IPv4 add `-ENOBUFS`, the
  route adds). Dropped from P-B: `ip -6 addr show wg0` (the D2 §2
  correction stands on `addrconf.c` alone and no kept class depends on
  it), `ip -6 maddr`, the MTU-1279 errnos.
- **P-C** (offline, no VM): the **nesting proxy** of 5.4 over the existing
  D1/D2 check runs' records (the phase-1 counter itself is zero there by
  construction, M7).

**Interface commit** (on `task/w47`, **only after D3+L+A+E are integrated**
on the base): `Device.mtu`, `inet4Dev`, `inet6Dev`; `PrevQueue`;
`Kernel.napiPollList`; the new decisions (`wg_xmit.gso_error`,
`wg_xmit.staged_trim_iter`, `wg_prev_queue_dequeue.*`); **no new hidden
site**; the op schemas (`wg_xmit` `gso_size`/`pmtudisc`, `wg_set_mtu`,
`net_fixture.routes`, `wg_batch` with `inject_gso` items and its CQE
result, `kcov_capacity`, `wait_ms`); the wire opcodes allocated by the
coordinator (placeholders `OP_SET_MTU`, `OP_BATCH` until then, section 6);
`DEVICE_MTU` removed; the two new environment files created empty with
their hooks in `Env.lean`.

**Streams and file ownership** (the two streams meet in `Env.lean` only at
the hooks, so neither edits the other's file):
- **T — transmit shapes (W4):** **`Leanux/Env/IpStack.lean`** (new:
  `xmitPackets` for IPv4 GSO and the IPv4 route MTU, the `{224.0.0.1}`
  set, `setMtu` consequences, and the boundary `unsupported`s; `Env.lean`
  hooks `xmitPackets`, `xmitMulticastLoop` and the `wg_set`/`wg_up`
  keepalive rule of section 4), `Leanux/WG/Device.lean` (`wgXmit`
  GSO/trim/`wgOpen`), `Leanux/WG/Send.lean` (`sendKeepalive`),
  `harness/noise.py` (the GSO segment builder), `harness/guest.c` W4 ops
  and fixture (`wg_xmit` options, `wg_set_mtu`, `route_into_wg0` MTU-aware
  at MTU 0, `SO_SNDBUFFORCE`).
- **B — bulk (W7):** `Leanux/WG/Send.lean` (`enqueuePerDeviceAndPeer`),
  `Leanux/WG/Data.lean` (`txWorker`), `Leanux/WG/RxData.lean` (`rxPoll`,
  `enqueuePerPeerRx`), `Leanux/WG/Receive.lean` (`consumeData` arms),
  **`Leanux/Env/Batch.lean`** (new: `batch`, `napiSoftirq` with the
  per-peer list and the repoll (13.5(a)), the `condResched`
  generalization, the generic phase-1 detector; `Env.lean` hooks `batch`
  and the worker runners), `harness/guest.c` `wg_batch` (from `wg_flood`,
  with `inject_gso` and the CQE result), `kcov_capacity`.
- **H — harness, generator, corpus, evidence, and the check change:**
  `scripts/wg-w47-corpus.py`, `corpus/wireguard/w4_*`, `w7_*`,
  `scripts/wg-mutants.py` patterns W4-M* and W7-M*, `evaluator/
  napi_orders.py` extension, the probes and their results note, and
  **`evaluator/check.py`'s per-section operand agreement** (13.2 (ii),
  approved): mirror branches tagged with their NET_RX section ordinal
  (`leanux-model` output, one field), Linux's comparison records
  partitioned by the remote stream's section blocks, two mirror runs on
  an operand mismatch with the independence test, `NAPI_PLACEMENTS_MAX`
  and `napi_placements` removed, `napi_irq_before_put` becoming the
  all-false/all-true pair; every recorded D2/D3 chunk replayed.

**Effort** (v3 against v2, by what each stream builds; the user asked for
the change, not hours):

| Stream | v2 | v3 |
|---|---|---|
| T mirror/environment | GSO ×2 families with short last segments, fragmentation ×2 families, `inet_id` + 3 hidden sites + `wg_connect`, route MTU ×2 (`mtu6`), 2 membership sets + loop control, link-local source selection, `setMtu` with 3 thresholds, `IFLA_MTU` | IPv4 GSO with equal segments, IPv4 route MTU, the `{224.0.0.1}` set, `setMtu` with the 0/68/1280 flags, 6 boundary `unsupported`s |
| T harness | `wg_xmit` ×5 options, `SEND2_FD` + connect, `wg_set_mtu`, `wg_create.mtu`, fixture: routes, link-local, MTU-aware at 3 thresholds, 2 sockopts; `noise.py` GSO + fragment builders | `wg_xmit` ×2 options, `wg_set_mtu`, fixture: routes, MTU-aware at MTU 0, 1 sockopt; `noise.py` GSO builder |
| B | as v2 plus the repoll; minus the multi-peer `napiSoftirq` | unchanged otherwise |
| H corpus | 35 W4 + 15 W7 classes | 5 W4 + 11 W7 classes, plus 3 boundary domain controls |
| H mutants | W4 ×15, W7 ×10 | W4 ×10 (M1, M3-M10, M16), W7 ×9 (M1-M6, M8-M10) |
| H check | — | the per-section operand agreement (13.2 (ii)) |
| Probes | P-A, P-B ×6 facts, P-C | P-A, P-B ×4 facts, P-C |

**Integration:** the full check with bulk traces one per chunk, the W4/W7
mutants and controls, the phase-1 counter report, the report and signoff.
Phase 2 (step workers) and the stretch tier are separate decisions after
integration.

## 13. Decisions for the user

**Decided, 2026-10-07** (v3). Provenance per item; the v2 texts below are
kept as the record of the options and reasoning.
- Scope — [USER 2026-10-07]: "we should stop at the boundary of wireguard
  (unless this breaks important things)". The IP stack is modeled only
  where it drives WireGuard code paths or is needed to predict WireGuard's
  observable behaviour. Applied in section 16.
- 13.1 — [AGENT 2026-10-07, under delegated authority]: the connected
  sender was the recommendation, but **no K1 and no connected sender**:
  fragmentation is beyond the boundary (16.1), so neither is built. K1
  deferred under the boundary rule.
- 13.2 — [USER 2026-10-07]: **option (ii) approved** — per-NET_RX-section
  operand agreement, two mirror runs, the independence check. Stream H
  (section 12).
- 13.3 — [AGENT, delegated]: as recommended (generic phase 1; nesting
  proxy; phase 2 on the W7 corpus).
- 13.4 — [AGENT, delegated]: as recommended (full-ring tier gated on P-A
  after `SO_SNDBUFFORCE`).
- 13.5 — [AGENT, delegated]: **(a)**, P9 in the stretch tier
  (`w7_budget_dead`, the repoll in `Batch.lean`).
- 13.6 — [AGENT, delegated]: **(a)**, `wg_set_mtu 0` as a terminal class.
  v3 then drops `w4_create_mtu_1279` and `w4_set_mtu_1279`, since the
  MTU-0 class reaches `.openHasInet6` false too (16.1).
- 13.7 — [AGENT, delegated]: as recommended; v3 adds that the `{224.0.0.1}`
  correction has no rejecting trace (8, W4-M13).

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
- **Added in v3:** `task/d3-int:evaluator/generate.py` 302 (the random
  xmit destinations include `e0000001`), `task/d3-int:evaluator/
  test_model_replay.py` 34-38 (a no-peer `wg_xmit` to 224.0.0.1 with its
  one NET_RX section); `task/census:docs/2026-10-04-d2-data-plane.md` 329
  (staged flushes of 1-4 packets: the multi-skb item), 335 (tampered tags:
  the poll's `DEAD` arm); `task/census:docs/2026-10-04-d2-sprint.md` 294
  (the multi-skb `DEAD` break never exercised).

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

## 16. Revision v3 — WireGuard boundary and decisions

**The rule** [USER 2026-10-07]: "we should stop at the boundary of
wireguard (unless this breaks important things)". Applied as: a class is
kept iff it reaches a WireGuard line, decision or outcome (in
`drivers/net/wireguard/`, as the mirror's A2 decisions name them) that no
other kept class reaches, or it is needed so that the observations of kept
traces stay predictable; the IP stack is modeled only as far as the kept
classes' bytes and records need. Everything else is marked **excluded:
beyond the WireGuard boundary**, as a fail-noisy `unsupported` in the
mirror (section 9) and a `validate_trace` refusal in the harness, with
three domain-control traces (section 8) showing the `unsupported` fires.
The verified kernel facts of the dropped classes stay in sections 2.1,
2.3-2.5 as record.

### 16.1 W4, class by class

| Class (v2) | WireGuard line / decision / outcome it alone reaches | Verdict |
|---|---|---|
| `w4_gso_4_2` (gso_size 1392, payload 2784) | `.xmitNotGso` false, `.xmitGsoError` false (device.c:176-187), a two-iteration `.xmitWalk` (`:189-204`) under a session; `.encChecksumPartial` false. The multi-skb encrypt/tx walks themselves are D2's (staged flushes of 1-4 packets, `d2-data-plane.md:329`). | **kept** — also the geometry anchor for `w4_gso_trim` |
| `w4_gso_trim` (2×128 at gso_size 8, then 1) | the trim loop `.xmitStagedTrimIter` true (device.c:211-214), `tx_dropped`; the 129-skb item of the flush | **kept** |
| `w4_gso_{4,6}_3`, non-divisor sizes, `w4_gso_{4,6}_128`, `w4_gso_4_48`, every IPv6 GSO class | nothing beyond the two above: segment count and size do not change a WireGuard branch (padding's arms are D2's); a short last segment and IPv6 are IP-stack geometry | **dropped** (boundary) |
| `w4_route_mtu_probe_4` (route MTU 1300, PROBE, len 1420) | `.padOverMtu` true (send.c:154-155) | **kept** |
| `w4_route_mtu_probe_6` | the same line; needs the IPv6 route MTU (`mtu6`) | **dropped** (boundary) |
| `w4_set_mtu_1300` | the data flow `dev->mtu → PACKET_CB->mtu` at device.c:173 and send.c:232 with a value other than 1420 (W4-M16: bytes 0 vs 12 bytes of padding); both families stay up | **kept** |
| `w4_set_mtu_0` (13.6(a)) | `.padNoMtu` true (send.c:145-146), `.openHasInet` false (device.c:39), `.openHasInet6` false (`:47`) | **kept**, terminal |
| `w4_set_mtu_1279`, `w4_create_mtu_1279` | `.openHasInet6` false only — reached by `w4_set_mtu_0`; `IFLA_MTU` and the 1280 threshold add IP-stack teardown modeling and fixture expectations for nothing further | **dropped** (redundant with the MTU-0 class) |
| `w4_frag_{4,6}_connected`, `w4_frag_4_unconnected`, `w4_gso_4_connected` | two ordinary `wg_xmit` calls; `.encChecksumPartial` false (GSO's); a second packet without a UDP header that WireGuard never parses. The ident draws (`.txHash`, `.inetIdSeed`, `.ipv6FragId`) are IP-stack hidden inputs | **dropped** (boundary; K1 deferred) |
| `w4_mcast_{4,6}`, `w4_mcast_{4,6}_nomember`, `w4_mcast_noloop`, `w4_mcast_noloop_v4opt` | none: `wg_xmit` sees an ordinary packet, the peer lookup reads only the destination, multicast draws no ICMP; the loop copy, TTL, hop limit and `sk_mc_loop` are IP-stack behaviour. What the existing corpus needs — the NET_RX section of a no-peer `wg_xmit` to `224.0.0.1` (`generate.py:302`) — is the IPv4 set `{224.0.0.1}`, kept in `xmitMulticastLoop` | **dropped** (boundary); the set kept |
| `w4_linklocal_6` | none (D2's IPv6 xmit lines); source selection is IP-stack | **dropped** (boundary) |

Kept W4: `w4_gso_4_2`, `w4_gso_trim`, `w4_route_mtu_probe_4`,
`w4_set_mtu_1300`, `w4_set_mtu_0` — 5 of 35. Together they reach every W4
WireGuard outcome of section 1: `.xmitNotGso`/`.xmitGsoError`/`.xmitWalk`
(n > 1), the trim, `.padOverMtu` true, `.padNoMtu` true, `.openHasInet`
false, `.openHasInet6` false, `.encChecksumPartial` false, and the
`Device.mtu` data flow. IP-stack modeling retained for them: IPv4 GSO
geometry with equal segments (ids, lengths, UDP checksums); `dst_mtu` =
route MTU for an IPv4 `PROBE` send; `Device.mtu` with the 68/1280 flags
and the fixture's refusals at MTU 0; the `{224.0.0.1}` set. Dropped
modeling: fragment geometry and the three hidden sites, `inet_id`, the
connected sender, IPv6 GSO, short last segments, `mtu6`, `IFLA_MTU`, the
IPv6 membership set and loop control, link-local source selection.

### 16.2 W7, checked against the rule

W7 is WireGuard queue behaviour (queueing.c/h, the workers' loops,
`wg_packet_rx_poll`) and stays in scope. Per class:

| Class (v2) | WireGuard line / decision / outcome it alone reaches | Verdict |
|---|---|---|
| `w7_multi_rx_2` | `wg_prev_queue_dequeue`'s "more remain" arm (queueing.c:91-95); `.prevQueuePeeked` true; the poll stopping at an `UNCRYPTED` head | **kept** |
| `w7_multi_rx_8` | no new line; the instance with per-item yields and two-item polls (W7-M3, M5, M9 conclusive) | **kept** (scheduling evidence) |
| `w7_multi_rx_4` | nothing between 2 and 8 | **dropped** |
| `w7_multi_rx_dead` | the poll's `DEAD` arm is D2's (tampered tags); a `DEAD` entry mid-queue takes no new line | **dropped** |
| `w7_multi_tx_2`, `w7_multi_tx_8` | the tx-side twins (`tx_queue` dequeue arms; the tx worker stopping at an `UNCRYPTED` head, send.c:269-272) | **kept** |
| `w7_multi_tx_4` | nothing between 2 and 8 | **dropped** |
| `w7_multi_tx_dead` (with A) | the encrypt worker's `DEAD` break mid-list (send.c:299-302) and `kfree_skb_list` of a multi-skb `DEAD` item (`:277-278`): "mirrored, but never exercised" (`d2-sprint.md:294`) | **kept** |
| `w7_mixed` | no new line; the one class ordering two deferred units by section starts in `Batch.lean` (needed for the environment's ordering rule) | **kept** |
| `w7_full_rx_1025`, `w7_full_tx_1025` | `.enqueuePeerQueueFull` true (queueing.c:74, `-ENOSPC`) on each side | **kept** (P-A gated) |
| `w7_epipe_rx`, `w7_epipe_tx` | `.enqueueRingFull` true (`-EPIPE`); `.dataEpipe` true and the in-softirq poll of a `DEAD` entry; send.c:322-323's `DEAD` list | **kept** (stretch) |
| `w7_two_napi` | none: `wg_packet_rx_poll` is per peer; two NAPIs in one `net_rx_action` is `dev.c`'s list, an environment arm | **dropped**; `napiSoftirq` keeps its `unsupported` |
| `w7_budget_dead` (13.5(a)) | `.rxPollBudgetDone` true (receive.c:483-484) and the repoll | **kept** (stretch) |

Kept W7: 11 of 15. The receive-side GSO inject (`inject_gso`) is the one
IP-stack mechanism kept for W7, because `w7_budget_dead` is unreachable on
one CPU without it.

### 16.3 What the rule changed elsewhere

- Hidden inputs (3): no new site; the fragment rows are record only; K1
  deferred; K3 moot (13.2 (ii) approved).
- Mirror/environment (4, 5.2): `xmitPackets` models IPv4 GSO and the IPv4
  route MTU and answers `unsupported` to the rest; no `Sender.inetId`;
  `napiSoftirq` keeps its multi-peer `unsupported`; the keepalive rule for
  `wg_set`/`wg_up` stays (the MTU classes need it).
- Harness (6): `wg_xmit` keeps `gso_size` and `pmtudisc ∈ {do, probe}`;
  no `connected`, `multicast_loop`, `SEND2_FD`, `wg_create.mtu`,
  `link_local`; the MTU-aware fixture only at MTU 0; `wg_batch` gains
  `inject_gso`; opcodes `OP_SET_MTU`, `OP_BATCH`.
- Mutants (8): W4 keeps M1, M3-M10 and adds M16; drops M2, M11-M15. W7
  drops M7. Three boundary domain controls and the 13.2 (ii) control
  added.
- Plan (12): T shrinks to the IPv4 GSO/route-MTU/MTU rules; H gains the
  `check.py` per-section operand agreement; P-B drops three facts; the
  effort table compares v2 and v3.
- Corrections to record at integration (13.7) are unchanged, with the
  note that the `{224.0.0.1}` fix has no rejecting trace.

**Size change:** classes 50 → 16 (W4 35 → 5, W7 15 → 11); hidden sites
3 → 0; harness ops/options: `wg_xmit` options 5 → 2, `wg_connect` and
`wg_create.mtu` gone, one new item kind (`inject_gso`); W4 mutants 15 →
10, W7 10 → 9; P-B facts 6 → 4.

## 17. Results [AGENT 2026-10-11, stream T]

Branch `task/w47` on the interface commit (`task/interface` b11145f: main
with housekeeping and the `Env.lean` split). Stream T is built and
validated at suite level; streams B and H are not started (17.5).

### 17.1 What was built (sections 4, 6, 16.1)

- **Mirror.** `Device.mtu`, `inet4Dev`, `inet6Dev` replace `WG.DEVICE_MTU`;
  the keepalive reads the device's MTU (send.c:232) and `wg_open` reads the
  two devices (device.c:39, 47). `wgXmit` takes the environment's packet
  list and `dst_mtu`: the GSO arm (`.xmitNotGso` false, the new
  `.xmitGsoError` at device.c:181 over `EnvSite.skbSegment`), the walk
  with the one `mtu` per call, and the trim loop (`.xmitStagedTrimIter`,
  device.c:211-214, `tx_dropped` per iteration) in place of the
  `unsupported` of `.xmitStagedOverflow`, which it replaces (same line).
  `setMtu` mirrors `dev_set_mtu` as a cut: `-ERANGE` above `max_mtu`, the
  MTU written, the inet6_dev down below 1280 and the in_device below 68
  (no decision in `dev.c`: the file is not anchored, and the kept classes
  use 1300 and 0).
- **`Env/IpStack.lean`.** `XmitOpts` (`gsoSize`, `probe`, the route MTU
  from `World.routes`); `xmitPackets` returns one `wg_xmit` call's packets
  and `mtu`, or the sender's errno (`-EMSGSIZE` above `cork->fragsize`,
  which is `dst_mtu` under `DO` and `dev->mtu` under `PROBE`; `-EINVAL`
  above 128 segments); IPv4 GSO with equal segments (`gsoSegment`: ids
  0..n−1, DF, per-segment header and complete UDP checksums,
  `CHECKSUM_NONE`); a payload at most `gso_size` long is one ordinary
  packet (udp.c:1005: no GSO flag). Beyond the boundary, `unsupported`:
  IPv6 GSO, a short last segment, an IPv6 route MTU or PROBE.
  `multicastLoops` is the `{224.0.0.1}` set (2.4), called from
  `Env.xmitMulticastLoop`. `MAX_XMIT_PAYLOAD4/6` take the MTU.
- **Harness.** `wg_xmit` packets carry `gso_size` (IPv4, 2-128 whole
  segments) and `pmtudisc` ("do" or "probe"); the guest sends with a
  `UDP_SEGMENT` cmsg and sets `IP_MTU_DISCOVER` per send, restoring `DO`
  after it; `wg_set_mtu {mtu}` is `SIOCSIFMTU` on the sender's socket;
  `net_fixture: {"routes": [{family, dst, mtu}]}` adds host routes into wg0
  with `RTAX_MTU` at every `wg_up` (wire: the `T` line's sixth field and
  `R` lines); the fixture is MTU-aware (2.3): below 68 the IPv4 address add
  is `-ENOBUFS`, below 1280 the IPv6 add `-EINVAL`, and the route adds
  `-ENODEV`, expected exactly, which the `w4_set_mtu_0` run confirmed (the
  fixture fails the trace on any other value: this is probe P-B's measurement
  of the four errnos). `SO_SNDBUFFORCE` (8 MiB) on the sender (2.7);
  `MAX_XMIT_PAYLOAD` 2784. `noise.gso_segments` builds the segments
  (checked in `harness/test_noise.py`).
- **Corpus** (`scripts/wg-w47-corpus.py`): the five kept classes of 16.1,
  and the three boundary domain controls (`corpus/w47-controls`,
  `scripts/wg-w47-controls.py`: the mirror alone, `--domain`, places each
  outside the domain with the stated reason).
- **Mutants** W4-M1, M3-M10 and M16, on the `w4_` subset.

### 17.2 Deviations and judgment calls [AGENT]

- **The keepalive of the MTU classes comes from the persistent-keepalive
  timer through `wg_advance`**, not from `wg_set`/`wg_up` under a session
  (section 4's keepalive rule). That rule changes `Env.runSendWorkers`'
  crypt-work treatment in `Env.lean`, which belongs to the dispatch-order
  stream at integration (docs/2026-10-11-interface.md), so stream T does
  not touch it. The timer route reaches the same two read sites
  (send.c:232 with 1300 and with 0, `.padNoMtu` true) and costs one
  `wg_advance` per class; the rule stays as described for the coordinator.
  `w4_set_mtu_0` turns the keepalive off before the down, so the up after it
  stages nothing and sends no second initiation.
- **`MAX_BRANCHES`** (`evaluator/protocol.py`, a shared surface) is raised
  from 4096 to 32768: the trim class's 129-packet flush reports 2766
  branches in one operation and 4307 in the trace. The guest's output limit
  still bounds the whole.
- **The placeholder wire opcode is 25** (`OP_WG_SET_MTU`, named for the
  guest-defines test), outside the reservations 20-24; the coordinator
  allocates the real code. `wg_batch` (stream B) needs a second code.
- `.xmitGsoError`'s site is an `EnvSite` (assumed success, as L's and E's
  sites) rather than an `AllocSite`: `skb_segment`'s allocations are not in
  an armed range (A's inventory covers WireGuard's own sites).
- The sender's `-EMSGSIZE`/`-EINVAL` are returned as results (22 and 90
  join `wg_xmit`'s semantic errnos) rather than `unsupported`, since the
  trace contract already refuses the shapes that would produce them.

### 17.3 Validation

All on the A oracle (`kernel-net-choice-a`, identity `c79e3e0c…`), under
`capped`, at `d0f27e1`:
- Unit tests (`evaluator.test_evaluation`, `harness.test_trace`,
  `harness.test_wg`, `harness.test_linux`, `harness.test_noise`): 96 pass
  (the GSO segment builder and the wire header are new cases).
- Each `w4_*` trace alone against Linux: 5/5 agreement (the first run of
  `w4_set_mtu_0` failed on the up's second initiation, fixed by turning
  the keepalive off before the down; the first run of `w4_gso_trim` failed
  the old 4096-branch bound).
- Suites `handwritten,wireguard` (`.artifacts/check/w47-suites`): **pass,
  187/187**, 9038 operand pairs, 3 output-limit chunk splits, no retries.
- Boundary controls (`scripts/wg-w47-controls.py`): 3/3 placed outside the
  domain with the stated reason.
- Mutants W4-M1, M3-M10, M16 on the `w4_` subset: **10/10 rejected**, no
  other outcome in any run. M1, M3, M4 (`w4_gso_4_2` and `w4_gso_trim`
  bytes), M7 and M8 (`w4_route_mtu_probe_4` bytes) are semantic
  mismatches; M5 and M6 are hidden mismatches at `w4_gso_trim`'s flush (the
  stop fails the chunk, so every trace of it is listed); M9, M10 and M16
  are control-flow mismatches at `w4_set_mtu_0` / `w4_set_mtu_1300`
  (M16 also a semantic mismatch: the 12 bytes of padding).

### 17.4 Wire opcodes needed from the coordinator

`wg_set_mtu` (placeholder 25) and, for stream B, `wg_batch` (the design's
`OP_BATCH`; `wg_flood` is 18 and would be subsumed).

### 17.5 Not done: streams B and H

- **B** (section 5, `Env/Batch.lean`, `wg_batch` from `wg_flood` with
  `inject_gso` and the CQE result, `PrevQueue` as data, the multi-item
  loops, the generic phase-1 detector, the repoll of 13.5(a), `kcov_capacity`,
  probe P-A) is untouched: the interface commit's `Batch.lean` holds only
  the shared runner pieces.
- **H**: the per-section operand agreement of 13.2 (ii) in `check.py`,
  `napi_orders.py`, the W7 corpus and mutants, the phase-1 controls.

## 17.6 Stream B: what was built [AGENT 2026-10-11, stream B]

Branch `task/w47` continued on the merge of the dispatch-order capture
(`task/dispatch-order-replay` f0827f7, option A [USER 2026-10-11]: the
oracle is now the `bb3e577d…` build, kind-307 queue records, the unit word
in section starts). The merge conflicted only in `scripts/wg-mutants.py`'s
run list (both lists kept).

- **`prev_queue` as data (5.1).** `PrevQueue` (`Leanux/WG/Types.lean`:
  `items`, `tailIsStub`, `peeked`) replaces the `tx_queue` and `rx_queue`
  lists; `Leanux/WG/PrevQueue.lean` mirrors `wg_prev_queue_dequeue`
  (queueing.c:80-106) with the five decisions `tail_is_stub` (84),
  `stub_empty` (85), `more_remain` (91), `tail_not_head` (96, true is P5:
  `unsupported`), `restub_next` (100), and `wg_prev_queue_peek` /
  `wg_prev_queue_drop_peeked` (queueing.h:143-155). `queueing.c` is
  anchored and `wg_prev_queue_dequeue` listed in `correspondence/kcov.json`.
  The two `queue->tail = next; atomic_dec(&queue->count); return tail;`
  blocks (92-94, 101-103) are one block in the build, attributed to
  101-103 and reached from both `if (next)` arms (observed: the first
  dequeue of a two-item queue covered 101-103), so neither true arm has
  witness lines of its own; `more_remain` true is the absence of 96 and
  `restub_next` true the absence of 105.
- **Multi-item queues (5.2).** The one-item `unsupported`s are gone from
  `enqueuePerDeviceAndPeer` and its receive twin; `-ENOSPC` and `-EPIPE`
  are returned there (the receive twin's `.enqueuePeerQueueFull` and
  `.enqueueRingFull` were `unsupported`); `consume_data`'s `-EPIPE` arm
  marks the packet `DEAD` through `enqueuePerPeerRx` (moved to
  `Receive.lean`), whose `napi_schedule` is polled in the same
  `net_rx_action` pass (`Env.pollScheduledInline`, 2.6). The tx worker and
  the NAPI poll peek through the queue; an `UNCRYPTED` head ends the run
  with the item peeked (`.txNotUncrypted` and `.rxPollNotUncrypted` are
  real branches now), and a producer's state update reaches a peeked item
  (`PrevQueue.updateFirst`: the oldest still-`UNCRYPTED` packet of its
  keypair, both queues being FIFO).
- **Scheduling (5.3, 5.4).** `Env/Batch.lean`: `runWorker` keeps the
  mirror's stack of open workers (`World.openWorkers`); `condResched` runs
  any of the encrypt, tx and decrypt workers whose section start is next
  and whose queue is non-empty, the tx worker being the unit the dispatch
  record names (`peekUnit`/`resolveUnit`, as `Env.runCryptWorkers`), and
  the decrypt worker through the runner the caller supplies
  (`Env.runDecryptAt`, carrying the switch fuel). Phase 1, generic: after
  the runnable starts, a nested unit that yields while any outer open
  worker still has queued work (`queuedWork`: the encrypt ring, the tx
  work queue or the tx worker's own queue with a sendable head, the
  decrypt ring, the handshake queue) is `unsupported "a worker yielded below
  an open worker with queued work (the mirror's stack order)"`.
- **`wg_batch` (5.5).** `Env.batch`: the items in order with no worker
  between them (an inject's `NET_RX` nested at the send, a transmit as
  `wg_xmit`'s packets through `xmitPackets`), each item's result as the
  operation's `cqes` (its length, or the sender's errno; the `io_uring_enter`
  result is the count submitted); then `afterBatch`: the queued units as
  the records order them (the decrypt worker, the crypt workers by their
  section starts, the handshake send workers), work left over `unsupported`.
  `Syscalls.wgBatch`, `Runner`'s `wg_batch {items, wait_ms}` with
  `inject {family, port, message}` and `xmit {packet}` items
  (`parsePacket` shared with `wg_xmit`). Not under `socketCallOn`: the
  io_uring descriptor plumbing is the fixture's, as the flood's.
- **Harness (6).** `harness/guest.c` `OP_WG_BATCH` 26 (`wg_set_mtu` keeps
  25; both allocated by the coordinator, docs/2026-10-11-interface.md):
  `batch_prep` builds the SQEs from the wire payload (per item kind,
  length, body) before the window, `batch_enter` is the one
  `io_uring_enter`, the completions are read from the CQ ring and reported
  as `LEANUX_WGBATCH` outside the window (a console write inside it added
  the tty's path to the coverage), the trace's `wait_ms` follows.
  `harness/trace.py` `validate_batch`/`encode_batch` (a batch transmit
  takes no `gso_size`/`pmtudisc`, refused); `harness/linux.py`
  `attach_batches`; `evaluator/protocol.py` `cqes`; `evaluator/check.py`:
  a batch trace runs in its own chunk (as the flood's), its `wait_ms` is in
  the guest budget, its decisions repeat per item (their later outcomes add
  to the set, as a repeatable decision's), and only the WireGuard files
  and the headers their paths inline are compared for the operation
  (`BATCH_FILES`: the file-table functions `io_uring_enter` and each send's
  `fget`/`fput` run are the fixture's).
- **Corpus and mutants (6, 8).** `w7_multi_rx_{2,8}`, `w7_multi_tx_{2,8}`,
  `w7_mixed` (`scripts/wg-w47-corpus.py`, the core tier; `wait_ms` 200 for
  two items, 400 for more); mutants W7-M3, M4, M5, M9 on the `w7_` subset.

### 17.7 Deviations and judgment calls [AGENT]

- **`Kernel.napiPollList`** (5.2) is not built: `napiSoftirq` keeps its
  `unsupported` for several peers' NAPIs (v3 dropped `w7_two_napi`), and
  every kept class schedules one peer's NAPI per softirq; the per-peer flag
  stays the poll list's one entry.
- **The repoll of 13.5(a)** (`net_rx_action` under a budget-exhausted poll)
  is not built: `.rxPollBudgetDone` true stays `unsupported` at the poll
  site (fail-noisy), pending the stretch tier's `w7_budget_dead`.
- **`kcov_capacity` per trace, `SO_RCVBUFFORCE`, `MAX_PAYLOAD` growth and
  probe P-A** are not done: the core tier's batches (2-8 items) fit the
  constants; the 1025-item tier needs them and P-A's measurement first.
- **The batch's decisions repeat per item** inside one operation. Rather
  than marking every receive- and transmit-path decision repeatable (which
  would loosen every other operation), the check treats a `wg_batch`
  operation's decisions as repeatable; their first occurrences keep the
  order check within each function.
- **Only the WireGuard files are compared for a `wg_batch` operation.** The
  io_uring submission's descriptor plumbing (`io_uring_enter`'s `fdget` of
  the ring, each send's `fget`/`fput` of the sender) is the fixture's and
  the mirror models none of it; the flood precedent skips the whole
  operation, this one keeps everything WireGuard runs per item.
- **`Env/Batch.lean`'s `condResched` takes the decrypt runner as an
  argument** (`runDecryptAt`), because the decrypt worker's hooks
  (`napiSoftirq`, `napiIrqExit`) live in `Env.lean` after the crypt runners;
  `runCryptWorkers` without one answers `unsupported` to a switch to the
  decrypt worker (only `inject` and `batch` supply it).
- **W7-M3 and W7-M5 are conclusive on this corpus**: the single-trace runs
  took the peeked arm (`wg_prev_queue_peek.peeked=1`: `w7_multi_rx_2` once,
  `w7_multi_rx_8` seven times, `w7_multi_tx_2` once, `w7_mixed` once) and
  the tx worker met an `UNCRYPTED` head in `w7_multi_tx_2`; resched records
  occurred in every multi-item run (5 in `w7_multi_rx_2`, 10 in
  `w7_multi_rx_8`), so W7-M9 is live.

### 17.8 Validation (stream B)

All on the dispatch-order oracle (`kernel-net-choice-q`, identity
`bb3e577d…`), under `capped`, at `e3b11a8`:
- Unit tests (`evaluator.test_evaluation`, `harness.test_trace`,
  `harness.test_wg`, `harness.test_linux`, `harness.test_noise`,
  `evaluator.test_model_replay`): 112 pass.
- Each `w7_*` trace alone against Linux: 5/5 agreement (53, 53, 77, 125 and
  125 operand pairs; `cqes` `[64, 64]` for the two-item receive batch). On
  the way: the guest did not parse the batch's payload (fixed), its
  completion report inside the window added the tty's path (moved out),
  and the merged dequeue block (17.6) was declared.
- Suites `handwritten,wireguard` (`.artifacts/check/w47b-suites`): **pass,
  192/192**, 9471 operand pairs.
- Mutants W7-M3, M4, M5, M9 on the `w7_` subset (5 traces each; the run's
  summary file was not written because the design doc was being edited
  while it ran, so the verdicts are read from each mutant's `report.json`):
  - **W7-M3 rejected** (4 `hidden_mismatch`, 1 agreement): the lost peeked
    item leaves its records unconsumed.
  - **W7-M4 rejected** (5 `mirror_invariant`): with the tail left off the
    stub the next dequeue finds no entry behind a non-stub tail and the
    mirror stops on its own invariant, before the `tail_is_stub` disagreement
    the design named; a verdict, but the weaker kind.
  - **W7-M5 rejected** (1 `mirror_invariant` on `w7_multi_tx_2`, 4
    agreement): the tx worker that continues past an `UNCRYPTED` head stops
    on an invariant of the send path; the other four runs never met one.
  - **W7-M9 survived** (5 agreement). The consumed-but-unrun switch is
    absorbed: the units it switched to are run by `afterBatch`'s
    record-ordered loop at their section starts, the yielding worker's
    pending stop is reconciled as a resumed rest, and within a `wg_batch`
    operation the repeated decisions are compared as outcome sets, so the
    tx worker meeting an `UNCRYPTED` head mid-list or not is invisible.
    The per-item order of those outcomes, or stream H's per-section
    bookkeeping, is what a rejecting form needs; listed, not claimed.

### 17.9 Not done: the rest of B, and H

- B: the 1025-item tier (`w7_full_*`, W7-M1, M2; P-A, `kcov_capacity`,
  `SO_RCVBUFFORCE`, `MAX_PAYLOAD`), `w7_multi_tx_dead` (W7-M6, with A's
  `skbCowHead` steer), the stretch tier (`w7_epipe_*`, `w7_budget_dead`,
  the repoll, W7-M8, M10), `Kernel.napiPollList`, the phase-1 detector's
  synthetic-stream controls (section 8), phase 2 (step workers) as a
  decision on the phase-1 count.
- H: the per-section operand agreement of 13.2 (ii) in `check.py` and the
  `napi_orders.py` extension (polls per decrypt-worker run, items per poll,
  the (a)/(b/c) split), the phase-1 counter report.


## 17.10 Stream H: what was built [AGENT 2026-10-11, stream H]

Branch `task/w47` continued on the merge of `task/dispatch-order`
`dbe9e0e` (the PENDING-bit model of queued units, `a333927`; one conflict,
`World.openWorkers` beside the new `pendingWork`; `Env/Batch.lean`'s
`condResched` takes `resolveUnit`'s new signature). Commit `fbf2826`.

- **The per-section operand agreement (13.2 (ii), T1).** The mirror stamps
  every step with the ordinal of the NET_RX section it ran in
  (`Step.netRx`; `World.netRxSections`/`netRxSection`, set in
  `Env.runWorker` for `.netRx` and cleared at its end, reset per operation;
  the model output's `section` field, accepted by `evaluator/protocol.py`).
  The guest tags every remote comparison record with the dispatch-section
  blocks it occurred in: `split_hidden` numbers the blocks by their start
  records in area order (a section's records reach the remote area as one
  block at its stop, nested blocks before their enclosing one, so the
  running count is the block and the stop record ends it), and
  `print_records` prints each distinct remote record once, in sorted
  order, with its blocks as ranges (`"1-3,7"`, a fifth element;
  `harness/linux.py` accepts it). `evaluator/check.py`: `netrx_sections`
  maps each operation's `net_rx_action` blocks of the comparison child to
  the mirror's ordinals by the start records' sequence numbers;
  `record_blocks` parses the ranges; `section_agreement` is the rule, run
  on an operand mismatch of a trace with open placements after one more
  mirror run with every placement before the put (`napi_irq_before_put`
  all true). `NAPI_PLACEMENTS_MAX` and `napi_placements` are gone; the
  report's `napi_irq_placements` is now `napi_before_put_sections`, the
  NET_RX ordinals taken from the before-put run, per trace.
- **The rule, as the data corrected it.** The design said the (c')
  placement changes only the operands inside the poll's section. The first
  replay of `rx_roam_v6` (one open poll) showed it also changes the
  enqueue's own `wg_peer_put`, the branch right after the poll outside any
  section (3 → 2 with the poll after it, 2 → 1 with the poll before it),
  and it moves the section among the branches outside any section. So the
  runs are compared per section (each NET_RX section's branches, and the
  branches outside any, each in their own order): the control flow must be
  the same; the operands may differ only in `count` NET_RX sections and
  `count` adjacent runs of branches outside them, paired in order; each
  pair (the poll's span) agrees with Linux under one run as a whole, the
  section's branches against that section's block and the put's against
  the records outside the NET_RX blocks; everything else agrees under
  both. More differences than open polls fail the trace: the independence
  premise failed.
- **A second correction from the first live run.** The guest's
  first-occurrence marking compared record content only, so the worker's
  put behind the poll, identical in bytes and address to the poll's put
  (`wg_peer_put` is one function), was dropped; records are now distinct
  per block. The naive per-block printing then made a flood's 520 identical
  NET_RX sections print 520 copies, past the rekey bound of the four
  `e_underload_*` traces; hence the ranges.
- **`evaluator/napi_orders.py`** reads the function word of the 16-byte
  start record (the dispatch-order capture widened it; before this the (a)
  and (b/c) counts were both zero on the new kernel), counts the NET_RX
  polls per decrypt-worker run (`polls_per_run`), and the phase-1 nesting
  proxy (5.4, P-C): a resched record in a unit nested in another unit, per
  (outer, inner) pair (`nested_yields`), with the trace and operation; the
  CLI adds the report's phase-1 rejections.

### 17.11 The phase-1 counter report (5.4, 13.3)

On the dispatch-order oracle (`kernel-net-choice-q`, identity `bb3e577d…`):

| Run | Nesting proxy (resched in a nested unit) | Phase-1 rejections |
|---|---|---|
| `w47b-suites` (stream B's suite run, 192 traces) | 6: `handshake_receive_worker > tx_worker` 3, `> encrypt_worker` 3 | 0 |
| `w47h-suites`, first run of H (192) | 9: `handshake_receive_worker > encrypt_worker` 6, `> tx_worker` 2, **`encrypt_worker > tx_worker` 1** | **1: `w7_multi_tx_8`** (operation 4, at peer.c:227) |

The proxy occurs in the receive worker's nested units of ordinary traces
(`d2_rx_deliver_v6`, `d2_xmit_after_session`, `l_delete_after_clear_work`,
`w4_gso_trim`, …) without a rejection: the outer receive worker had no
queued work. The one rejection is the design's case exactly: the tx worker
yielded under the encrypt worker while the encrypt ring still held items
(an 8-item transmit batch), fail-closed. In two runs of the five-trace W7
core tier that is 1 of 10 bulk-trace runs; the design makes phase 2 (step
workers) a decision on this count ("a few percent of bulk traces"), so it
goes to the coordinator with the 1025-item tier, where the rate can only
grow.

### 17.12 Deviations and judgment calls [AGENT]

- The poll's span (17.10) replaces the design's "everything outside the
  sections agrees" test, which the data refuted; the independence test is
  now the count of differing spans against the open-poll count, and the
  per-section control-flow equality.
- Remote comparison records are printed in sorted order with block ranges,
  not in first-execution order: no consumer depends on their order
  (`operand_agreement` matches any record at the condition; the harness
  checks duplicates only).
- `polls_per_run` and the (a)/(b/c) split come from the records; the items
  per poll do not (the mirror's `wg_prev_queue_peek.peeked` outcomes in the
  report's decision table are the measure, as 17.7 used them).
- **W7-M9's rejecting form is not built.** The per-section bookkeeping
  partitions *operands* by NET_RX section; W7-M9's consumed-but-unrun
  switch is visible only in the per-item order of the tx worker's
  outcomes, which the batch operation's repeatable decisions compare as
  sets. A rejecting form needs per-dispatch-section coverage (the guest
  tagging PCs by block as it now tags comparison records, and the check
  comparing each section's decisions as its own sequence): a new check
  rule, for a later step. The mutant is **rejected live anyway** under the
  PENDING-bit model of the dispatch-order capture (17.13): the switch it
  skips leaves the tx unit pending in the mirror, so the encrypt worker's
  next item queues nothing and Linux's re-queue record (kind 307) stays
  unconsumed, a hidden mismatch (2 of the 5 `w7_` runs; the others had no
  mid-loop yield). It is listed as rejected by that mechanism, not by the
  per-item order the design named.

### 17.13 Validation (stream H)

All on the dispatch-order oracle, under `capped`:
- `lake build leanux-model` passes; unit tests (the six modules, with
  `test_section_agreement_two_runs`: a synthetic two-poll trace whose
  second poll came before the put passes with section 2 under the
  before-put run, and a mixed span, a wrong poll, a difference outside the
  spans, a control-flow difference and a record outside its block all
  fail; `test_netrx_sections_from_the_remote_rows`): 114 pass.
- Live, single traces: `rx_roam_v6` (one open poll), `d2_rx_window_boundary`,
  `d2_rx_in_order`, `e_underload_flood` (op 3: 6378 comparison records,
  3825 tagged, the widest in blocks 1-520; cmp child 1.79 s of the 4.5 s
  bound, as before the change) all pass.
- The recorded runs replayed through both placement runs and
  `section_agreement` (`.artifacts/h/section_driver.py`, not committed):
  `rx_roam_v6` 41 operand pairs, no problems, the after-put run (101
  branches differ between the runs: the poll's and the put's operands, and
  the poll's position); `d2_rx_window_boundary` 65 and `d2_rx_in_order` 68
  pairs, no open poll, no problems.
- Suites `handwritten,wireguard` (`.artifacts/check/w47h-suites`, at
  `fbf2826`): **pass, 192/192**, 9471 operand pairs, no retries, no
  before-put sections (no operand mismatch with an open poll occurred, so
  the two-run rule was exercised by the replays above, not live). The run
  before the commit (same code but the first guest tagging, 17.10) was
  187/192: the four `e_underload_*` past the rekey bound from the
  per-block copies, and `w7_multi_tx_8` the phase-1 rejection of 17.11.
- Mutants W4-M1, M3-M10, M16 and W7-M3, M4, M5, M9 (`scripts/wg-mutants.py`,
  `.artifacts/check/mutants-summary.json`): **14/14 rejected**, no other
  outcome. W4 as in 17.3; W7-M3 4 `hidden_mismatch`; W7-M4 5
  `mirror_invariant`; W7-M5 1 `mirror_invariant`; **W7-M9 2 `hidden_mismatch`**
  (17.12), where stream B's run had it survive.

### 17.14 The NAPI poll at a worker's yield [AGENT 2026-10-12, int-w]

`w7_mixed` operation 4 on the integration branch: the decrypt worker gave
up the CPU at its first `cond_resched` and the records then show the
NET_RX section of the pending NAPI poll (ksoftirqd ran it: D2's order
(a)), and only after it the encrypt and tx workers' sections, all before
the decrypt worker's resumption. `condResched` switched to a crypt worker
only when its start record was the very next record, so the poll's section
blocked the switch and the resumed decrypt worker met the encrypt worker's
start where it expected its next item's read (a hidden mismatch, site 44
for site 6; 1 of 1 alone, 1 of 1 in the combined suite). The rule
(`Leanux/Env/Batch.lean` `condResched`, its docstring): a NET_RX section
the records place at the yield, with a NAPI poll pending, runs first by the
existing NET_RX rules (`Env.napiSoftirq`, passed in as `runNetRx`), and the
switch to the crypt worker whose start follows is still taken; any other
record at the yield stays with the resuming worker, whose next read it must
be. No kernel change, no new instrument. The same recording also shows the
tx worker yielding below the suspended decrypt worker, which resumed with
its ring item before the tx worker's rest: that is phase 1's case (5.4),
`unsupported` fail-closed under this rule as before, and phase 2's to
model.

Validation (dispatch-order oracle `bb3e577d…`, under `capped`): `lake build
leanux-model`; unit and replay tests 118 pass (D2-M12's pattern follows the
new `condResched` signature); `w7_mixed` alone three times: 3/3 agreement,
the first with the order the gap showed (poll, encrypt, tx, then the
decrypt worker's second item); the `w7_` subset: 4 of 5 agreement,
`w7_multi_tx_8` the phase-1 `unsupported` of 17.11 (a tx yield below the
encrypt worker with ring items, scheduling-dependent); the combined suite
`handwritten,wireguard` (`.artifacts/check/int-w-suites-2`): **pass,
238/238**, 11153 operand pairs, no retries, `w7_multi_tx_8` agreeing in
that run.
