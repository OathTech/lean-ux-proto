# Correspondence audit: `Leanux/WG/Device.lean` against `device.c` [AGENT, independent audit, 2026-10-13]

A reading audit of `Leanux/WG/Device.lean` (397 lines, at `2c7a076`) against
`drivers/net/wireguard/device.c` (Linux 6.12.110, pristine) and the C it
calls on the modelled device paths. No build, no checker run. Line numbers
are the C file's and the Lean file's at that commit.

Classes, from the brief: (1) a C choice point with no mirror choice point and
no declared cut; (2) a mirror choice point out of the C's order; (3) an arm
the mirror resolves silently where the C branches on state; (4) data of a
different shape; (5) a hidden input the C reads that the mirror does not
consume there; (6) something the mirror does that the C does not. **O** =
could change an observable outcome on a trace; **I** = internal
correspondence only. An exclusion recorded in a design document with its
reason is listed in section 3, not counted as a finding.

## 1. Inventory

| C function | device.c | Mirror (Device.lean) | Status |
|---|---|---|---|
| `wg_open` | 31-62 | `wgOpen` 49-62, `wgUp` 68-72 | mirrored, order exact |
| `wg_pm_notification` | 64-95 | none | declared out: census P1, L 2.5 (no `PM_SLEEP`) |
| `wg_vm_notification` | 97-113 | none | declared out: census P2, L 2.5 (no `VMGENID`) |
| `wg_stop` | 115-135 | `wgStop` 79-98, `wgDown` 102-104 | mirrored, order exact; ring drain declared (L 8) |
| `wg_xmit` | 137-234 | `wgXmit` 301-355 | mirrored; findings X1-X8 |
| `lookup`, `wg_allowedips_lookup_dst` | allowedips.c 127-147, 356-364 | `lookup` 28-37, `lookupDst` 40-44 | mirrored; retry declared (census P5) |
| `wg_check_packet_protocol` | queueing.h 70-74 | `wgXmit` 303 | two fixed outcomes: X1 |
| `wg_destruct` | 242-270 | `wgDestruct` 257-278 | mirrored, order exact; finding D1 |
| `wg_setup` | 274-307 | `wgSetup` 185-186 | mirrored as a fresh `Device`; finding U1 |
| `wg_newlink` | 309-400 | `wgNewlink` 206-244, `wgCreate` 249-254 | mirrored; unwind declared (census W11) |
| `wg_netns_pre_exit` | 409-428 | `netnsPreExit` 382-395 | mirrored, order exact (W8 3.3) |
| `wg_device_init/uninit` | 434-472 | none | declared out: L 2.6 (boot, `__exit`) |
| `dev_set_mtu` (a cut) | net/core/dev.c 9061-9122 | `setMtu` 369-372, `MAX_MTU` 361 | finding M1 (observable), M2 |
| `wg_ratelimiter_*` | ratelimiter.c 55-221 | 109-179 | mirrored; bucket reduction declared (L 1118-1125) |

## 2. Findings

### 2.1 `wg_open` (31-62) and `__dev_open`

No finding. The `dev_v4`/`dev_v6` tests (39, 47) are `.openHasInet`/`.openHasInet6`
on `Device.inet4Dev`/`inet6Dev` (51-52); `wg_socket_init`'s error (52-53) is
`.openSocketError` (56); the peer loop (54-58) reports `.openPeersIter` per
peer plus the exit, with `wg_packet_send_staged_packets` then the
`persistent_keepalive_interval` test (`.openKeepalive`, 60) in the C's order.
`wgUp` sets `running` before `wgOpen` and clears it on failure, as
`__dev_open` does with `__LINK_STATE_START` (dev.c:1551-1557). The devconf
writes at 44-45 and 48 are IP-stack state below the boundary (section 3).

### 2.2 `wg_stop` (115-135) and `__dev_close_many`

| # | C | Lean | Class | What | Effect |
|---|---|---|---|---|---|
| S1 | 122-128 | 85 | 6 | (retired 2026-10-14, a no-op) `requireNotPending` before each peer's purge: a fail-noisy dispatch-timing guard the C has no counterpart for. | I. Keep: it is the hidden-input rule for a queued handshake worker, and it stops rather than guesses. |

The per-peer sequence purge, `wg_timers_stop`, `wg_noise_handshake_clear`,
`wg_noise_keypairs_clear` (next, previous, current), `wg_noise_reset_last_sent_handshake`
(its coarse-clock record) is in the C's order (86-90); the ring drain
(130-131) stops `unsupported` when nonempty and reports `.stopDrainIter`
false otherwise (94-96, declared, section 3); `handshake_queue_len = 0` and
`wg_socket_reinit(NULL, NULL)` follow (97-98).

### 2.3 `wg_xmit` (137-234), with `lookup` and `wg_check_packet_protocol`

| # | C | Lean | Class | What | Effect |
|---|---|---|---|---|---|
| X1 | 147; queueing.h:73 | 303-304 | 3 | `real_protocol && skb->protocol == real_protocol` is reported as two fixed `true` outcomes (`.checkProtoParsed`, `.checkProtoMatches`), so `.xmitBadProtocol` is constant false and its `err` arm (148-150, 230-233: `tx_errors`, no ICMP) is `unsupported "unreachable"`. The C decides on the version nibble of the packet (`ip_tunnel_parse_protocol`, ip_tunnel_core.c:1109-1120) and `skb->protocol`; the mirror holds `pkts` and `family`, and `Packet.protocol` (Send.lean:172-178) already derives the EtherType from that nibble. | I on the corpus (the sender's IP layer always agrees). A malformed `pkts` from the environment (`Env/Stack.reply4` builds bytes and `dst` separately) would pass silently instead of stopping. |
| X2 | 173 | 327 | 3 | `skb_valid_dst(skb)` reported as a fixed `true` (`.xmitValidDst`); `mtu` is the environment's `dst_mtu` argument. | I; declared (census P11, W4 2.3). Listed for completeness. |
| X3 | 176 | 329 | 4 | `skb_is_gso(skb)` (`gso_size != 0`) is decided by `pkts.length < 2`: the GSO flag is encoded in the list's length. Sound for the environment's segmentation (`xmitPackets`, IpStack.lean:169-204: a payload at most `gso_size` is one ordinary packet, udp.c:1005; a longer one has at least two segments), but a proxy, not the C's operand. | I. |
| X4 | 192-194 | 340 | 3 | `skb_share_check` reported false per segment; its `GFP_ATOMIC` clone outcome is never consumed. | I; declared (census P11: no AF_PACKET). |
| X5 | 225-233; dev.c `__dev_queue_xmit`'s `rcu_read_unlock_bh` | 313-316 | 2 | The ICMP error's loopback NET_RX section is consumed inside `err` (`loopbackSend`, 315) before `tx_errors++` (316) and before `wg_xmit` returns; in the C the softirq runs after `wg_xmit` returned and the counter moved. State.lean:174-200 records the reason (the softirq runs at the region's end). | I: nothing in the section reads `tx_errors`; the record order is the same. |
| X6 | 153; allowedips.c:360, 362 | 318 | 4 | The lookup key is the argument `addr` (the sendto destination), not `ip_hdr(skb)->daddr` / `ipv6_hdr(skb)->daddr` read from `pkts`' bytes as the C's data flow has it. | I: the environment builds the header from `addr`; a `reply4` with a `dst` that disagrees with its `bytes` would not be caught. |
| X7 | 181-183 | 332-334 | 3 | `IS_ERR(segs)` returns the fixed `-ENOMEM`; the C returns `PTR_ERR(segs)`, which is `-ENOMEM` for an allocation failure inside `skb_segment` but `-EINVAL` for the header checks of `inet_gso_segment`/`udp4_ufo_fragment`. The value is the sender's `sendto` errno (udp.c `udp_send_skb` returns `ip_send_skb`'s error). | I: the fixture's segments are well formed, and the header checks are below the boundary; only the allocation outcome (`envOk .skbSegment`) is in scope. |
| X8 | 137-234 | 329-355 | 6 | An empty `pkts` is accepted: the walk reports its exit, nothing is spliced, `sendStagedPackets` and `peerPut` still run. The C never enters without an skb. | I. An `invariant` would fail closed. |

Verified exact: the no-peer arm (154-162) with its `skb->protocol` debug
branches (`.xmitNoPeerInet`/`Inet6`, 320) and `err_icmp` without a put; the
endpoint-family test as the C's `&&` (166, 324); `err_peer`'s put before the
ICMP (325, 333); the GSO arm (176-187); the walk with the one `mtu` per call
(189-204, 338-342); the trim loop before the splice, one `tx_dropped` per
iteration, bounded so the false exit is always reported (211-215, 346-352);
`wg_packet_send_staged_packets`, the put, `NETDEV_TX_OK` (218-221, 353-355);
`tx_errors` once at `err` (231, 316). `lookup` (28-37): `swap_endian`'s
choice on the runtime `bits`, `find_node`, `wg_peer_get_maybe_zero`, and the
`retry` as `unsupported` (declared, section 3). `lookupDst` (40-44) branches
on the family as the C does on `skb->protocol` (359, 361).

### 2.4 `wg_destruct` (242-270)

| # | C | Lean | Class | What | Effect |
|---|---|---|---|---|---|
| D1 | 255, 258 | 265-271 | 3 | The guard for work `destroy_workqueue` would run (265-267) checks the send, encrypt, tx, decrypt and clear queues but not the handshake ring, which the mirror then purges silently (271, mirroring `wg_packet_queue_free(&handshake_queue, true)`). A nonempty ring means `wg_packet_handshake_receive_worker` was queued and `destroy_workqueue(handshake_receive_wq)` (255) would have run it, after `wg_peer_remove_all`, before the purge. | I: unreachable, since `wgStop` stops `unsupported` on a nonempty ring (94-95) and a never-up device receives nothing. An `invariant` would keep the guard consistent. |

Order verified: `creating_net = NULL`, `incoming_port = 0`, `wg_socket_reinit`
(250-252, 259-260); `wg_peer_remove_all` (254, 261); the three
`destroy_workqueue` (255-257) as the guard plus `mayHaveSlept` (the rescuer's
`kthread_stop`); the queue frees (258-260); `rcu_barrier` (261, 272);
`wg_ratelimiter_uninit` (262, 273); the frees as `wg := none` (277).

### 2.5 `wg_setup` (274-307) and `wg_newlink` (309-400)

| # | C | Lean | Class | What | Effect |
|---|---|---|---|---|---|
| U1 | 305; 320, 348-359; register | 186 (`Device` defaults, Types.lean:386-500) | 4 | `wgSetup` builds the device with fields the C sets later: `inet4Dev`/`inet6Dev` true (the `in_device`/`inet6_dev` exist only from `register_netdevice`'s `NETDEV_REGISTER`, 367), `peerAllowedips.seq = 1` (`wg_allowedips_init`, 320), the three `last_cpu = -1` (`wg_packet_queue_init`, 348-359). `creatingNet` and `deviceUpdateGen` are explicitly zeroed (186) and set in `wgNewlink` (208, 211), as the C does. | I: nothing reads them between `wg_setup` and the point the C sets them, and a failed `newlink` frees the device (253). |
| N2 | 333-346, 348-361 | 216-223 | 5 | Each `alloc_workqueue` (the wq, its pwqs, the rescuer's kthread) and each `wg_packet_queue_init` (`ptr_ring_init`, then `alloc_percpu`, queueing.c:25-41) has several allocation outcomes; the mirror asks one `envOk` per C call. | I: A's domain; the first failure's arm is the same whichever allocation failed, and every failure after 326 is `unsupported` (section 3). |

Verified exact: the first failure returns `-ENOMEM` without unwinding (326-327,
212) and `wgCreate` frees the device as `rtnl_newlink` does (253); the order
`creating_net`, `wg_cookie_checker_init` (clock then random, cookie.c:19-26,
189-192), `device_update_gen = 1` (316-323, 208-211); the ten error tests in
the C's order (326-369, 212-238); `register_netdevice`'s ifindex from the
netns cursor and the two `neigh_parms_alloc` draws (237-242). `MAX_MTU`
(361) is `round_down(INT_MAX, 16) - 80` (297).

### 2.6 `wg_netns_pre_exit` (409-428)

No finding. `device_list` (one device) is `.preExitDevIter` (385, 395), the
creator test `.preExitCreator` on `creatingNet` (386), then carrier off,
`creating_net = NULL`, `wg_socket_reinit(NULL, NULL)`, and the peer loop
with `wg_socket_clear_peer_endpoint_src` (418-423, 389-394). `creatingNet :
Bool` stands for `creating_net == net`, sound because `Env.netnsCleanup`
(Env.lean:896-905) runs only in the foreign-creator mode (W8 3.3, section 3).
The linkwatch event is the environment's (W8b).

### 2.7 `dev_set_mtu` (`setMtu`, a declared cut on net/core/dev.c)

| # | C | Lean | Class | What | Effect |
|---|---|---|---|---|---|
| M1 | dev.c:9061-9075 | 370 | 3 | `dev_validate_mtu` returns **`-EINVAL`** for `new_mtu > dev->max_mtu` and for a negative `ifr_mtu` (the harness casts `(int)op->a`, guest.c:2393); the mirror returns **`-ERANGE`**. No patch in `kernel/patches/` touches `net/core/dev.c`. `evaluator/protocol.py:228-230` expects `{ENODEV, ERANGE}` for `wg_set_mtu`, so the arm is both wrong and never exercised: the corpus holds `w4_set_mtu_0` and `w4_set_mtu_1300` only. The design's statement (W4 doc 1786) carries the same value. | **O**: a trace with `wg_set_mtu 2147483553` (above `MAX_MTU` 2147483552), or any value of 2^31 or more, gets `EINVAL` from Linux and `ERANGE` from the mirror. |
| M2 | dev.c:9090-9094 | 370-371 | 3 | `dev_set_mtu_ext` returns 0 for `new_mtu == dev->mtu` before validating and before the notifiers; the mirror validates and rewrites unconditionally. | I: the current MTU is always within range, and the rewrite is idempotent. |

### 2.8 `wg_ratelimiter_init/uninit/gc_entries` (ratelimiter.c:55-221, lines 109-179)

| # | C | Lean | Class | What | Effect |
|---|---|---|---|---|---|
| R1 | 65-66, 71-72 | 152-156 | 3 | On the uninit walk (`work` NULL) the per-entry `if (!work \|\| expired)` is constant true and is folded into `.gcV4EntryIter`'s true span (65-67); the periodic run, where it branches on the clock, is `unsupported` (159, 161). | I; the bucket-0 reduction and the "not a dispatched unit" rule are declared (L 1118-1125; section 3). |

Verified exact: `++init_refcnt != 1` (160-161, 121); the cache and the two
table allocations with `--init_refcnt` and `-ENOMEM` on failure (163-182,
198-203; 118-124); the key drawn after the tables (184, 126);
`!init_refcnt || --init_refcnt` (208-209, 166-169); `table_size` 2048 as an
environment constant (109, L 2.1).

## 3. Declared cuts and exclusions verified (not findings)

- `wg_pm_notification`, `wg_vm_notification`: census P1, P2; L 2.5; D3 769.
- `wg_device_init/uninit`, the rtnetlink core (`-EEXIST`, `-ENODEV`): L 2.6, 2.4;
  Device.lean 11-15, 246-254, 280-295.
- `wg_check_packet_protocol`, `skb_valid_dst`, `skb_share_check` false: census
  P11 (no `CONFIG_PACKET`); X1 above is about the true outcome being asserted.
- `lookup`'s `retry` after a dying peer: census P5 (`unsupported`, line 35).
- `wg_stop`'s ring drain with a message queued: L section 8 "Not claimed"; `unsupported`, 94-95.
- `wg_newlink`'s unwinding arms (381-399): census W11, Device.lean 203-207
  (`unsupported` after a reported decision).
- `wg_netns_pre_exit` in the foreign-creator mode only, `creatingNet` as the
  pointer test: W8 3.3; the `-ENONET` of `wg_socket_init`: W8 2.2.
- The ICMP error path's own hidden inputs (`icmp_global_allow`'s jiffies and
  credit, `inet_peer_xrlim_allow`, the inetpeer allocation): W8/W9 doc 395-407
  (M7, W9-R); the mirror consumes the cut-site records and infers "sent" from
  the `icmpCredit` draw (314-315). Below the boundary.
- `wg_open`'s devconf writes (44-45, 48) and `wg_setup`'s features, flags,
  `netif_keep_dst` (277-303): IP-stack and netdev-core state; the
  `addr_gen_mode` consequence is recorded in W4 2.4.
- `wg_ratelimiter_gc_entries` reporting bucket 0 only, the periodic run
  outside the domain: L 1118-1125, Device.lean 131-143.
- `dev_set_mtu` as a cut with no decision in dev.c: W4 doc 1786.

## 4. Verdict

The module follows `device.c`'s shape closely: every choice point of
`wg_open`, `wg_stop`, `wg_xmit`, `wg_newlink`, `wg_destruct` and
`wg_netns_pre_exit` on a modelled path has a mirror decision at the C's line,
in the C's order, with the C's loop exits reported, and every arm the mirror
does not follow stops `unsupported` with a recorded reason; the per-peer
sequences of `wg_open` and `wg_stop`, `wg_xmit`'s error labels with their
`tx_errors` and `tx_dropped` counters, and the trim-before-splice are exact.
Counts by class: class 1, 0; class 2, 1 (X5); class 3, 6 (X1, X7, D1, M1, M2,
R1); class 4, 3 (X3, X6, U1); class 5, 1 (N2); class 6, 2 (S1, X8); 13 in
all, of which one (M1) can change an observable outcome and S1 is a guard
worth keeping. Fix first: **M1** (`setMtu` returns `-EINVAL` above `max_mtu`
and for a negative `ifr_mtu`, with `protocol.py`'s expected set and the W4
doc's sentence corrected, and one trace above `MAX_MTU` added so the arm is
exercised); **X1** (`wg_check_packet_protocol` decided from the first
packet's version nibble against `family`, via `Packet.protocol`, so the two
decisions are live and a malformed environment packet fails closed); **D1**
(an `invariant` on a nonempty handshake ring in `wgDestruct`, matching the
guard on the other queues), with X6 and X8 as the same kind of cheap
fail-closed tightening if a fourth is wanted.
