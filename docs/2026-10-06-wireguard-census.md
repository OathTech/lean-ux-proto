# WireGuard coverage census — 2026-10-06 [AGENT]

A read-only census by a Fable agent of the union of the branches `main`,
`task/d3-int`, `task/l-m`, `task/a1` and `task/e-b`, against
`drivers/net/wireguard` in 6.12.110.

The census works to the user's goal (2026-10-06): 100% of reasonable
single-CPU WireGuard. Everything in reach that can be differentially tested
gets built. Exclusions are only for profound reasons.

## Coverage

| State | Functions fully modeled | Lines |
|---|---|---|
| After integrating the current branches | 150 / 202 (74%); 24 partial, 21 declared cuts | ≈3,920 / 4,636 (≈85%) |
| After workstreams W1–W12 | ≈178 / 202 (≈88%) | ≈4,330 / 4,636 (≈93%) |

The ceiling is the remaining ≈300 lines, which are boot/exit code, RCU
callbacks, the crypto reference, unobservable code, the two dead notifiers,
and profound arms inside modeled functions.

## Profound exclusions (with evidence)

| | What | Why |
|---|---|---|
| P1 | `wg_pm_notification` | `CONFIG_PM`/`SUSPEND` are unset, so the registration is a stub (`suspend.h:473-478`) |
| P2 | `wg_vm_notification` | `VMGENID` needs ACPI, which is unset (`random.h:30-37`) |
| P3 | Module and boot code | WireGuard is built in, so `__exit` never runs |
| P4 | RCU callbacks | They only free memory and run outside any section |
| P5 | Concurrency recheck arms | They need SMP or in-region preemption: `lookup` retry, a stolen index, an unhashed replace, the rechecks, the dead-peer arms, `prev_queue tail != head` |
| P6 | Send-side `REKEY`/`REJECT_AFTER_MESSAGES` | The limit is 2^60 |
| P7 | Probability and size bounds | 64 index collisions, 256 jitter rejections, `MAX_PEERS` 2^20, ratelimiter `max_entries` 16384 within 1 s |
| P8 | Constants the stack validates | `prepare_skb_header`, the `wg_receive` NULL arms, nla-policy exact lengths |
| P9 | NAPI budget exhaustion | A poll sees at most one packet on one CPU |
| P10 | A VLAN-tagged skb | The tunnel parser returns only IP/IPv6/0 |
| P11 | `wg_check_packet_protocol`, `skb_valid_dst`, `skb_share_check` false in `wg_xmit` | Only AF_PACKET produces these, and `CONFIG_PACKET` is unset. A config change would lift this. |
| P12 | The exact depth of a flood, the trylock path, a full ring | Scheduling-driven. A capture of `handshake_queue_len` would lift this. |
| P13 | Kworker items pending across syscalls | Not deterministically reachable. The within-syscall case is W3. |
| P14 | Structurally dead arms | `hmac` long key, null ephemeral, `!peer` in `add`, the `WARN_ON`, too many fragments |

## In-reach workstreams

| WS | Scope | Size |
|---|---|---|
| W1 | Netlink completeness: ifindex, `-EBADR`, `-EOPNOTSUPP`, protocol version, missing or malformed attributes, unknown flags, odd endpoint attributes, scope/flowinfo | S |
| W2 | Multi-message dump: skb budget, `-EMSGSIZE`, cursors, `allowedips_seq`, dead cursor | M |
| W3 | `wg_peer_remove` with queued handshake work (REMOVE_ME in the same message; send worker inline at the flush) | S-M |
| W4 | Transmit shapes: UDP GSO, staged trim, padding arms (route MTU, `SIOCSIFMTU`, `IFLA_MTU`), `Device.mtu` as state, multicast/link-local bytes | M |
| W5 | Receive shapes: outer TOS and ECN set_ce/set_ect1, silent inner drops, scoped IPv6 source, outer DS and tstats observed | S-M |
| W6 | Inner-packet stack reactions: options/ext headers, reassembly with `ip_expire`, TCP RST, ICMP unreachable re-entering wg0 | M-L |
| W7 | Bulk and multi-item queues: io_uring batches of data and xmits, multi-item rings, `prev_queue` peeked state, two-peer NAPI, transmit fragmentation, full rings | L |
| W8 | netns exit, `-ENONET`, `-EPERM` | M-L |
| W9 | `socket.c` `send4`/`send6` routing as decisions | M |
| W10 | DoS completion: the ratelimiter (in progress), GC at idle points, a flood then down, cookie freshness and secret rotation | S-M |
| W11 | Allocation completion: the `wg_newlink` unwind, the cookie-reply `alloc_skb` | S |
| W12 | Several peers' timers of one kind in one pass | S-M |
| W13 | A second device (wg1); wg0↔wg1 as a real peer pair | L |

## Integration notes

- `purgeStagedPackets` is defined on both d3-int and l-m.
- The "D3 stream M: not yet" stubs on l-m and e-b are replaced by d3-int.
- `Env.wgUp` differs between L and main.
- `kcov.json` omits `make_cookie`, `wg_socket_send_buffer_as_reply_to_skb`,
  `wg_socket_init` and `send4`/`send6`.

## Kernel changes that would lift exclusions (need user approval)

- A capture of `handshake_queue_len` (P12).
- `CONFIG_PACKET=y` (P11).
- `CONFIG_PM_SLEEP` with an s2idle/RTC wake instrument (P1).
