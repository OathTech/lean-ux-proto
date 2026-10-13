# Correspondence audit: `Leanux/WG/Netlink.lean` and `NetlinkDump.lean` against `netlink.c` — 2026-10-13 [AGENT, independent audit]

Read-only audit of the mirror of `drivers/net/wireguard/netlink.c` (Linux
6.12.110, `.deps/linux`) at `main` 2c7a076, against the principle in
AGENTS.md ("Behavioral mirror at the thin-layer altitude"). Method: every
conditional, loop, early return and error arm of the eleven C functions on
the modelled paths was walked in C order and its mirror counterpart located;
the helpers each path calls (`peer.c`, `noise.c`, `cookie.c`, `socket.c`,
`allowedips.c`, `curve25519.h`) were read where the netlink path's shape
depends on them. Declared exclusions (`docs/2026-10-06-w1-w2-netlink.md`,
section 5; `docs/decisions.md` 2026-10-12; the module notes) are verified
and listed, not reported. The transport below the driver (af_netlink.c,
genetlink.c) is the environment by that decision and is not audited.

File keys: N = `Leanux/WG/Netlink.lean`, D = `Leanux/WG/NetlinkDump.lean`,
P = `Leanux/WG/Peer.lean`, R = `Leanux/WG/PeerRemove.lean`,
S = `Leanux/WG/Socket.lean`, A = `Leanux/WG/AllowedIps.lean`,
K = `Leanux/WG/Keypair.lean`. C lines are `netlink.c` unless named.

## 1. Per-function tables

Status: `match` (same choice point, same position, same arms); `declared`
(a cut or constant with a recorded reason, section 3); `F<n>` (a finding,
section 2). The policy tables (22-50) have no mirror choice point by design
(P8: the validator rejects what the policy would; design 2.2, 5).

### lookup_interface (52-73) → N:107-125

| C | Choice point | Lean | Status |
|---|---|---|---|
| 57-58 | both or neither selector → `-EBADR` | N:109 `lookupBothOrNeither` | match |
| 59-61 | by ifindex in the socket's netns | N:112-113 `lookupHasIfindex`, the device table | match |
| 62-64 | by name | N:115-116 `lookupHasIfname` fixed `true` | declared (implied by 57) |
| 65-66 | no device → `-ENODEV` | N:117 `lookupNoDev` | match |
| 67-70 | `!link_ops ‖ !kind ‖ strcmp` → `dev_put`, `-EOPNOTSUPP` | N:122-124 three operands, `lookupNotWireguard` | match; `!kind` declared dead; `dev_put` declared |

### set_port (314-327) → N:128-138

| C | Choice point | Lean | Status |
|---|---|---|---|
| 318-319 | same port → 0 | N:130 `setPortSame` | match |
| 320-321 | every peer: clear endpoint src | N:131-134 `setPortPeerIter` → S:121 | match |
| 322-325 | not running → store port, 0 | N:135-137 `setPortNotRunning` | match |
| 326 | `wg_socket_init` | N:138 → S:61 | declared cut |

### set_allowedip (329-355) → N:141-153

| C | Choice point | Lean | Status |
|---|---|---|---|
| 335-337 | FAMILY, IPADDR or CIDR absent → `-EINVAL` | N:142-143 `aipNoFamily/NoAddr/NoCidr`, short-circuit order | match |
| 341-346 | `AF_INET && cidr ≤ 32 && len 4` → `insert_v4` | N:147-149 → A:180 | match |
| 347-352 | `AF_INET6 && cidr ≤ 128 && len 16` → `insert_v6` | N:150-152 → A:180 | match |
| 354 | neither → `-EINVAL` | N:153 | match |

### set_peer (357-491) → N:156-225

| C | Choice point | Lean | Status |
|---|---|---|---|
| 365-369 | public key absent or short → `-EINVAL` | N:162 `peerHasPubkey`, `peerPubkeyLen` fixed | match; length declared (P8) |
| 370-372 | preshared key if present and 32 bytes | N:164-166 | match; length declared |
| 374-378 | flags; `& ~7` → `-EOPNOTSUPP` | N:167-169 | match |
| 381-383 | protocol version ≠ 1 → `-EPFNOSUPPORT` | N:170-171 | match |
| 386 | hashtable lookup, strong reference | N:172 → P:231-236 | match; bucket walk declared |
| 389-391 | new peer with REMOVE_ME or UPDATE_ONLY → 0 | N:173-175 | match |
| 394 | mask REPLACE_ALLOWEDIPS | N:176 | match |
| 397-409 | identity set and key is the device's → 0 | N:177-179 | match |
| 412-417 | `wg_peer_create` (MAX_PEERS, zalloc, dst_cache) → error | N:180-183 → P:247-279 | match; dst_cache arm declared |
| 421 | `wg_peer_get` | N:186 | match |
| 424-427 | REMOVE_ME → `wg_peer_remove`, out | N:189-191 → R:123 | match |
| 429-434 | preshared key copied | N:192-193 | match |
| 436-448 | endpoint: `len 16 && AF_INET` / `len 28 && AF_INET6` / ignored | N:194-201 → S:142 | match on the encoded layouts; **F1** on a cross-layout `af` |
| 450-452 | REPLACE_ALLOWEDIPS → `remove_by_peer` | N:202 → A:187 | match |
| 454-467 | allowed IPs: parse error → `-EINVAL`; `set_allowedip` error → out | N:204-215 | match (no loop test on `goto out`, as in C) |
| 469-480 | keepalive: send iff old 0, new ≠ 0, running; store; send | N:217-223 | match |
| 482-483 | running → `send_staged_packets` | N:224 | match |
| 486-489 | out: put; memzero if the PSK attribute is present | N:157-160 (put, then memzero) | match |

### wg_set_device (493-608) → N:229-293

| C | Choice point | Lean | Status |
|---|---|---|---|
| 499-502 | lookup error → `out_nodev` | N:233-236 | match |
| 507-511 | flags; `& ~1` → `-EOPNOTSUPP` | N:237-239 | match |
| 513-521 | port or fwmark: `!net ‖ !ns_capable` → `-EPERM` | N:240-244 `setDevNoNet` computed, `setDevNotCapable` fixed | match; capability half declared |
| 523 | `device_update_gen++` | N:245 | match |
| 525-531 | fwmark stored; every peer's src cleared | N:246-251 | match |
| 533-538 | `set_port`; error → out | N:252-254 | match |
| 540-541 | REPLACE_PEERS → `wg_peer_remove_all` | N:255 → R:133 | match |
| 543-545 | private key present and 32 bytes | N:256 | match; length declared |
| 551-553 | stored (clamped) key equals the attribute → skip | N:259 | match |
| 558-565 | `generate_public` (null secret, null point); lookup; put; remove | N:261-267 → P:69-72, P:231, P:38, R:123 | match |
| 568 | `!has_identity && running` | N:268-270 | match |
| 569 | set identity: clamp; `has_identity = generate_public(raw)`; public kept when not written | N:271 → P:75-81 | match |
| 570 | `&& has_identity` | N:272-273 | match |
| 572 | cookie device keys (identity arm) | N:274 → P:85-95 | match |
| 573-578 | per peer: precompute (no identity, null point); expire (next, current); send staged | N:275-280 → P:53-64, K:110-125 | match |
| 583-596 | peers: parse error → `-EINVAL`; `set_peer` error → out | N:281-292 | match |
| 599-607 | out: unlock, `dev_put`; `out_nodev`: memzero private key | N:230-232 at every exit | match; `dev_put` declared |

### get_allowedips (75-94) → D:55-66

| C | Choice point | Lean | Status |
|---|---|---|---|
| 80-82 | nest start fails → `-EMSGSIZE` | D:56-57 | match |
| 84-90 | cidr ‖ family ‖ address (4 or 16) fails → cancel, `-EMSGSIZE` | D:58-64, room restored | match |
| 92-93 | nest end, 0 | D:65-66 | match |

### get_peer (105-197) → D:88-167

| C | Choice point | Lean | Status |
|---|---|---|---|
| 109-114 | peer nest fails → `-EMSGSIZE` | D:92-93 | match |
| 110 | node = `ctx->next_allowedip` | D:94 | match |
| 117-121 | public key fails → err | D:98-99 | match |
| 123 | no node → the fixed part (a stale cursor skips it) | D:100 | match |
| 130-135 | preshared key fails → err | D:101-102 | match |
| 137-146 | handshake ‖ keepalive ‖ tx ‖ rx ‖ protocol fails → err | D:104-113 | match |
| 149-159 | endpoint by `sa_family` (0: none); fails → err | D:119-125 | match |
| 160-162 | node = first of the peer's list | D:133 | match |
| 164-165 | no node → `no_allowedips` | D:136-139 | match |
| 166-169 | seq unset → taken; changed → `no_allowedips` | D:140-145 | match |
| 171-173 | allowed-IPs nest fails → err (seq kept) | D:146-147 | match |
| 175-187 | from the node: `read_node`; put fails → both nests ended, cursor = node, `-EMSGSIZE` | D:151-164 | match; node dereferenced after the seq test |
| 188-193 | nests ended; both cursors reset; 0 | D:134-135, 165-167 | match |
| 194-196 | err: peer nest cancelled | `.cancelled` with the entry room | match |

### wg_get_device_start (199-208) → D:322-333

| C | Choice point | Lean | Status |
|---|---|---|---|
| 203-205 | lookup error returned (acknowledged by the core) | D:326-330 `getStartErr` | match |
| 206-207 | `ctx->wg = wg` | D:332 `hasWg` | match |

### wg_get_device_dump (210-302) → D:189-276

| C | Choice point | Lean | Status |
|---|---|---|---|
| 222-223 | `cb->seq`; cursor | D:191-193 | match |
| 225-229 | header fails → out (`-EMSGSIZE`); consistency flag | D:194-199 | declared unreachable; flag match |
| 231-237 | no cursor: port ‖ fwmark ‖ ifindex ‖ ifname fails → out | D:201-211 | declared unreachable |
| 239-251 | identity: private ‖ public fails → out | D:212-219 | match; failure declared |
| 254-257 | peers nest fails → out; `ret = 0` | D:221-224 | declared unreachable |
| 264-268 | list empty ‖ (cursor && dead) → nest cancelled, out | D:227-233 | match |
| 269-276 | from the cursor: `get_peer` fails → not done, break; else cursor = peer | D:237-262 | match |
| 277 | nest end | D:262 | match |
| 280-282 | `!ret && !done && cursor` → get; put the old cursor | D:265-269 | match |
| 286-289 | `ret` → `genlmsg_cancel` | D:270 | declared unreachable |
| 290-296 | end; done → cursor NULL, 0; else cursor, `skb->len` | D:272-276 | match; **F2** |

### wg_get_device_done (304-312) → D:171-173

| C | Choice point | Lean | Status |
|---|---|---|---|
| 308-309 | `ctx->wg` → `dev_put` | D:172 `getDoneHasWg` | match; `dev_put` declared |
| 310 | put the cursor | D:173 | match |

## 2. Findings

Class 1 (omission): none. Class 2 (order): none. Class 3 (silent arm): none
undeclared (the seven fixed values are in section 3). Class 5 (hidden input
not consumed): none (section 3). Class 6 (mirror-only behaviour): none
undeclared (the stops are in section 3). Class 4 (data shape): two.

**F1 (class 4, observable).** `EndpointAttr` (N:52-59) holds the attribute
as parsed fields: `family` (the `sa_family` bytes), `addr` as the 4- or
16-byte integer of the trace's `family`, `port`, `flowinfo`, `scope`, `len`.
The C (441-446) reads `nla_data` as a `sockaddr_in` or a `sockaddr_in6` by
`len` and `addr->sa_family` alone. The validator (`harness/wg.py:86-112`) and
`Runner.parseEndpoint` (`Leanux/Runner.lean:267-283`) admit `af` with any
`len` in 16..128 for either `family`, so one layout's bytes can be presented
under the other arm's test. Trace: a `wg_set` whose peer endpoint is
`{family: 4, addr: "7f000001", port: 51820, af: 10, len: 28}` (the bytes
`0a00 ca6c 7f000001` then 20 zeros), then a `wg_get`. The C takes the
`sockaddr_in6` arm and stores `[::]:51820` with `sin6_flowinfo` 0x7f000001;
the mirror takes `peerEndpointV6Family` (N:200) and stores the address
0x7f000001 with `flowinfo` 0 (N:201). The dump's `endpoint.addr` and
`flowinfo` differ. The symmetric trace `{family: 6, addr: "::1", port, af: 2,
len: 16, flowinfo: 0x7f000001}` makes the C store `127.0.0.1` and the mirror
`0.0.0.1`. The design's 3.3 rows use `af` and `len` only on the ignored
combinations, so this is not a recorded exclusion. Fix: fail closed in
`parseEndpoint` and `_endpoint` when `af` names the other family and `len`
is that family's size (the only combinations the C accepts under the
reinterpretation), or carry the attribute's bytes.

**F2 (class 4, internal only).** `DumpCall.ret := 1` (D:276) stands for the
C's `skb->len` (296); only its sign is read (`netlinkDump`, D:298, 304), so
no observable changes, but the per-socket `dumpDoneErrno` is a flag where
the C's is a length.

Outside the count (transport): on a start error `netlinkDumpStart`
(D:326-330) keeps the socket's `ctx` and `prevSeq`, where
`__netlink_dump_start` zeroes `nlk->cb` (af_netlink.c:2417) before `start`
(2431). Nothing reads them before the next start re-zeroes them; internal
only, and in the environment by the recorded decision.

Shapes checked and found equal: `struct dump_ctx` ↔ `DumpCtx`; `struct
endpoint`'s union `src4`+`src_if4` / `src6` ↔ `Endpoint.src`, `srcIf`; the
peer, device and allowed-IPs fields the dump reads; `peer_list` and
`allowedips_list` as ordered lists; the pubkey table as a map.
`DeviceAttrs`/`PeerAttrs` lack the attributes the policy admits but the set
path never reads (`WGDEVICE_A_PUBLIC_KEY`, `WGPEER_A_LAST_HANDSHAKE_TIME`,
`RX_BYTES`, `TX_BYTES`): no C read, nothing to mirror.

## 3. Declared cuts, constants, hidden inputs and stops (verified, not findings)

| Fixed value or cut | Lean | Reason, where recorded |
|---|---|---|
| `lookupHasIfname` = true | N:115 | the `-EBADR` test (57) leaves exactly one selector; the `else if` is implied. Not written down anywhere |
| `lookupNoKind` = false | N:122 | every registered `rtnl_link_ops` sets `.kind` (design 2.1, 5) |
| `peerPubkeyLen`, `peerPskLen`, `setDevPrivateKeyLen` = true | N:162, 165, 256 | `NLA_POLICY_EXACT_LEN`, P8 (design 2.1, 5) |
| `setDevNotCapable` = false | N:243 | `CONFIG_USER_NS` unset; `GENL_UNS_ADMIN_PERM` passed with the same credential; the capdrop op drops `CAP_SYS_ADMIN` only (W8 note 2.2; seccomp design, op 33) |
| `peerCreateDstCacheFail` = false | P:256 | percpu allocation retired as a choice (a-alloc 6.4) |
| header, device part, peers nest, `ret != 0` → `unsupported` | D:195, 203-217, 222, 270 | a fresh 3776-byte chunk holds the 140-byte device part (design 2.3, 5) |
| `-EBUSY`, `-EAGAIN`, a lone `NLMSG_DONE` → `unsupported` | D:325; `Syscalls.lean:269-280` | af_netlink.c unanchored (decisions.md 2026-10-12) |
| `dev_get_by_*` / `dev_put` (59-64, 69, 309, 602) | — | net_device refcount unmodelled; its consumer `netdev_wait_allrefs` made unreachable (design 2.3 C1, 4.2) |
| `wg_socket_init` (326) | S:61-83 | cut over the bound ports; `-ENONET`, `-EADDRINUSE`, the port draw (S module note, recorded deviation) |
| pubkey bucket walk (386, 559) | P:231-236 | one `pubkeyLookupMatch`; siphash-keyed order unobservable (P module note) |
| `sin_zero` (442) | — | decoder rejects nonzero (design 5) |

Hidden inputs on these paths (class 5), all consumed at the C site:

| C site | Record | Lean |
|---|---|---|
| peer.c:33 `kmem_cache_zalloc` | alloc site 6 | P:251 |
| peer.c:34 `dst_cache_init` → `dst_cache_reset` jiffies | kind 306 | P:271 → S:103-108 |
| peer.c:49, noise.c:184 coarse boot clock | clock | P:274, K:115 |
| allowedips.c:190, 205, 234 `kmem_cache_zalloc` | alloc sites | A:123, 136, 160 |
| send.c:226 `alloc_skb` (keepalive) | alloc site 13 | `Send.lean:261-266` |
| socket.c:294, 311 `dst_cache_reset[_now]` jiffies | kind 306 | S:142-150, 121-124 |
| udp.c:257 `get_random_u32` (port 0, running) | `udpPortDraw` | S:72 |
| af_netlink.c:2290 chunk `alloc_skb`, :820 autobind | cut sites 21, 170 | `Syscalls.lean:257-267`; the dump callback reads no record, so boundary consumption keeps the order |
| curve25519 (558, noise.c:301, 50) | deterministic | P:61, 69-72 |

Mirror-only stops (class 6), all fail-noisy and documented (design 4.3,
risk 4, 4.5): `requireNotPending` at D:244 (`tx_bytes` of a dumped peer),
S:143 (endpoint), P:24, 41, 203 (references), P:54, 77, K:111 (identity
and handshake); the invariant at D:153 (a stale node with an unchanged
sequence); the op-9 `coalesce` invariants at D:363-396.

## 4. Verdict

The module follows netlink.c's shape closely: every conditional, loop, early
return and error arm of the eleven C functions on the modelled paths has a
mirror choice point at the same position with the same arms, including the
flag masks, the lookup and the remove/update-only semantics, the keepalive
and listen-port side effects in the C's order, the private-key change with
its two public-key generations and the per-peer precompute and expiry, the
dump's cursors, the allowed-IPs sequence test, the `-EMSGSIZE` resumption
and the cancel paths; every fixed value and cut has a recorded reason except
one that is implied by the preceding test, and every hidden input on these
paths is consumed at its C site. Counts: class 1: 0; class 2: 0; class 3: 0
undeclared; class 4: 2 (F1 observable, F2 internal); class 5: 0; class 6: 0
undeclared. Fix first: (1) F1, fail closed in `parseEndpoint` and
`_endpoint` on an `af` that puts the bytes under the other `sockaddr`
layout, since the validator admits it and the dump differs; (2) compute
`lookupHasIfname` from `ref.ifname.isSome` (N:115), removing the one fixed
value no document records; (3) F2 and the start-error zeroing, so that
`NlSock` holds the C's state at the boundary (a length, a zeroed context).
