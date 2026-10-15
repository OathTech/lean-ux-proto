# Correspondence audit: `Leanux/WG/Receive.lean` and `RxData.lean` against `receive.c` and `cookie.c`

[AGENT, independent audit, 2026-10-13] A reading audit of the receive-path
mirror at `main` 2c7a076 against the pristine Linux 6.12.110 source
(`.deps/linux/drivers/net/wireguard/receive.c`, `cookie.c`, with
`queueing.h`, `socket.c:203-332`, `ratelimiter.c:84-156`,
`include/net/inet_ecn.h`). No build, no checker run, no mirror change. The
rule applied is AGENTS.md's "thin-layer altitude": same-shaped data, one
mirror choice point per C choice point in the C's order, out-of-scope arms
as explicit `unsupported`/`invariant`, hidden inputs consumed from records.
Differences the altitude excludes (byte layout, pointers, barriers, locking,
RCU, the primitives, the stack below the device) are not reported. An
exclusion recorded with its reason in a design doc, the census
(`docs/2026-10-06-wireguard-census.md`, rows P5-P14) or the module header is
listed where it matters but is not a finding.

Classes: **1** C choice point with no mirror choice point and no declared cut;
**2** mirror choice point out of the C's order; **3** an arm resolved by a
fixed value where the C branches on state; **4** data of a different shape;
**5** a hidden input the C reads that the mirror does not consume there;
**6** something the mirror does that the C does not. "Observable" means a
trace can be described on which the kernel's verdict or output and the
mirror's differ; "internal" means only the correspondence (the decision
stream, the proof obligation) differs.

Findings are numbered F1-F14 across the tables; the counts and the verdict
are at the end.

## 1. `wg_packet_receive` (receive.c:542-586) — `packetReceive` (Receive.lean:412-439)

Matched in order: `prepare_skb_header < 0` (:544, `.rxPrepareFailed`
413), the switch (:546, `.rxHandshake` 415, `.rxData` 432, the default's
`WARN` as `invariant` 439), `rng_is_initialized` (:552, 417),
`handshake_queue_len > 2048` (:554, 420), the produce failure (:561, 423),
`atomic_inc` (:567, 426), `wg_cpumask_next_online` (:568, 427, with the
`.cpumaskWrap` decision), `queue_work_on` (:570, `queueDeviceWork` 430 with
its dispatch record), the DS field (:575, 436).

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F10 | :555-560 `ptr_ring_produce_bh` into a 4096-slot `ptr_ring` (`device.c:358`); :212 `ptr_ring_consume_bh` | 423 `handshakeQueue.length ≥ 4096`; 305 `drop 1`; `Types.lean:445` `List` | 4 | The handshake ring is a `List` with a length full-test. The crypt rings were repaired to `PtrRing` after the simulation-target review (4.1); this ring was not, so its counterexample applies: a consumed slot stays occupied until a batch of 16 clears it, and Linux's produce fails at 4096 minus the carried slots while the mirror fails at 4096. **Observable in principle**: a `wg_batch` of more than 4081 handshake injects after an earlier drained batch (no corpus trace does this; `Env.flood` summarizes its batch's producer side and is unaffected). Internal otherwise. |
| — | :552 `rng_is_initialized` | 417 constant, `unsupported` | 3 | Recorded: the guest waits for the RNG (comment). Not counted. |
| — | :554-559 the trylock path | 420 `unsupported` | 3 | Recorded: `docs/2026-10-05-e-dos.md` §11, census P12. Now reachable by a `wg_batch` of more than 2048 handshake injects (the trylock cannot fail on one CPU); the reason is stale but the arm is explicit. Not counted. |

## 2. `prepare_skb_header`, `validate_header_len` (receive.c:28-90) — Receive.lean:46-79

All 13 conditions have a decision in the C's order (`.checkProtoParsed`/
`.checkProtoMatches` for queueing.h:70-74, `.prepBadProtocol` ..
`.prepPullHeaderFailed`, `.hdrTooShort` .. `.hdrCookieLen`). The message
sizes (16, 148, 92, 64, minimum 32) agree with `messages.h:80-118`.

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| — | :52-56, :59-60, :66-67, :76, :79, :86 (eight arms on the skb's layout) | 67-78 constant `false` | 3 | Recorded: census P8 ("constants the stack validates"), the module header, `docs/2026-10-05-a-alloc.md:123`. The UDP receive path has already bounded and trimmed the datagram, so each arm is structurally dead; a divergence is caught by the checker's spans, not by the mirror. Not counted. |
| — | :74 `pskb_may_pull(.., 4)` | 74 `msg.length < 4` | — | Modelled (a payload under 4 bytes); so :30 is then dead in both, as the Lean comment says. |

## 3. `wg_receive_handshake_packet` (receive.c:92-204) — `receiveHandshakePacket` (Receive.lean:219-293)

Matched in order: the cookie arm (:104, `.hsCookie` 220); `under_load`
(:112-115, `.hsUnderLoad` 227, `.underLoadNow` 229); the decay (:116-119,
`.hsWasUnderLoad` 234, `birthdateTest` 239, `.hsDecayExpired` 242 with the
reset 243); `wg_cookie_validate_packet` (:121, 244); the two-term
`packet_needs_cookie` table with the C's short-circuit (:123-132,
247-254, the invalid-MAC drop as a bare `return`); the switch (:134,
257/267); the initiation arm (:139-155, 258-266); the response arm
(:161-188, 268-280, `begin_session` as `.hsRespSessionBegun`); `!peer`
(:192, `invariant` 282); `update_rx_stats` (:198, 287-290, peer and device
tstats); the timers and the put (:201-203, 291-293). The function-static
`last_under_load` (:100) is `World.lastUnderLoad` (kernel-global, not per
device) and `handshake_queue_len` is `Device.handshakeQueueLen`, both the
C's shape.

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F9 | :112 `handshake_queue_len >= MAX/8` | 227 `branch`, not `branchCmp` | 3 | The threshold is a declared decision but its operands are not checked (`docs/2026-10-05-e-dos.md` appendix: "E-M6 (threshold) not claimed"). A mirror threshold other than 512 would still agree on every trace that runs far above it. Internal. |
| — | :198 `dev_sw_netstats_rx_add` then `peer->rx_bytes` | 287-290 peer then device | 2 | Data-only (no choice point between); `updateRxStats` (RxData.lean:55) has the C's order. Not counted. |

## 4. `wg_packet_handshake_receive_worker` (receive.c:206-218) — `receiveStep`, `handshakeReceiveWorker` (Receive.lean:298-316)

Matched: the ring poll (:212, `.workerConsumed`), the packet (:213), the
free and `atomic_dec` (:214-215, 308, after the packet as in C), the
unconditional `cond_resched` (:216, the environment's `condResched`). The
ring's consume is a list `drop 1`: see F10.

## 5. `wg_cookie_message_consume` (cookie.c:198-236) — `cookieMessageConsume` (Receive.lean:83-101)

Matched: the lookup of either kind with the peer reference (:205-209,
`indexLookup [.handshake, .keypair]` 85, `.cookieLookupMiss` 86),
`have_sent_mac1` (:212, `.cookieNoMac1Sent` 90, with the `goto out` put
91), the decrypt with the C's operands (:216-219: nonce at offset 8, the
32-byte sealed cookie at 32, AAD `last_mac1_sent`; 95), the store (:222-228,
`.cookieDecryptOk` 96, `.cookieBirthdate` 98), `out:` (:235, 101). No
finding.

## 6. `wg_cookie_validate_packet` (cookie.c:119-154) — `cookieValidatePacket` (Receive.lean:166-178)

Matched: `compute_mac1` over `len - 32` bytes (:130-133, 168-170,
`.macInvalid`), `!check_cookie` (:137, `.macNoCookieCheck` 171),
`make_cookie` and `compute_mac2` over `len - 16` bytes (:140-144, 173-176,
`.macCookieInvalid`).

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F2 | :147-148 `if (!wg_ratelimiter_allow(..)) goto out` | 178 a plain `if ← ratelimiterAllow src` | 1 | No decision is declared at cookie.c:147 (`Decision.lean` has none for `wck 147`), unlike every other callee test on this path (`.hsRespSessionBegun`, `.rxPollCounterInvalid`). The outcome is forced by `.rlAllow`/`.rlEntryMatch` inside the callee and the `RATELIMITED` state feeds `.hsLoadedCookieOk`, so the verdict cannot differ. Internal. |

## 7. `make_cookie` (cookie.c:91-117) — `makeCookie` (Receive.lean:118-122)

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F7 | :96-102 `if (wg_birthdate_has_expired(secret_birthdate, 120)) { secret_birthdate = now; get_random_bytes(secret) }` | 119 `_ ← hiddenClock .birthdateExpired` (the outcome discarded); `Device.cookieSecretBirthdate` (`Types.lean:407`) is never read | 3 (and 5: the rotation's clock :99 and random :100 are not consumed) | The mirror consumes the age test's clock record and ignores the result; the rotation arm is neither modelled nor `unsupported`. The recorded reason (`docs/2026-10-05-e-dos.md` §11: "needs D3's time advance; 120 s ≫ 4 s") predates D3: `wg_advance` moves the coarse boot clock (the `e_underload_decayed` trace crosses the 1 s decay that way) and takes up to 2^31 ticks. **Observable**: `wg_advance` of 120 s or more after wg0's creation, then a `wg_flood` with a leading valid initiation: Linux seals the cookie reply under a rotated secret, the mirror under the old one. With records the kernel's extra kind-208 and random records would surface as a stray-record mismatch at the next consumer (misattributed); in the domain filter, nothing. **Fixed 2026-10-13** (task/receive-fixes: the age test declared as `make_cookie.secret_expired`, the rotation's clock read and random bytes consumed as sites 129/134, `make_cookie` listed; `e_underload_cookie_rotated` fails before (the reply's bytes) and agrees after). |
| F4 | :107-112 the source address by `skb->protocol` | 121 a plain `if src.family == 4` | 1 | No decision; the Lean comment records why (`make_cookie` is an out-of-line static not in `correspondence/kcov.json`'s functions, so a span could not be witnessed). The address bytes feed the cookie, which is byte-checked, so the verdict cannot differ. Internal; the fix is to list the function. **Fixed 2026-10-13** with F7 (`make_cookie.ipv4`/`.ipv6`). |

## 8. `wg_ratelimiter_allow` (ratelimiter.c:84-156) — `ratelimiterAllow` (Receive.lean:138-161)

Matched: the protocol (:95, `.rlProtoIp`), the bucket hit with the token
arithmetic and both clock reads (:111-131, :146; `.rlEntryMatch`, `.rlAllow`
with operands, `.ratelimiterNow`, `.ratelimiterInsertNow`), the table limit
before the allocation (:135-140, `.rlOverLimit`, `.rlAllocFail`), the insert
with `TOKEN_MAX - PACKET_COST` (:142-151). The 16384-entry limit is
recorded (`docs/2026-10-05-e-dos.md` §11 and the appendix) and the `(net,
ip)` hash is a declared cut.

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F13 | :138 `kmem_cache_alloc(entry_cache, GFP_KERNEL)` | 156 `envOk .ratelimiterEntry` | 5 | The allocation outcome comes from the environment oracle (the pipes-era `EnvSite`), not from a kind-305 record as `docs/2026-10-05-a-alloc.md` §6 declares for E's sites (`replySkb` and `skbCowDataRx` on this same path use `hiddenAlloc`). The arm is `unsupported`, so the verdict cannot differ. Internal. | **Fixed 2026-10-15 (B4):** the site is `AllocSite.kmemCacheAllocRlEntry`, consumed by `hiddenAlloc`; the arm is the C's `err_oom` drop. The reason given below was wrong: the kind-305 hook is generic, not a list.
| F12 | :100-106 the IPv6 table, keyed by the source `/64`; `:108-109 return false` | 139-140 `unsupported "the ratelimiter on a non-IPv4 handshake"` | 4 | Explicit and fail-noisy, but the reason ("arm C is IPv4") is in the code only; no design doc records the IPv6 ratelimiter as excluded. Internal. |

## 9. `wg_packet_send_handshake_cookie` (send.c:110-122), `wg_cookie_message_create` (cookie.c:180-196), `wg_socket_send_buffer_as_reply_to_skb` (socket.c:203-233) — Receive.lean:186-216

Matched: `sender_index` at offset 4 for both message types (213-214),
the nonce before `make_cookie` (:190, :192; 206-207, `.cookieNonce`), the
seal with the initiation's MAC1 as AAD (:193-195, 208), the 64-byte reply
(209); `wg_socket_endpoint_from_skb` (:213, `endpointFromSkb` 187 with its
family decisions), `alloc_skb` (:217, `.replySkb` 195), `send4`/`send6`
(:224-227, 199, no `dst_cache`, as the C passes `NULL`).

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F3 | :218-219 `if (!skb) return -ENOMEM`; :224-227 the family switch | 195 `if !(← hiddenAlloc .replySkb) then return`; 199 a plain `if` | 1 | No decisions are declared for socket.c:218 or :224-227 (the function is not listed; the Lean comment at 189-194 records this as a follow-up). The record is consumed and the no-reply outcome is modelled, so the verdict cannot differ. Internal. |

## 10. `wg_packet_consume_data` (receive.c:509-540) — `consumeData` (Receive.lean:366-394)

Matched: the keypair lookup with the peer reference (:516-519,
`indexLookup [.keypair]` 368), `wg_noise_keypair_get` including the `NULL`
case (:520, 371-374, `.keypairGetNull`/`.keypairGetZero`, `.dataNoKeypair`),
`err_keypair` with `wg_peer_put(NULL)` as `.peerPutNull` (:536-539,
376), `is_dead` (:523, `.dataPeerDead` 380, then the keypair put and the
peer put 382-383), the enqueue (:526, 387), `-EPIPE` (:528-529,
`.dataEpipe` 391, `enqueuePerPeerRx .dead`), the early return (:530-533,
`.dataEnqueueOk`/`.dataEnqueueOkEpipe` 393).

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F1 | :534-539 `err:` for `ret == -ENOSPC` — `wg_noise_keypair_put(keypair, false)`, `wg_peer_put(peer)`, `dev_kfree_skb(skb)`, no counter | 394 `invariant "unreachable"` after both `.dataEnqueueOk` and `.dataEnqueueOkEpipe` are false | 1 | `enqueuePerDeviceAndPeerRx` returns `-ENOSPC` (328, `.enqueuePeerQueueFull`, the peer's `rx_queue` at `MAX_QUEUED_PACKETS`), and `.dataEnqueueOkEpipe`'s false span already names :535, yet the arm's body is a mirror-defect stop; the rx skb created at 386 is never freed. The W7 design puts the arm in scope (`docs/2026-10-06-w4-w7-transmit-bulk.md` 2.6 "Receive: err → puts and dev_kfree_skb (receive.c:534-539)", 5.2 "the receive twin likewise") and the tx twin models it (`w7_ring_1025` agrees on `-ENOSPC`). The docstring at 318-321 ("one item per queue is the domain") is stale. **Observable**: a `wg_batch` of 1025 data messages for one peer (no kworker runs inside the call, design 2.7): Linux drops the 1025th silently and polls the rest; the mirror stops with an invariant and gives no verdict. **Fixed 2026-10-13** (task/receive-fixes: the err arm as the C's puts and free; `w7_ring_rx_1025` (scripts/wg-w47-corpus.py `rx_1025_pending`) exercises it: the old mirror stops `invariant` at operation 4 and the fixed one is in domain under `leanux-model --domain`, and Linux runs it with the 1025th dropped silently; it is not in the tier suite because its 1024 inline polls meet the (c') placement ambiguity 1019 times, beyond the protocol's 64 open polls per trace, so the check reports `invalid_output`). |

## 11. `wg_queue_enqueue_per_device_and_peer`, `wg_queue_enqueue_per_peer_rx` (queueing.h:157-178, 193-203) — Receive.lean:322-361

Matched: the `UNCRYPTED` publication (:163, 324), `wg_prev_queue_enqueue`'s
count test before the ring (:167, `.enqueuePeerQueueFull` 328, count
excludes the peeked item as `queueing.c:80-106` decrements at dequeue),
`wg_cpumask_next_online` (:173, 331), the ring's physical full test (:174,
`.enqueueRingFull` 334 on `PtrRing.full`), `queue_work_on` (:176, 338);
the peer reference around the state publication and `napi_schedule`
(:198-202, 351-361). `napi_schedule`'s `NAPI_STATE_SCHED` test is a
declared cut (RxData.lean header).

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F5 | :174 produce, then :176 `queue_work_on` | 338 `queueDeviceWork`, then 339 `produce` | 2 | The full test (334) is taken on the ring before either, and the queue record is order-insensitive to the ring's contents, so nothing differs. Internal. |
| F14 | — | 355-356 `invariant` unless the skb is on its peer's `rx_queue`; RxData.lean:357 `invariant` unless `pkt.peer == pid` | 6 | Store-hygiene assertions with no C counterpart; they can only turn a mirror bug into a stop. Internal. |

## 12. `wg_packet_decrypt_worker`, `decrypt_packet` (receive.c:493-507, 242-292) — RxData.lean:63-124

Matched: the ring poll (:499, `.decWorkerConsumed`), the state from the
result (:500-503, `.decWorkerDecrypted`, `enqueuePerPeerRx .crypted/.dead`),
`need_resched` (:504, `.decWorkerNeedResched` through the environment's
record); `!keypair` (:249), the three-term reject with `is_valid = false`
(:252-256, `.decKeyInvalid`, `.decKeyExpired` with the recorded clock,
`.decCounterLimit` with operands), the nonce (:259-260, 77),
`skb_cow_data` (:268-272, `.skbCowDataRx` lax, `.decCowDataFailed`,
`.decTooManyFrags`), `skb_to_sgvec` (:275), the AEAD under the receiving
key and the 4-zero-byte nonce (:278-281, 85-86), the trim (:287-288). The
plaintext of length `len - 32` replaces the message in the one skb (90).

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F6a | :499 `ptr_ring_consume_bh`: the pending NET_RX runs at its `spin_unlock_bh`, after the consume | 99 `softirq` before the consume at 100 | 2 | D2 placement (b). The poll reads the peer's `rx_queue`, not the ring, and the consumed item is already `UNCRYPTED` on that queue, so the poll's reads are the same. Internal. |
| — | :249, :271 (`> ARRAY_SIZE(sg)`), :275, :287 | 65, 80, 83, 89 constant `false` | 3 | Recorded: census P14 (too many fragments), `docs/2026-10-05-a-alloc.md` §6.4 (`skb_to_sgvec` is not an allocation; a linear skb), the module header (`pskb_trim`). Not counted. |

## 13. `counter_validate` (receive.c:295-331) — `counterValidate` (RxData.lean:129-157)

Matched, with operands: both limits (:302-303, `.ctrRejectCounter`,
`.ctrRejectTheirs`), the window (:308, `.ctrTooOld`), the advance with the
clear loop (:314-322, `.ctrAdvance`, `.ctrClearIter` per word, `min(..,
128)`), the bit test-and-set (:324-326, 152-157). The bitmap is 128 words of
64 bits (`Types.lean:113-116`), the C's `backtrack[]`. No finding.

## 14. `wg_packet_rx_poll` (receive.c:438-491) — `rxPoll` (RxData.lean:338-382)

Matched in order: the budget (:448, `.rxPollNoBudget`), the peek-and-state
loop condition with the head left peeked when `UNCRYPTED` (:451-453,
`PrevQueue.peek` 346, `.rxPollPacket`, `.rxPollNotUncrypted`),
`drop_peeked` (:454, 359), `state != CRYPTED` (:458, `.rxPollNotCrypted`),
`counter_validate` (:461, `.rxPollCounterInvalid`), `endpoint_from_skb`
(:470, `.rxPollEndpointFailed`), `consume_data_done` (:474, 367), `next:`
with the keypair put, the peer put and the free (:477-481, 370-373,
`.rxPollFree`), the budget break (:483-484, `.rxPollBudgetDone`),
`napi_complete_done` (:487-488, `.rxPollComplete` 377, `napiScheduled`
cleared). The budget is `NAPI_POLL_WEIGHT` 64 (`netdevice.h:2632`,
`peer.c:57`).

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F6b | :411 `napi_gro_receive` adds to `napi->rx_list` and `gro_normal_one` (`include/net/gro.h:526-532`) flushes it to the stack once `rx_count >= gro_normal_batch` = 8 (`net/core/hotdata.c:11`), i.e. mid-poll; the remainder at `napi_complete_done` | 367 `gro := gro ++ ..`; 380 `napiCompleteDone gro` after the loop | 2 (the NAPI's `rx_list`/`rx_count` is not represented: 4) | For UDP inner packets delivery is local and recordless, so nothing differs (`w7_multi_rx_8` polls exactly 8). It differs when a delivery re-enters WireGuard: on a poll of 9 or more packets whose 8th provokes the kept IPv4 TCP RST (`wg_xmit` nested, with its dst-cache clock and queue records) and whose 9th roams the endpoint (a `dst_cache_reset` jiffies record), Linux's RST records precede the 9th packet's and the mirror's follow it — a hidden mismatch, a false rejection. Internal. **Fixed 2026-10-13** (task/receive-fixes: `GroState` in RxData.lean, the batch of 8 and the held lone TCP segment). Not observable on this fixture: the one-CPU kernel runs the NET_RX softirq inline at every decrypt, so a poll holds one or two packets and `rx_count` never reaches 8 (`w7_multi_rx_9_rst_roam`, written for the scenario, polls 9 packets in 19 sections and agrees under both mirrors); modelled, unexercised. |
| — | :487-490 `work_done == budget`: no `napi_complete_done`, `net_rx_action` repolls | 381 `unsupported` | 3 | Explicit; recorded as option 13.5 of `docs/2026-10-06-w4-w7-transmit-bulk.md` (§10 derives the trace: two peers, a full ring, a 64-segment GSO inject). Not counted. |

## 15. `wg_packet_consume_data_done` (receive.c:335-436) — `consumeDataDone` (RxData.lean:283-332)

Matched in order: `set_peer_endpoint` (:343, 284, `endpointEq` and the
`dst_cache_reset` record in `Socket.lean`), `received_with_keypair` with
`handshake_complete` and `send_staged_packets` (:345-349, `.doneReceivedNew`
285-287), `keep_key_fresh` (:351, 288), the two timers (:353-354), the
keepalive with `message_data_len(0)` = 32 (:357-363, `.doneRxKeepalive`,
`updateRxStats` 298), `timers_data_received` (:365), `network_header <
head` (:367), the `may_pull`/version test as the C's three-term expression
(:369-373, 306-308), `ip_tunnel_parse_protocol` computed (:384, 311), the
IPv4 arm with `tot_len < 20` before the ECN rewrite (:385-389, 315-318),
the IPv6 arm (:390-393, 319-321), the type fall-through (:395, 322), `len >
skb->len` (:398, 323), `pskb_trim` (:401, 326, `goto packet_processed`
without a counter), `lookup_src` with the put and the peer test (:404-409,
327-329), `update_rx_stats(message_data_len(len_before_trim))` (:412, 331),
the three `DEV_STATS_INC` arms (:415-433, `dishonest` 276-279: `rx_errors`
with `rx_frame_errors` or `rx_length_errors`). The ECN rewrite
(`inet_ecn.h:251-284`, 77-113, 134-164) is matched arm by arm, including
`csum16_add`'s carry fold and the `0xFBFF + ecn << 8` addend.

| Item | C | Lean | Class | Finding |
|---|---|---|---|---|
| F8 | `inet_ecn.h:176-177, 182-183, 212-213, 218-219`: `network_header + sizeof(hdr) <= tail` inside `INET_ECN_set_ce`/`set_ect1` | 245-250 no test | 3 | Implied by the `honest` test (receive.c:369-372) that precedes it, and the functions are declared branch-free in `correspondence/kcov.json`, so the compiler left no point to witness; still a C condition with no mirror counterpart or comment. Internal. |
| — | :367 `network_header < head`; :401 `pskb_trim` | 302, 326 constant `false` | 3 | Recorded in the module header (`wg_reset_packet` resets the network header to `data`; a linear skb). Not counted. |
| — | :411-412 `napi_gro_receive` then `update_rx_stats` | 331 stats, then the bytes returned for delivery | 2 | Data-only; folded into F6b. Not counted. |

## 16. `keep_key_fresh` (receive.c:220-240) — `keepKeyFreshRx` (RxData.lean:171-184)

Matched: the early return (:225, `.rxFreshSentLastminute`), the four-term
`send` with the receive-side threshold 165 s (:230-233, `.rxFreshKeypair`,
`.rxFreshValid`, `.rxFreshInitiator`, `.rxFreshExpired` with operands), the
flag and the queued initiation (:236-239, `.rxFreshSend`). No finding.

## 17. `wg_receive` (socket.c:316-332), `wg_allowedips_lookup_src` (allowedips.c:367-375), `update_rx_stats` (receive.c:19-24)

`wgReceive` (Receive.lean:442-445): both NULL arms constant and explicit
(census P8). `lookupSrc` (RxData.lean:162-166): the family switch
(`.lookupSrcV4`, `.lookupSrcV6`) on the inner source at offsets 12 and 8.
`updateRxStats` (RxData.lean:55-59): the device tstats and `peer->rx_bytes`.
No finding.

## 18. Hidden inputs on the path (class 5 check)

Consumed from records at the C's site: `.underLoadNow` (:115),
`.birthdateExpired` at :117 (the decay), cookie.c:96 (`make_cookie`),
receive.c:253 (`decrypt_packet`) and :232 (`keep_key_fresh`);
`.cookieBirthdate` (cookie.c:225); `.cookieNonce` (:190);
`.ratelimiterNow`/`.ratelimiterInsertNow` (ratelimiter.c:121, 146);
`.replySkb` (socket.c:217, exact 2); `.skbCowDataRx` (receive.c:268, lax
0); the wall clock of `wg_timers_handshake_complete` on key confirmation
(`.walltimeLastHandshakeData`); the dispatch records of `queue_work_on`
(receive.c:570, queueing.h:176); the NET_RX section records that place the
poll; the `cond_resched` records. Not consumed: the rotation's clock and
random reads (cookie.c:99-100, F7) and the ratelimiter entry allocation
(F13). Nothing else on the path reads a hidden input.

## 19. Counts and verdict

| Class | Count | Items |
|---|---|---|
| 1 omission | 4 | F1 (rx `-ENOSPC` arm body), F2 (cookie.c:147), F3 (socket.c:218, :224-227), F4 (`make_cookie`'s protocol) |
| 2 order | 3 | F5 (queue record before produce), F6a (softirq before the consume), F6b (GRO flush placement; also the unrepresented `rx_list`) |
| 3 fixed arm | 3 | F7 (cookie-secret rotation discarded), F8 (ECN tail tests), F9 (under-load threshold operands unchecked) |
| 4 shape | 2 | F10 (handshake ring as a list), F12 (IPv6 ratelimiter, reason in code only) |
| 5 hidden input | 1 | F13 (`envOk` for the ratelimiter entry; F7's rotation reads are counted under F7) |
| 6 extra | 1 | F14 (store-hygiene assertions) |

Of the fourteen, two could change an observable outcome on a describable
trace (F1, F7) and one in principle (F10); the rest are internal.

**Verdict.** The two modules follow the C's control-flow shape closely:
every conditional, loop, early return and error arm of `wg_packet_receive`,
`prepare_skb_header`, `wg_receive_handshake_packet`, both workers,
`wg_packet_consume_data`, `decrypt_packet`, `counter_validate`,
`wg_packet_rx_poll`, `wg_packet_consume_data_done`, `keep_key_fresh`,
`wg_cookie_message_consume` and `wg_cookie_validate_packet` has a declared
mirror decision in the C's order, the C's short-circuit structure is kept
where it decides what runs, the state is the C's (the `PACKET_CB` fields,
the replay bitmap, the two queues, the counters, the static
`last_under_load`), and the hidden inputs are consumed at their sites. The
fixed-outcome arms are, with one exception, structurally dead and recorded
as such. Counts by class: 4 omissions, 3 order differences, 3 fixed arms, 2
shape differences, 1 unconsumed hidden input, 1 extra; two findings are
observable. Fix first: **F1**, the receive-side `-ENOSPC` arm
(receive.c:534-539) that the mirror ends in `invariant "unreachable"` while
its own enqueue returns `-ENOSPC` and the design puts the arm in scope — a
1025-message batch gives Linux a silent drop and the mirror no verdict;
**F7**, `make_cookie`'s secret-rotation test (cookie.c:96-102), whose clock
record is consumed and whose outcome is thrown away — with `wg_advance` the
120 s age is reachable and the cookie reply's bytes would differ, so the
arm needs a declared decision and an `unsupported` (or the rotation
modelled from the records); **F10**, the 4096-slot handshake `ptr_ring`
still represented as a `List` with a length full-test, the one ring the
simulation-target review's repair (4.1) did not reach, which a large
handshake batch after a drained one would expose.

## 20. Disposition (2026-10-14, the pre-release review's section 12)

Every item of the findings tables, so that the verdict paragraph's "every
conditional" cannot override its own omissions.

| Item | Disposition | Where |
|---|---|---|
| F1 | fixed: `consume_data`'s `-ENOSPC` arm as the C's two puts and silent free; `w7_ring_rx_1025` in the tier | task/receive-fixes (landed in f45bde8), the tier (7a92672) |
| F2 | fixed: `.macRatelimited` at cookie.c:147, a declared decision | task/review-receive (2026-10-14) |
| F3 | fixed: `wg_socket_send_buffer_as_reply_to_skb` listed; `.replyInSkbNull`, `.replyEndpointErr`, `.replyNoMem` (A's `replySkb` record), `.replyInet`, `.replyInet6` | task/review-receive |
| F4 | fixed with F7: `make_cookie`'s protocol switch as `.cookieProtoIp`/`.cookieProtoIpv6` | task/receive-fixes |
| F5 | justified: the full test precedes both the produce and the `queue_work_on`; no state the order could change between them | internal |
| F6a | justified: D2 placement (b), the pending NET_RX at the consume's `spin_unlock_bh`; the scheduler places it by the records | internal |
| F6b | fixed: `GroState`, the batch of 8 and the held lone TCP segment; unobservable on one CPU (every decrypt runs the softirq inline), modelled and listed unexercised | task/receive-fixes, W5-W6 design |
| F7 | fixed: the cookie-secret rotation modelled from the records; `e_underload_cookie_rotated` | task/receive-fixes |
| F8 | checked: the `network_header + sizeof(hdr) <= tail` tests are implied by the honest test (receive.c:369-372); `inetEcnSet` asserts the implication fail-closed | task/review-receive |
| F9 | fixed: `.hsUnderLoad` declared with its operands (receive.c:112-113, the counter against 512); the boundary traces `e_underload_511/512/513` | task/review-receive |
| F10 | deferred: the 4096-slot handshake `ptr_ring` as a `List` with a length full-test; unreachable inside the domain (the trylock arm at > 2048 stops first); a representation task named in the audit wave's integration record | f45bde8 |
| F12 | fixed: the IPv6 ratelimiter table (`.rlProtoIp6`, `table6` keyed by the source /64), `e_underload_ratelimit6` and `_deny`; a `wg_flood` with `family: 6` | task/review-receive |
| F13 | fixed (B4, 2026-10-15): `AllocSite.kmemCacheAllocRlEntry` over the generic kind-305 hook, armed by the ratelimiter traces' `draw` entries; the `-ENOMEM` arm is the C's `err_oom` drop, reached only by steering a class the host does not enable. The earlier reason ("not in the kind-305 hook's list") was wrong: there is no list; the site's row in `harness/steer.py` and its constructor were missing | task/design-b4 |
| F14 | justified: store-hygiene `invariant`s with no C counterpart, fail-noisy on a mirror defect only | internal |
