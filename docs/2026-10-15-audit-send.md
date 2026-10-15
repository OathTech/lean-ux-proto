# Correspondence audit: `Leanux/WG/Send.lean` (with `Data.lean` and the send half of `Handshake.lean`) against `send.c`

[AGENT, independent audit, Claude Opus 5.5, written 2026-10-14] A reading
audit of the transmit-path mirror at `main` ca6b22e against the pristine
Linux 6.12.110 source (`.deps/linux/drivers/net/wireguard/send.c`, with
`queueing.h`, `queueing.c`, `timers.c:30-39,145-217`, `timers.h:24-29`,
`noise.c:131-149`, `socket.c:20-200`, `cookie.c:180-196`, `peer.c:43`,
`messages.h:34-54`, `include/linux/ptr_ring.h`, `include/net/ip_tunnels.h:555-599`,
`include/net/inet_ecn.h:46-52`, `include/linux/cpumask.h` for `NR_CPUS=1`,
`lib/crypto/chacha20poly1305.c:236-237`). No build, no checker run, no guest,
no mirror change. Configuration `kernel/config-x86_64-net-choice`: `CONFIG_SMP`
unset, `NR_CPUS=1`, `PREEMPT_NONE`, `HZ=250`, no `DYNAMIC_DEBUG` (every
`net_dbg_ratelimited` is compiled out: no choice point).

The mirror of `send.c` is spread over three files: `Leanux/WG/Send.lean`
(queueing a handshake, staging, `create_data`, the queueing.h enqueues, the
ECN encapsulation, the purge, the keepalive), `Leanux/WG/Data.lean`
(padding, `encrypt_packet`, the encrypt and tx workers, `create_data_done`,
the send-side `keep_key_fresh`) and `Leanux/WG/Handshake.lean:455-491` (the
initiation, the response, the send worker). The cookie reply is
`Receive.lean:246-257`. Line numbers are the files' at ca6b22e; a bare C
line is `send.c`'s.

Classes, as in the four earlier audits: **1** a C choice point with no
mirror choice point and no declared cut; **2** a mirror choice point (or a
state change between two of them) out of the C's order; **3** an arm the
mirror resolves by a fixed value or from its own state where the C branches
on state it does not consult; **4** data of a different shape; **5** a
hidden input the C reads that the mirror does not consume there; **6**
something the mirror does that the C does not. Severity: **O** observable
on a describable trace (a verdict or an output differs); **O-p** observable
in principle on a describable but exotic trace; **I** internal (only the
correspondence, the decision stream or the diagnosis differs). Status per
choice point: `match`, `declared` (an exclusion recorded with its reason;
section 5) or `F<n>`.

Method: each conditional, loop, early return and error arm of the fifteen
functions, in C order, located at its `branch`/`branchCmp`/`branchExpired`/
`unsupported`/`invariant`; each callee read where the path's shape depends
on it; each hidden read matched to its consumer; the thresholds and
arithmetic recomputed from the C's constants. `-ENOKEY` has no arm in
`send.c`: it is `wg_xmit`'s (`device.c:157-160`), covered by the device audit.

## 1. `wg_packet_send_handshake_initiation` (21-44) — `sendHandshakeInitiation` (Handshake.lean:471-485)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 25-27 | `!wg_birthdate_has_expired(last_sent, REKEY_TIMEOUT)` → return | 473 `.initRateLimited` (`branchExpired`, the clock record, `le` operands) | match |
| 29 | `last_sent = now` | 474 `.initLastSent` | — |
| 34 | `create_initiation` succeeded | 477 `.initCreated` | match |
| 35-42 | mac; traversal; any_sent; `last_sent = now`; send (DSCP 0x88); handshake_initiated | 479-485, `.initLastSentAgain` | order exact |

## 2. `wg_packet_handshake_send_worker` (46-53) — `handshakeSendWorker` (Handshake.lean:489-491)

No choice point: the initiation, then `wg_peer_put`. `process_one_work`'s
clearing of PENDING before the function is `Env.lean:260-263`
(`handshakePending := false` before `runWorker`). match.

## 3. `wg_packet_send_queued_handshake_initiation` (55-83) — `sendQueuedHandshakeInitiation` (Send.lean:46-63)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 58-59 | `!is_retry` → attempts = 0 | 48 `.queuedNotRetry` | match |
| 66-67 | `!expired(last_sent, REKEY_TIMEOUT)` → out | 52 `.queuedNotExpired` (`branchExpired`) | match |
| 68 | `\|\| is_dead` → out (evaluated only when expired) | 53 `.queuedDead` | match |
| 71 | `wg_peer_get` | 54 | — |
| 75-80 | `!queue_work(...)` → `wg_peer_put` | 57 `.queuedAlreadyQueued p.handshakePending`; 61 the queue record | **F3** |

47 is the retired `requireNotPending` (a no-op since 2026-10-14) and 63 the
vestigial `queuedThisCall` bookkeeping: F7.

## 4. `wg_packet_send_handshake_response` (85-108) — `sendHandshakeResponse` (Handshake.lean:455-468)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 89 | `last_sent = now` | 456 `.respLastSent` | — |
| 94 | `create_response` succeeded | 459 `.respCreated` | match |
| 96 | `begin_session` succeeded | 462 `.respSessionBegun` | match |
| 98-105 | session_derived; traversal; any_sent; `last_sent = now`; send | 463-468, `.respLastSentAgain` | order exact |

## 5. `wg_packet_send_handshake_cookie` (110-122) — `sendHandshakeCookie` (Receive.lean:254-257)

No choice point of its own (`correspondence/kcov.json` records it).
`wg_cookie_message_create` (cookie.c:180-196): type 3, the receiver index
read at offset 4 of either handshake message, the 24-byte nonce
(`.cookieNonce`) before `make_cookie`, XChaCha20-Poly1305 with the
initiating message's MAC1 (`len - 32`, 16 bytes) as AAD (Receive.lean:246-250).
The reply send is the receive audit's F3, fixed. match.

## 6. `keep_key_fresh` (124-139) — `keepKeyFresh` (Data.lean:167-178)

| C | Choice point | Lean | Status |
|---|---|---|---|
| 131 | `keypair` | 171 `.freshKeypair` | match |
| 131 | `&& is_valid` | 174 `.freshValid` | match |
| 132 | `&& (sending_counter > REKEY_AFTER_MESSAGES` | 175 `.freshCounter`, `branchCmp`, `>` against 2^60 | match |
| 133 | `\|\| (i_am_the_initiator` | 176 `.freshInitiator` | match |
| 134 | `&& expired(birthdate, REKEY_AFTER_TIME)))` | 177 `.freshExpired`, 120 s | match |
| 137-138 | `send` → queued initiation, `is_retry = false` | 178 `.freshSend` | match |

The constants agree with `messages.h:41-46` (`1ULL << 60`, 120); the
comparison is strict as in the C; the `&&`/`||` nesting is the C's
(`andM`/`orM`), so the clock is read only for an initiator under the counter
limit. The read of `sending_counter` agrees with the mirror's counter
convention (`atomic64_inc_return(..) - 1` is the old value, Send.lean:245-246).
No reference is taken, as in the C.

## 7. `calculate_skb_padding` (141-160) — `calculateSkbPadding` (Data.lean:52-59)

| C | Choice point | Lean | Status |
|---|---|---|---|
| 145-146 | `!mtu` → `ALIGN(len, 16) - len` | 53 `.padNoMtu` | **F8** (operands) |
| 154-155 | `last_unit > mtu` → `last_unit %= mtu` | 55 `.padOverMtu` | **F8** (operands) |
| 157-158 | `min(mtu, ALIGN(last_unit, 16))` | 58 `.padClamped` | **F8** (operands) |

Arithmetic recomputed: `alignPadding` is `__ALIGN_KERNEL(n, 16)`;
`MESSAGE_PADDING_MULTIPLE` 16 (`messages.h`); `min(x, y)` takes `y` on
equality and the mirror's `mtu < align` does the same; the result never
underflows (after 155, `last_unit < mtu`; otherwise `last_unit ≤ mtu`). A
keepalive (length 0, any MTU) pads to 0, so its message is 32 bytes, which
`create_data_done`'s keepalive test relies on (section 10). The length is
taken before `skb_checksum_help`, which does not change it.

## 8. `encrypt_packet` (162-219) — `encryptPacket` (Data.lean:70-96)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 173 | `skb_get_hash` (its `!l4_hash && !sw_hash` test, the flow-hash secret's one-time draw) | 73 `skipCut [.flowHashSecret]` | declared (cut, D4) |
| 176-178 | padding, `trailer_len`, `plaintext_len` | 74-75 | — |
| 183 | `skb_cow_head(..) < 0` → false | 78 `.encCowHeadFailed`, `hiddenAlloc .skbCowHead` (lax 0) | declared (D1) |
| 187 | `ip_summed == CHECKSUM_PARTIAL` | 82 `.encChecksumPartial` on `csum.isSome` | match |
| 188 | `&& skb_checksum_help(skb)` → false | 83 `.encChecksumHelpFailed`, `hiddenAlloc .skbChecksumHelp` (lax 0) | declared (D1) |
| 192-193 | `num_frags < 0` | 86-87 `.encCowDataFailed`, `.skbCowDataTx` (lax 0) | declared (D1) |
| 193 | `\|\| num_frags > ARRAY_SIZE(sg)` | 88 `.encTooManyFrags false` | declared (D2) |
| 199-209 | zero padding, header `{4, remote_index, le64 nonce}`, trailer | 91, 96 `dataMessage` | — |
| 213-215 | `skb_to_sgvec(..) <= 0` → false | 94 `.encSgvecFailed false` | declared (D3) |
| 216-218 | `return chacha20poly1305_encrypt_sg_inplace(..)`: false on `WARN_ON(src_len > INT_MAX)` (chacha20poly1305.c:236-237) | 96 `some` unconditionally | **F5** |

The key is `PACKET_CB(first)->keypair`'s sending key for every skb of the
item (Data.lean:126 passes the head's), the nonce each skb's own, the
AEAD nonce 4 zero bytes then the little-endian counter, no AAD; the
`#guard`s at Data.lean:240-245 pin three messages.

## 9. `wg_packet_send_keepalive` (221-240) — `sendKeepalive` (Send.lean:261-269)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 225 | `skb_queue_empty_lockless(staged)` | 263 `.keepaliveStagedEmpty` | match |
| 226-229 | `alloc_skb(.., GFP_ATOMIC)` NULL → return (no send) | 266 `.keepaliveNoMem`, `hiddenAlloc .keepaliveSkb` (exact) | match |
| 230-233 | `mtu = dev->mtu`; `skb_queue_tail` | 268 `{ mtu := dev.mtu }`, appended | — |
| 239 | `wg_packet_send_staged_packets` | 269 | — |

## 10. `wg_packet_create_data_done` (242-260) — `createDataDone` (Data.lean:181-195)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 247-248 | traversal; any_sent (before any send) | 182-183 | — |
| 249 | `skb_list_walk_safe` | 188, 193 `.doneSkbIterate` | match |
| 250 | `is_keepalive = len == message_data_len(0)` (32), read before the send | 189 `MESSAGE_DATA_LEN_0` on the ciphertext | — |
| 251 | `!wg_socket_send_skb_to_peer(..)` | 190, 192 `.doneSendOk` | match |
| 252 | `&& !is_keepalive` | 192 `.doneNotKeepalive` (`andM`) | match |
| 256-257 | `data_sent` → `wg_timers_data_sent` | 194 `.doneDataSent` | match |
| 259 | `keep_key_fresh` (unconditionally) | 195 | — |

`wg_socket_send_skb_to_peer` (socket.c:168-186) is `sendSkbToPeer`
(Data.lean:151-164): the family switch, the `-EAFNOSUPPORT` free, `tx_bytes
+= skb_len` read before the send, with the item's `ds`. `send4`/`send6` are
Socket.lean's (W9), outside this audit.

## 11. `wg_packet_tx_worker` (262-285) — `txStep`, `txIter` (Data.lean:202-232)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 269 | `(first = wg_prev_queue_peek(..)) != NULL` | 205 `PrevQueue.peek`, 209 `.txPacket` | match |
| 270-271 | `&& state != UNCRYPTED` (the head left peeked) | 212 `.txNotUncrypted` | match |
| 272-273 | `drop_peeked`; `keypair = PACKET_CB(first)->keypair` | 216, 218 | — |
| 275-278 | `state == CRYPTED` → `create_data_done`, else `kfree_skb_list` | 219 `.txCrypted`, 222 | match |
| 280-281 | `keypair_put(.., false)`; `peer_put` | 223-224 | — |
| 282-283 | `need_resched()` → `cond_resched()` | 232 `.txNeedResched` (the scheduler's records) | match |

Per-peer serial order: items reach the tx worker only through the peer's
`prev_queue` (`txQueue`, FIFO, `PrevQueue.lean`), the worker stops at the
first `UNCRYPTED` head and resumes from the peeked item, so
`create_data_done` runs in enqueue order whatever order the encrypt worker
finished in, as in the C.

## 12. `wg_packet_encrypt_worker` (287-309) — `encryptStep`, `encryptIter` (Data.lean:108-145)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 293 | `ptr_ring_consume_bh(..) != NULL`; its `spin_unlock_bh` runs a pending softirq **after** the consume | 111 `softirq` (the NAPI poll), **then** 112-118 `consume`, `.encWorkerConsumed` | **F1** |
| 296 | `skb_list_walk_safe` | 125, 133 `.encWorkerSkbIterate` (the `false` only when the walk was not broken) | match |
| 297-302 | `encrypt_packet` → `wg_reset_packet` (cut), else `DEAD`, break | 126-132 `.encWorkerEncrypted` | match |
| 305 | `wg_queue_enqueue_per_peer_tx(first, state)` | 134 | — |
| 306-307 | `need_resched()` → `cond_resched()` | 145 `.encWorkerNeedResched` | match |

## 13. `wg_packet_create_data` (311-331) — `createData` (Send.lean:148-162)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 317-318 | `is_dead` → err with `-EINVAL` | 151 `.createDataDead` | match |
| 320-321 | enqueue per device and peer | 153 | — |
| 322-323 | `ret == -EPIPE` → enqueue per peer tx `DEAD` | 154 `.createDataEpipe` | match |
| 326 | `!ret` → return | 157 `.createDataOk` | match |
| 326-327 | `\|\| ret == -EPIPE` → return | 158 `.createDataOkEpipe` | match |
| 328-330 | keypair put, peer put, `kfree_skb_list` (no counter) | 159-162 | — |

## 14. `wg_packet_purge_staged_packets` (333-340) — `purgeStagedPackets` (Send.lean:205-208)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 336-337 | `tx_dropped += qlen` | 207 | — |
| 338 | `__skb_queue_purge`: `while ((skb = __skb_dequeue(list)) != NULL) kfree_skb` (skbuff.h) | 208 `staged := []`, no decision | **F4** |

`kref_release`'s purge (peer.c) is inlined in `peerPut` (Peer.lean:58-59)
with the same count: equivalent.

## 15. `wg_packet_send_staged_packets` (342-414) — `sendStagedPackets` (Send.lean:211-257)

| C | Choice point / effect | Lean | Status |
|---|---|---|---|
| 351 | `skb_queue_splice_init`: `if (!skb_queue_empty(list))` (skbuff.h) | none (214-216 test, then clear) | **F4** |
| 353-354 | `skb_queue_empty(&packets)` → return | 214 `.stagedEmpty` | match |
| 358-359 | `wg_noise_keypair_get(current_keypair)`: `!keypair \|\| !kref_get_unless_zero` | 218 `keypairGet` (`.keypairGetNull`, `.keypairGetZero`, Keypair.lean:18-25) | match (2) |
| 361-362 | `!keypair` → out_nokey | 232 `.stagedNoKeypair` | match |
| 363-364 | `!is_valid` → out_nokey | 235 `.stagedKeyInvalid` | match |
| 365-367 | `expired(birthdate, REJECT_AFTER_TIME)` → out_invalid | 236 `.stagedBirthdateExpired` (180 s) | match |
| 374 | `skb_queue_walk` | 241, 251 `.stagedNonceIterate` | match |
| 378 | `ds = ip_tunnel_ecn_encap(0, ip_hdr, skb)` | 243 (section 16) | — |
| 379-380 | `nonce = atomic64_inc_return(..) - 1` | 245-246 | — |
| 381-382 | `nonce >= REJECT_AFTER_MESSAGES` → out_invalid (no loop exit decision) | 249 `.stagedNonceRejected`, `branchCmp`, `2^64 - 8130` | match |
| 385-388 | terminate the list; `wg_peer_get(keypair->entry.peer)`; keypair to the head's CB; `create_data` | 255-257 | — |
| 392 | out_invalid: `is_valid = false` | 222-225 | — |
| 394 | `wg_noise_keypair_put(keypair, false)` (`!keypair` returns) | 226 (`.keypairPutNull`, noise.c:133) | match (3: null, unreference_now, kref) |
| 399 | `skb_queue_walk` | 227-228 `.stagedOrphanWalk` | match |
| 400 | `skb_orphan`: `if (skb->destructor)` (skbuff.h) | none | **F4** |
| 407 | `skb_queue_splice`: `if (!skb_queue_empty(list))` (skbuff.h); at the head | 230 `packets ++ staged` | **F4** |
| 413 | queued initiation, `is_retry = false` | 231 | — |

`REJECT_AFTER_MESSAGES` = `U64_MAX - (8192 - 64) - 1` = `2^64 - 8130`
(Send.lean:41-42 against `messages.h:34-46`); the measured operand
`0xffffffffffffe03d` (Decision.lean, `.stagedNonceRejected`) is that minus
1, the compiler's `> R - 1`. The splice back puts the packets ahead of
anything staged meanwhile, as `skb_queue_splice` does. The current keypair
is read from the peer state before the staged queue is cleared; nothing
writes it in between.

## 16. Helpers on the path

| C | Choice point | Lean | Status |
|---|---|---|---|
| queueing.h:163 | state `UNCRYPTED` | Send.lean:126 | — |
| queueing.h:167, queueing.c:74 | `!atomic_add_unless(&count, 1, MAX_QUEUED_PACKETS)` → `-ENOSPC` | 130 `.enqueuePeerQueueFull` on `txQueue.count ≥ 1024` (a peeked item uncounted, as `count--` is at dequeue) | **F8** (operands) |
| queueing.h:126-128 | `wg_cpumask_next_online`: `cpu >= nr_cpu_ids` → first (`-1 → 0`, then wrap) | 73-75 `.cpumaskWrap`; `encryptLastCpu` initially -1 (queueing.c:33) | match |
| queueing.h:174-175 | `ptr_ring_produce_bh` fails (`r->queue[r->producer]` occupied) → `-EPIPE` | 137 `.enqueueRingFull` on `PtrRing.full` | match |
| queueing.h:174, 176 | produce, then `queue_work_on` | 141 `queueDeviceWork`, then 142 `produce` | F2 (order) |
| queueing.h:186 | `wg_peer_get(PACKET_PEER(skb))` | 101-102 | — |
| queueing.h:108-109 | `cpu >= nr_cpu_ids` (initially `nr_cpumask_bits`, peer.c:43) | 84 `.chooseCpuInvalid` | match |
| queueing.h:110 | `\|\| !cpumask_test_cpu(cpu, online)` | 85 `.chooseCpuOffline false` | declared (D8) |
| queueing.h:113 | `for (i < cpu_index)`: `id % 1` = 0 | 90-91 `.chooseCpuIndexIterate` | match |
| queueing.h:188-190 | state; `queue_work_on` (PENDING from the record when held queued, ce038d4); put | 107, 116-119 | — |
| queueing.h:145 | `wg_prev_queue_peek`: `queue->peeked` | PrevQueue.lean:301 `.prevQueuePeeked` | match |
| queueing.c:84-85 | `tail == STUB`; `!next` → NULL | 279, 281 | match (2) |
| queueing.c:91 | `if (next)` | 288 `.prevQueueMoreRemain` | match |
| queueing.c:96 | `tail != head` → NULL | 292 `false`, `unsupported` | declared (D7) |
| queueing.c:100 | re-stub `next` | 294 `.prevQueueRestubNext true` | declared (D7) |
| if_vlan.h:612 | `eth_type_vlan(type)` | Send.lean:186 `.vlanTypeIsVlan`, `unsupported` | declared (D6) |
| ip_tunnels.h:560, 562 | `ETH_P_IP` → `tos`; `ETH_P_IPV6` → `ntohs(*(u16 *)h) >> 4` as u8; else 0 | 188, 190-192 | match (2) |
| inet_ecn.h:49 | `INET_ECN_is_ce(inner)` → `ECT_0` (2), else `inner & 3`; outer 0 | 200-201 `.ecnEncapInnerCe` | match |
| socket.c:174, 177, 182 | `AF_INET`; `AF_INET6`; `!ret` → `tx_bytes` | Data.lean:157-161 | match (3) |
| socket.c:194 | `alloc_skb` NULL → `-ENOMEM` (callers ignore it) | Handshake.lean:428 `.sendBufNoMem` | match |
| timers.c:147, 214, 35 (two) | `!timer_pending(new_handshake)`; `persistent_keepalive_interval`; `netif_running && !is_dead` | Handshake.lean:368, 414, 331-334 | match (4; the handshake audit, 2.10) |

`skb->protocol` for the dsfield is derived from the first nibble of the
staged bytes (Send.lean:172-178): 0 for a keepalive (`alloc_skb` zeroes
it), and for a `wg_xmit` packet the version nibble, which
`wg_check_packet_protocol` (queueing.h:70-74) has already equated with
`skb->protocol`.

`PtrRing` (PtrRing.lean) against `ptr_ring.h`: `__ptr_ring_full` is the
producer slot's occupancy (:49-52); `__ptr_ring_produce` writes and wraps
(:104-116); `__ptr_ring_discard_one` advances the head and clears
`head..tail` downwards once `head + 1 - tail >= batch` or the end is reached,
then wraps both cursors (:247-289); `batch` is `SMP_CACHE_BYTES * 2 /
sizeof(void *)` = 16, reduced to 1 above half the size (`__ptr_ring_set_size`).
All agree, including the clear loop's inclusive bounds.

## 17. Findings

| # | Class | Severity | C | Lean | Finding |
|---|---|---|---|---|---|
| F1 | 2 | O-p (fail-noisy with records) | send.c:293 `ptr_ring_consume_bh`: `spin_lock_bh; __ptr_ring_consume; spin_unlock_bh`, the pending NET_RX running at the unlock, after `__ptr_ring_discard_one`; receive.c:345-349 → send.c:388 → queueing.h:174 | Data.lean:111-112 `softirq` before `consume`; `Env/Batch.lean:104-116` | The pending NAPI poll is run before the ring poll. The design's justification (W4-W7 17.17: "the poll's reads do not depend on the encrypt worker's state (its ring and the tx queue)") misses one path: a poll that confirms a responder's new keypair (`wg_noise_received_with_keypair`) flushes the staged packets, so `create_data` **produces into the encrypt ring** and tests its producer slot, the slot the C's consume may just have cleared under the batch rule. Trace: an encrypt-worker run that consumed 15 items (tail 0, head 15, slots 0-14 still occupied); a responder peer A with staged packets; then one `wg_batch` of 1009 xmits to peer B (the ring is now physically full, producer at slot 0) and A's first data message, with the 17.17 schedule (the decrypt worker yields at `cond_resched` to the encrypt worker before NET_RX runs). Linux: the consume moves the head to 16, clears slots 0-15, and the poll's produce succeeds (A's packets are encrypted and sent; an encrypt queue record). Mirror: the produce meets slot 0 occupied, `-EPIPE`, A's list is `DEAD` and freed, a tx queue record instead. With records the queue records diverge (a hidden mismatch, a false rejection); without them, A's data messages are missing. A second variant (an empty ring at a re-queued instance's first poll) makes the mirror encrypt in the current activation the item the C leaves to a new instance: equal outputs, records that mismatch when the tx unit is not pending. No corpus trace has the schedule; settling it needs a deterministic replay instance built like `W7_CRYPT_AHEAD` (`evaluator/test_model_replay.py`), or the trace above run until the 17.17 schedule appears. The decrypt worker's twin (the receive audit's F6a, justified there because the poll reads the `rx_queue`) has the same structure; this audit did not re-examine it against the poll's writes. |
| F2 | 2 | I | queueing.h:174 produce, then :176 `queue_work_on` | Send.lean:141 `queueDeviceWork`, then 142 `produce` | The queue record is consumed before the item enters the ring. The full test (137) precedes both and nothing reads the ring between, so nothing differs; the twin of the receive audit's F5 (justified there). |
| F3 | 3 | I (fail-noisy, non-specific) | send.c:75 `!queue_work(handshake_send_wq, &transmit_handshake_work)`: false iff PENDING, which `process_one_work` clears when it takes the item, before the function's section | Send.lean:57 `.queuedAlreadyQueued p.handshakePending`; `Env.lean:260-263` clears the flag only when the environment dispatches | The rule ce038d4 introduced for the transmit unit (`peekQueuedUnit`: a queue record for a unit the mirror holds queued is the kernel's second queueing after its dequeue, Send.lean:116) and the device-level `unsupported` by name (`queueDeviceWork`, Defs.lean:2031-2035) were not applied to the handshake send unit (nor to the clear unit, Timers.lean:63). If anything calls this function for a peer between its send work's dequeue and its section start (the case ce038d4 met live for the tx unit), the mirror takes `already_queued`, drops the reference and leaves the kernel's queue record to surface later as an unexplained mismatch. The second instance would be rate-limited by `last_sent_handshake` (send.c:25), so outputs agree; only the diagnosis and the decision stream differ. |
| F4 | 1 | I | skbuff.h inlines on the staged path: `skb_queue_splice_init`'s `!skb_queue_empty` (send.c:351), `__skb_queue_purge`'s loop (:338), `skb_orphan`'s `if (skb->destructor)` (:400), `skb_queue_splice`'s `!skb_queue_empty` (:407) | Send.lean:214-216, 208, 227, 230 | Four C choice points with no decision and no declaration. :351 is the same condition as :353's (declared) and :407 is always true after :353, so both are redundant; the purge loop is summarised by its count (each iteration only frees). `skb_orphan`'s arm depends on the skb's origin (a local socket's packet carries `sock_wfree`; a keepalive or forwarded packet none) and releases the sender's `sk_wmem_alloc` charge: below WireGuard's boundary, unobservable under the fixture's `SO_SNDBUFFORCE` (W4-W7 2.7), but recorded nowhere. Note the per-skb orphan walk at :399 is a decision while its body's branch is not. `kcov.json`'s `files` exclude `skbuff.h`, so the check cannot see these either. |
| F5 | 1 | I | send.c:216 `return chacha20poly1305_encrypt_sg_inplace(..)`; chacha20poly1305.c:236-237 `if (WARN_ON(src_len > INT_MAX)) return false` | Data.lean:96 `return some ..` | The function's last outcome is the AEAD's boolean, which the mirror fixes to success with no decision or comment. Structurally dead (a plaintext is at most 65535 + 15 bytes), the census P14 class ("the `WARN_ON`") would cover it if it named it; it names other WARN_ONs. |
| F6 | 6 | I | — | Send.lean:105-106 (`invariant` unless the head is on its peer's `tx_queue`); State.lean:69-71 (`freeTxSkb` on a dangling id) | Store-hygiene assertions with no C counterpart; they can only turn a mirror defect into a stop. Twin of the receive audit's F14. |
| F7 | — (documentation) | I | — | Send.lean:16-20, 22-27, 43-45, 55-56, 47, 63, 65-69 | Stale text in the module this audit reads first: the header says paths touched by the pending worker are `unsupported` via `requireNotPending` (retired 2026-10-14, State.lean:91-102) and that more than one item in a crypt queue is outside the domain (lifted by W7: multi-item `PrevQueue` and `PtrRing`, Send.lean:131); `sendQueuedHandshakeInitiation`'s docstring and comment rest on the retired guard ("requireNotPending excludes every other pending case"), which is also why F3's gap reads as covered. 47 and 63 are the no-op call and the vestigial `queuedThisCall`. `keypairGetCurrent` (65-69) is the receive path's NULL get (Receive.lean:418), defined here under a misleading name. |
| F8 | 3 | I | send.c:145, 154, 157-158 (`!mtu`, `last_unit > mtu`, `min`); queueing.c:74 (`count` against 1024) | Data.lean:53, 55, 58 and Send.lean:130: plain `branch` | Thresholds declared without operands (the receive audit's F9 pattern, fixed there by `branchCmp`): an MTU or a queue bound off by an amount that does not flip a trace's outcome is not caught by the operand check. The padding is partly guarded by the output (a different padding changes the message length); the queue bound only by the W7 tier's boundary traces (`w7_ring_1025`). |

Kernel behaviour notes for the tray are in section 19.

## 18. Hidden inputs on the path (class 5 check)

Consumed at the C's site and in its order: the coarse clock at send.c:25,
29, 39 (`.initRateLimited`, `.initLastSent`, `.initLastSentAgain`), :66
(`.queuedNotExpired`), :89, :101 (`.respLastSent`, `.respLastSentAgain`),
:134 (`.freshExpired`), :365 (`.stagedBirthdateExpired`); the queue records
of `queue_work` (:75) and `queue_work_on` (queueing.h:176, :188); the
section and resched records of both workers' `cond_resched` (:282, :306);
the allocation records at :226 (`.keepaliveSkb`, exact) and socket.c:192
(`.sendBufSkb`), and the lax ones at :183, :188, :192; the flow-hash secret
at :173 (a cut); the cookie nonce and `make_cookie`'s reads (cookie.c:190,
96-100); the timers' `jiffies` and jitter draws (timers.c:149-150, 185-186,
206, 216); `send4`/`send6`'s dst-cache and IP-stack records (Socket.lean).
Nothing on the path reads a hidden input the mirror leaves unconsumed. No
class 5 finding.

## 19. Kernel behaviour note (for the tray; not a tray entry)

**Staged packets can be stranded by the flush that should send them.**
Classification: DESIGN NUANCE, with a QUESTION. C (pristine 6.12.110):
`wg_packet_send_staged_packets` steals the whole staged queue
(send.c:350-352), reads `current_keypair` (:357-360), and on `NULL` puts
the packets back (:406-408) and queues an initiation (:413). The flush on
key confirmation, `wg_packet_consume_data_done` (receive.c:345-349), calls
the same function. If the confirmation's flush runs between another
caller's steal and its put-back (on SMP: `wg_xmit` on one CPU, the NAPI
poll on another; on one CPU: a process-context caller with BH enabled,
`set_peer` (netlink.c:482-483), `wg_set_device` (:577) or `wg_open` (device.c:55), with NET_RX run at :352 or
:360), it finds the queue empty and returns; the other caller then puts
the packets back with no key in view and queues an initiation that the
responder's `REKEY_TIMEOUT` rate limit (:66, `last_sent_handshake` set when
the response went out, :89, :101) normally suppresses. The packets then
wait for the next trigger: another `wg_xmit` to that peer, a persistent
keepalive, or the keepalive timer, which the confirming packet arms only if
it carries data (`wg_timers_data_received`, receive.c:365, comes after the
keepalive's `goto packet_processed`, :357-363). A confirming keepalive (what
an initiator with nothing staged sends, receive.c:180-186) arms nothing, so
a one-shot datagram can sit staged until unrelated traffic. The comment at
:401-405 accepts reordering here, not delay. Impact: latency, no loss
(bounded by `MAX_STAGED_PACKETS` trimming in `wg_xmit` and by the next
trigger). Reproducer: none in this corpus (the one-CPU oracle with no
interrupt-raised NET_RX gives no window in a netlink call); found by
reading during this audit. A reader without this repository would need an
SMP box racing a responder's first transmissions against the initiator's
confirming keepalive.

The uncounted drops on `-ENOSPC`, `-EPIPE` and the `DEAD` tx arm (send.c:
277-278, 322-330) are already tray report 01; not repeated.

## 20. Declared exclusions, verified and listed (not findings)

| # | C | Mirror | Declared in |
|---|---|---|---|
| D1 | `skb_cow_head`, `skb_checksum_help`, `skb_cow_data` failures (send.c:183-184, 187-189, 192-194) | `hiddenAlloc` lax 0: always success, a kernel failure record is left unconsumed (a stray record, fail-noisy) | `docs/2026-10-05-a-alloc.md` §6 table rows `skbCowHead`, `skbChecksumHelp` (with its non-allocation arms: GSO, frags, offsets), `skbCowData`; Data.lean header |
| D2 | `num_frags > ARRAY_SIZE(sg)` (:193) | constant `false` | census 2026-10-06 P14 ("too many fragments") |
| D3 | `skb_to_sgvec <= 0` (:213) | constant `false` | A §6.4 (class (d), not an allocation; a linear skb) |
| D4 | `skb_get_hash` (:173), `wg_reset_packet` (:299), the UDP tunnel transmit | cuts | Data.lean header; W9 |
| D5 | `REKEY_AFTER_MESSAGES`, `REJECT_AFTER_MESSAGES` on send (:132, :381) | modelled with operands, unexercised | census P6, D3 §9 |
| D6 | a VLAN-tagged skb (if_vlan.h:612) | `unsupported` | census P10 |
| D7 | `prev_queue` `tail != head` and the final `NULL` (queueing.c:96-97, 105) | `unsupported`; re-stub constant | census P5; W4-W7 §9 |
| D8 | `wg_cpumask_choose_online`'s online test (queueing.h:110) | constant `false` | `CONFIG_SMP` unset, `NR_CPUS=1`; Send.lean:77-79 |
| D9 | softirqs at the path's other BH-enable points (:352, :360, :408, :82, :135, :325, queueing.h:174) and timer sections nested mid-body | not run there: a NET_RX or timer section the scheduler cannot place is a hidden mismatch | D3 §5.3 and §9; `napiSoftirq`'s rule (Env/Batch.lean:104-116) |
| D10 | the census's unexercised send.c outcomes (`tx_worker.crypted` false, `create_data.epipe` true, `ok_epipe` false) | modelled | decision census §3: the W7 tier |
| D11 | `wg_socket_send_skb_to_peer`'s `else` on the data path (socket.c:180-181) | modelled, unreachable | decision census §3.1 |
| D12 | locks, RCU, barriers, `net_dbg_ratelimited`, byte layout | — | the altitude; no `DYNAMIC_DEBUG` |

## 21. Counts and verdict

Choice points walked: **82** (send.c 53, the helpers on its paths 29).
Status: **62 match**, **9 declared**, **11 F** (send.c:75 F3; :145, :154,
:157 and queueing.c:74 F8; :216 F5; :293 F1; :338, :351, :400, :407 F4).

| Severity | Count | Items |
|---|---|---|
| O | 0 | — |
| O-p | 1 | F1 |
| I | 7 | F2, F3, F4, F5, F6, F7, F8 |

By class: 1 — F4, F5; 2 — F1, F2; 3 — F3, F8; 6 — F6; documentation — F7.

**Verdict.** The transmit mirror follows `send.c`'s control-flow shape
closely: every conditional, loop, early return and error arm of the fifteen
functions has a declared decision in the C's order except the four skbuff.h
inlines (F4) and the AEAD's dead failure (F5); the `&&`/`||` structure is
kept where it decides what runs and what is read (`keep_key_fresh`'s clock,
`create_data`'s epilogue, the tx worker's peek); the constants (2^60, 120 s,
180 s, `2^64 - 8130`, 1024, 16, 32) and the padding arithmetic are the C's;
the state is the C's (a `prev_queue` per peer, the device's `ptr_ring` with
its batch rule, the skb store, `serial_work_cpu`, `last_cpu`); the per-peer
order of `create_data_done` is the queue's; the timer calls are in the
C's order relative to the sends; every hidden input is consumed at its site.
No item changes a verdict on a corpus trace. Fix first: **F1**, the NAPI
poll placed before the encrypt worker's ring poll, whose design
justification overlooks the poll's own produce into the same ring on key
confirmation — at the batch-clearing boundary of a full ring the C sends
what the mirror drops; place the poll after the consume (the C's order) or
show the case outside the domain with a fail-noisy stop; **F3**, carry
ce038d4's queue-record rule (or a named `unsupported`) to the handshake send
and clear units; **F7**, correct the module header and docstrings, which
still describe the retired pending guard and the lifted single-item limit.
