# Correspondence audit: `Leanux/WG/Handshake.lean` against `noise.c`

2026-10-13, branch `task/audit-handshake` from `main` at 2c7a076. An
independent reading audit [AGENT]: no build, no checker run, no mirror change.
It reports every place where the mirror's control-flow shape differs from
the C's, by the six classes the brief names: (1) a C choice point with no
mirror choice point and no declared cut; (2) a mirror choice point out of the
C's order; (3) an arm resolved silently where the C branches on state; (4)
data of a different shape; (5) a hidden input the C reads that the mirror
does not consume there; (6) something the mirror does that the C does not.

## 1. Scope and method

- C: `drivers/net/wireguard/noise.c` (Linux 6.12.110, pristine), with the
  callers `receive.c:92-218`, `send.c:21-122`, and the helpers the module
  mirrors: `cookie.c:156-178`, `timers.c:30-39,145-217`, `socket.c:168-201,
  235-256`, `peerlookup.c:119-226`, `noise.h`, `include/linux/random.h:60-91`,
  `include/linux/rculist.h:181-187`, `include/net/ipv6.h:564-574`. The
  configuration `kernel/config-x86_64-net-choice`: `HZ=250`, no `SMP`,
  `PREEMPT_NONE`, no `DYNAMIC_DEBUG` (so every `net_dbg_ratelimited` is
  `if (0)`: no choice point); `kdf`'s `WARN_ON(IS_ENABLED(DEBUG) && ...)` is
  compile-time false.
- Mirror: `Leanux/WG/Handshake.lean` (505 lines) and the functions it calls
  in `Keypair.lean`, `Peer.lean`, `Receive.lean:213-316`, `Send.lean:43-63,
  259-269`, `State.lean:95-156`. Decisions and their C spans:
  `Leanux/Kernel/Decision.lean`; hidden sites: `Leanux/Kernel/Defs.lean:1007-1306`;
  declared cuts: `correspondence/kcov.json` (no `shared_exits`,
  `operand_exclusions` or `branch_free_functions` entry touches these
  functions), `docs/2026-10-06-future-proof-paths.md` 3(a),
  `docs/2026-10-04-d1-sprint.md` item 3, `docs/2026-10-06-wireguard-census.md` P5.
- Method: each C conditional, loop, early return and error arm in source
  order, matched to the `branch`/`branchCmp`/`branchExpired`/`unsupported`/
  `invariant` at a Lean line; each hidden read (`get_random_*`, `ktime_*`,
  `jiffies`, allocation) matched to its `hidden*` consumer and its position;
  each struct field to `Peer`/`Keypair`/`Device`. Locks, RCU, barriers,
  `memzero_explicit` of locals, byte layout and the primitives' internals are
  the altitude's exclusions and are not reported.

Line references are `noise.c` unless prefixed; Lean lines are
`Handshake.lean` unless prefixed.

## 2. Function tables

### 2.1 Mixing and message helpers (`noise.c:344-514`)

| C | Choice point / effect | Lean | Note |
|---|---|---|---|
| kdf 362, 370, 378 | `!dst \|\| !len` x3, `goto out` | 49-51 | six decisions; `orM` short-circuits as `\|\|`; the dst flags are the call site's pointer constants, as in C |
| derive_keys 396-401 | clock, then kdf, then birthdate/is_valid | 255-262 | `.deriveKeysBirthdate` read before the kdf, as 396 precedes 397 |
| mix_dh 411-416 | `!curve25519` -> false | 71-76 | `.mixDhNull`; key written only when the caller passes one |
| mix_precomputed_dh 424-429 | `!memneq(precomputed, 0)` -> false | 79-82 | `.mixPrecomputedNull` |
| mix_hash 432-440 | none | `noiseHash` | |
| mix_psk 448-450 | kdf x3, mix_hash(temp) | 221-223, 317-319 | inlined at both callers |
| handshake_init 458-460 | none | 100, 165 | |
| message_encrypt 467-470 | none | 180-181, 189-190, 225-226 | |
| message_decrypt 477-481 | `!decrypt` -> false | 85-89 | `.msgDecryptFailed` |
| message_ephemeral 490-494 | `dst != src` memcpy | 63-67 | `.msgEphemeralCopy`, the call site's constant |
| tai64n_now 501-513 | clock; ALIGN_DOWN(nsec, 2^24) | 145-150, 188 | `.tai64nNow` (16-byte timespec64) |

### 2.2 `wg_noise_handshake_create_initiation` (516-581)

| C | Choice point / effect | Lean | Note |
|---|---|---|---|
| 527 | `wait_for_random_bytes()` | none | I3 |
| 532-533 | `!has_identity` -> out | 162 | `.initNoIdentity` |
| 537 | handshake_init into the state | 165-166 | |
| 541 | generate_secret (random, clamp) | 168-169 | `.initEphemeral` records the clamped bytes; the mirror's clamp is idempotent |
| 542-544 | `!generate_public` -> out | 170-171 | `.genPublicNullSecret` (curve25519.h:50), `.initNoEphemeral` |
| 545-547 | message_ephemeral in place | 173-174 | I8 |
| 550-552 | es: `!mix_dh` -> out | 176-178 | `.initEsFailed` |
| 555-557 | s: encrypt, hash | 180-182 | |
| 560-562 | ss: `!mix_precomputed_dh` -> out | 184-186 | `.initSsFailed` |
| 565-567 | t: clock, encrypt | 188-191 | |
| 569-571 | index insert (unhash, random draws, two walks) | 192; Peer.lean:128-143 | `.indexDraw`, walk and collision decisions; the unhash at peerlookup.c:125 is I2; the stolen-index arm is D3 |
| 573-574 | state, ret | 193-194 | |

### 2.3 `wg_noise_handshake_consume_initiation` (583-665)

| C | Choice point / effect | Lean | Note |
|---|---|---|---|
| 599-600 | `!has_identity` -> out | 98 | `.consumeNoIdentity` |
| 602-605 | handshake_init, message_ephemeral (copy) | 100-102 | |
| 608-609 | es -> out | 103-104 | `.consumeEsFailed` |
| 612-614 | s: decrypt -> out | 106-107 | `.consumeStaticFailed` |
| 617-619 | pubkey lookup -> out | 109-110 | `.consumeNoPeer`; the bucket walk is D4 |
| 623-625 | ss -> out | 112-113 | `.consumeSsFailed` |
| 628-630 | t: decrypt -> out | 115-116 | `.consumeTimestampFailed` |
| 633-637 | replay (memcmp <= 0); flood (clock) | 119-123 | `.floodNow` read unconditionally, as 637 is; `.consumeFlood` is the comparison assigned at 635 |
| 639-640 | `replay \|\| flood` -> out | 124-125 | `orM` short-circuits as the C's test |
| 644-649 | copies; `memcmp > 0` -> latest_timestamp | 127-130 | `.consumeNewerTimestamp` |
| 650-652 | clock; `(s64)(last - now) < 0` -> last | 132-135 | `.consumptionNow`, `.consumeLaterTime`; I5 |
| 653-655 | state, ret_peer | 136-137 | |
| 662-663 | `!ret_peer` -> wg_peer_put(peer) | 94-96 | `.consumeFailedPut`, then `peerPut` (NULL-tolerant as the C) |

### 2.4 `wg_noise_handshake_create_response` (667-725)

| C | Choice point / effect | Lean | Note |
|---|---|---|---|
| 676 | `wait_for_random_bytes()` | none | I3 |
| 681-682 | `state != CONSUMED_INITIATION` -> out | 201 | `.respNotConsumed` |
| 684-685 | type, receiver_index | 202, 230 | |
| 688-691 | generate_secret; `!generate_public` -> out | 204-208 | `.respEphemeral`, `.respNoEphemeral` |
| 692-694 | message_ephemeral in place | 209-210 | |
| 697-699 | ee -> out | 212-215 | `.respEeFailed` |
| 702-704 | se -> out | 217-219 | `.respSeFailed`; I9 |
| 707-711 | psk; encrypt nothing | 221-226 | |
| 713-718 | index insert; state; ret | 228-230 | as 2.2 |

### 2.5 `wg_noise_handshake_consume_response` (727-814)

| C | Choice point / effect | Lean | Note |
|---|---|---|---|
| 744-745 | `!has_identity` -> out (no put) | 292 | `.crespNoIdentity` |
| 747-751 | index lookup (HANDSHAKE) -> out (no put) | 294-295; Peer.lean:212-226 | `.crespNoHandshake`; the walk, type test and `wg_peer_get_maybe_zero` are decisions |
| 753-761 | snapshot under the read lock | 302-303 | |
| 763-764 | `state != CREATED_INITIATION` -> fail | 304 | `.crespNotCreatedInitiation`; `fail` is `wg_peer_put` |
| 767-775 | message_ephemeral; ee, se -> fail | 306-315 | `.crespEeFailed`, `.crespSeFailed` |
| 778-783 | psk; decrypt nothing -> fail | 317-322 | `.crespDecryptFailed` |
| 790-793 | `state` recheck -> fail | 325 | `.crespStateChanged` |
| 794-801 | copies, state, ret_peer | 326-328 | |

### 2.6 `wg_noise_handshake_begin_session` (816-861)

| C | Choice point / effect | Lean | Note |
|---|---|---|---|
| 823-825 | `state != CREATED && state != CONSUMED` -> out | 267-269 | `andM` short-circuits as `&&` |
| 827-829 | keypair_create (kzalloc) -> out | 270-272; Keypair.lean:49-58 | `.kzallocKeypair`, `.keypairCreateNoMem`; counter |
| 830-832 | initiator flag, remote_index | 274-275 | |
| 834-839 | derive_keys, either slot order | 276-277 | `.sessionInitiator` |
| 841 | handshake_zero | 278; Peer.lean:191-195 | before the is_dead test, as the C |
| 843-845 | `!is_dead` -> add_new_keypair | 279-280 | `.sessionAlive` |
| 850-852 | `ret = index replace` (false when unhashed) | 284; Peer.lean:149-154 | `.idxReplaceUnhashed`; the false arm is D1 |
| 853-855 | dead: kfree_sensitive, ret false | 286 | D2 |

### 2.7 Keypair helpers (`noise.c:98-291`, `Keypair.lean`)

| C | Choice point / effect | Lean | Note |
|---|---|---|---|
| keypair_create 102-103 | `!keypair` -> NULL | 49-52 | |
| keypair_put 133-139; free_kref 126-128 | `!keypair`; `unreference_now` remove; kref release: remove, call_rcu | 31-41 | three decisions; the free is the store erase |
| keypair_get 146-148 | `!keypair \|\| !kref_get_unless_zero` | 18-25 | |
| add_new_keypair 210-249 | initiator; has next; the three puts | 61-77 | the C's order of writes and puts, on the snapshot pointers |
| received_with_keypair 262, 269, 280-287 | not new; changed; slide | 84-94 | |
| keypairs_clear 161-174 | next, previous, current | 98-107 | |

### 2.8 `wg_noise_precompute_static_static`, `expire`, `clear`, `init`

| C | Choice point / effect | Lean | Note |
|---|---|---|---|
| precompute 50-55 | `!has_identity \|\| !curve25519` -> memset 0 | Peer.lean:53-64 | short-circuit; the in-place write then the zeroing; I7 |
| expire 183-194 | handshake_clear; reset_last_sent (clock); next, current -> `sending.is_valid = false` | Keypair.lean:110-125 | `.resetLastSent`; `.expireNextKeypair`, `.expireCurrentKeypair`; I2, I7 |
| handshake_clear 91-94 | index remove; handshake_zero | Keypair.lean:129-131 | I2 |
| handshake_zero 80-85 | six fields | Peer.lean:191-195 | |
| handshake_init 70-72 | `peer_preshared_key` -> copy | Peer.lean:241-243 | `.handshakeInitHasPsk` |

### 2.9 Callers in `send.c` and `receive.c`

| C | Choice point / effect | Lean | Note |
|---|---|---|---|
| send.c:25-27 | `!expired(last_sent, REKEY_TIMEOUT)` -> return | 462 | `.initRateLimited` (clock `.birthdateExpired`) |
| send.c:29, 34-42 | clock; create; mac; traversal; sent; clock; send; initiated | 463-474 | `.initLastSent`, `.initCreated`, `.initLastSentAgain`; the C's order |
| send.c:51-52 (worker) | send; peer_put | 478-480 | I7 (Env.lean:263 clears `handshakePending` first) |
| send.c:89, 94-106 | clock; create; mac; begin_session; derived; traversal; sent; clock; send | 444-457 | `.respLastSent`, `.respCreated`, `.respSessionBegun`, `.respLastSentAgain` |
| send.c:118-121 (cookie) | message_create; reply | Receive.lean:213-216 | |
| receive.c:104-110 | cookie type -> consume, return | Receive.lean:220-222 | `.hsCookie` |
| receive.c:112-120 | under_load; `else if (last)`: decay, reset | Receive.lean:226-243 | `.hsUnderLoad` (`.underLoadNow`), `.hsWasUnderLoad`, `.hsDecayExpired` at 117 |
| receive.c:121-132 | validate; the three-way needs_cookie | Receive.lean:244-254 | `orM`/`andM` as the C's `\|\|`/`&&`; the invalid arm returns |
| receive.c:134-156 | initiation: cookie?; consume; `!peer`; endpoint; response | Receive.lean:257-266 | |
| receive.c:157-189 | response: cookie?; consume; `!peer`; endpoint; begin_session -> derived, complete, keepalive | Receive.lean:267-280 | `.walltimeLastHandshake` in `timersHandshakeComplete` |
| receive.c:192-195 | `!peer` -> WARN, return | Receive.lean:282 | `invariant`; unreachable from `wg_packet_receive`, as in C |
| receive.c:197-203 | rx stats; any_received; traversal; peer_put | Receive.lean:287-293 | I7 |
| receive.c:212-217 (worker) | consume; packet; kfree; dec; cond_resched | Receive.lean:298-316 | `.workerConsumed`; the decrement after the packet; I1 |

### 2.10 Cookie, timer and socket helpers in the module

| C | Choice point / effect | Lean | Note |
|---|---|---|---|
| cookie.c:163-166 | mac1; last_mac1_sent; have_sent_mac1 | 240-242 | |
| cookie.c:170-176 | `is_valid && !expired(birthdate, 115)` -> mac2 else zero | 245-249 | `andM`: the clock read only when valid, as `&&` |
| timers.c:35-37 | `running && !is_dead` -> mod_timer | 331-342 | `.modTimerRunning`, `.modTimerAlive`; `mod_timer`'s own arms are D5 |
| timers.c:147-150 | `!pending(new_handshake)` -> arm with jitter | 363-367 | the jitter drawn before the guard, as the argument precedes the call |
| timers.c:156-161 | running; `!pending(send_keepalive)` else need_another | 370-375 | |
| timers.c:170, 178 | del_timer | 378-383 | D5 |
| timers.c:184-186 | arm retransmit with jitter | 439-441 | `.retransmitJitter`, `.modTimerArm` |
| timers.c:194-197 | del; attempts 0; lastminute false; wall clock | 393-397 | |
| timers.c:205-206, 214-216 | arm zero-key; `interval` -> arm persistent | 400-408 | `.traversalKeepalive` is a comparison |
| random.h:76-80 | `for (;;)` u8 arm: `(u8)mult >= 256 % 83` | 353-359 | `(83 * r) % 256 >= 7`, `mult >> 8`; record-driven (review item 7) |
| socket.c:192-195 | `!alloc_skb` -> -ENOMEM | 421 | `.sendBufNoMem`; the callers ignore the result, as in C |
| socket.c:174-183 | AF_INET / AF_INET6 / else kfree; `!ret` -> tx_bytes | 422-435 | `send4`/`send6` mirrored (W9) |
| socket.c:239-253 | ETH_P_IP / ETH_P_IPV6 / -EINVAL; scope id | 486-496 | I4 |
| socket.c:304-305 | `endpoint_from_skb` ok -> set | 499-503 | |

Hidden inputs, in order of consumption, all matched to the C's read points:
`.initEphemeral` 541, `.tai64nNow` 501, `.indexDraw` peerlookup.c:132,
`.floodNow` 637, `.consumptionNow` 650, `.respEphemeral` 688,
`.kzallocKeypair` 100, `.deriveKeysBirthdate` 396, `.resetLastSent`
noise.h:103, `.initLastSent`/`.initLastSentAgain` send.c:29/39,
`.respLastSent`/`.respLastSentAgain` send.c:89/102, `.birthdateExpired`
(timers.h:28 at each caller), `.retransmitJitter`/`.newHandshakeJitter`
timers.c:186/150, `.modTimerArm` (jiffies), `.walltimeLastHandshake`
receive.c:179, `.underLoadNow` receive.c:115, `.sendBufSkb` socket.c:192.

## 3. Items

| # | Class | Finding | Observable? |
|---|---|---|---|
| I1 | 4 | `handshake_queue.ring` (a `ptr_ring` of 4096 slots, batch 16) is `Device.handshakeQueue : List` (Types.lean:445). The worker's consume (receive.c:212, Receive.lean:298-309) is shape-equivalent; the producer's full test (Receive.lean:423, `wg_packet_receive`, outside the audited functions) is a length test where the C tests the producer slot's occupancy, and consumed slots stay occupied until the batch of 16 clears them (ptr_ring.h:272). The mirror has `PtrRing` for the crypt queues. | No, inside the domain: the ring can only be that full with `handshake_queue_len > 2048`, which takes the trylock arm (receive.c:554-558) that Receive.lean:420-421 already stops as `unsupported`. |
| I2 | 1 | `hlist_del_init_rcu`'s `if (!hlist_unhashed(n))` (rculist.h:183), inlined at peerlookup.c:125 (`insert`'s first step) and :196 (`remove`, from `handshake_clear` :91, `keypair_put` :136, `keypair_free_kref` :126): `indexRemove` (Peer.lean:31-32) is a filter with no decision. `rculist.h` is not in `kcov.json`'s `files`, so the check cannot see it; nothing declares it. | No: both arms leave the entry absent. |
| I3 | 1 | `wait_for_random_bytes()` (527, 676) and `crng_ready()` inside `get_random_bytes_wait` (541, 688): a branch on global state with no mirror counterpart. Prose only (`docs/2026-10-12-simulation-target-review.md` "first external contract", `docs/2026-09-29-next-plan.md:311`); not in `kcov.json`. | No: the crng is ready before any trace (receive.c:552 guards the queue the same way). |
| I4 | 1 | `ipv6_iface_scope_id`'s `__ipv6_addr_needs_scope_id` test (ipv6.h:564-574, at socket.c:248): `endpointFromSkb` 493-494 resolves it with a plain `if` (no decision); the multicast arm is `unsupported`. `ipv6.h` is not anchored. | No for the fixture's link-local and global unicast sources; a multicast source stops. |
| I5 | 4 | `last_initiation_consumption` is `u64`, compared through `s64` casts at 635 and 651; `Peer.lastInitiationConsumption : Int` (Types.lean:276) and `hiddenClock .floodNow/.consumptionNow : Int` are unbounded, while the sibling clocks moved to `Int64` under review item 8 (`lastSentHandshake`, `birthdate`, `cookieBirthdate`). | No on a boot clock (wrap needs 2^63 ns). |
| I6 | 4 | `struct noise_handshake` is flattened into `Peer` (every field present: Types.lean:270-346); the `entry` nodes of the handshake and each keypair live in `Device.indexTable` with a `keypair` back-reference (Types.lean:92-99) instead of being embedded in their owner. Documented in Types.lean's header. | No. |
| I7 | 6 | `requireNotPending` stops (State.lean:95-97) in `peerPut` (Peer.lean:41), `peerGetMaybeZero` (:203), `precomputeStaticStatic` (:54), `expireCurrentPeerKeypairs` (Keypair.lean:111) and `sendQueuedHandshakeInitiation` (Send.lean:47): mirror-only domain guards at every reference change on the handshake receive path. | No wrong outcome: a handshake message for a peer whose `transmit_handshake_work` is queued (both ends initiating at once) stops as `unsupported` rather than being mirrored. |
| I8 | 6 | `createInitiation` 173 passes the constant `handshakeInitChainingKey` to `messageEphemeral` where the C reads `handshake->chaining_key` (546), the state the mirror wrote at 166. | No: the same value. |
| I9 | 6 | `createResponse` writes the `se` chaining key (702, in place in the C) only at 227, after `mix_psk` and `message_encrypt`; the `ee` key is written at 215. No choice point or state read lies between. | No. |

Declared cuts verified on the path (explicit, fail-noisy; not counted):

| # | C | Lean | Declared in |
|---|---|---|---|
| D1 | `wg_index_hashtable_replace` false (peerlookup.c:173-175, at 850) | 284 `unsupported` | d1-sprint item 3; census P5 |
| D2 | dead peer at `begin_session` (853-855) | 286 `unsupported` | future-proof-paths 3(a); census P5 |
| D3 | stolen index at insert (peerlookup.c:148-151) | Peer.lean:140 `unsupported` | census P5 |
| D4 | `wg_pubkey_hashtable_lookup`'s bucket walk (random siphash key) | Peer.lean:233-235, one decision | Types.lean:17-18 |
| D5 | `mod_timer`/`del_timer` internals (kernel/time/timer.c) | `armTimer`/`delTimer` with kind-303 records | Types.lean:13-14; D3 design |

## 4. Verdict

The module follows `noise.c`'s control-flow shape one-to-one: every
conditional, loop, early return and error arm of the 27 `noise.c` functions
on the handshake paths and of their five callers has a mirror decision at the
same position and in the same order, the `||`/`&&` tests keep the C's
short-circuit structure, the three-slot keypair rotation performs the C's
writes and puts in the C's order on the C's snapshot pointers, and every
hidden read (two ephemeral secrets, the TAI64N clock, the index draws, the
coarse-clock reads at their ten sites, the keypair birthdate, the two allocation outcomes,
the jitter bytes, the timer arms and the wall clock) is consumed at the C's
read point in the C's order. Counts: class 1, 3 (I2, I3, I4); class 2, 0;
class 3, 0 undeclared (D1-D5 are explicit, documented stops or cuts); class 4,
3 (I1, I5, I6); class 5, 0; class 6, 3 (I7, I8, I9). No item changes an
observable outcome on any trace inside the declared domain. Fix first: I2
(give `wg_index_hashtable_remove`'s `hlist_unhashed` test a decision, or
anchor and declare `rculist.h`, so the index table's removals are not the
one unreported branch on the path); I5 (hold `last_initiation_consumption`
and its two clock reads in the C's 64-bit width, as review item 8 did for
the sibling clocks); I1 (represent `handshake_queue.ring` with the `PtrRing`
the crypt queues already use, so the busy-arm stop is not the only thing
between the mirror and the ring's batch semantics).
