# Correspondence audit: `Leanux/WG/Peer.lean` and `Leanux/WG/PeerRemove.lean` against `peer.c` and `peerlookup.c` [AGENT, independent audit, Claude Opus 5.5, written 2026-10-14]

A reading audit of `Leanux/WG/Peer.lean` (301 lines) and
`Leanux/WG/PeerRemove.lean` (146 lines) at `main` `ca6b22e`, against
`drivers/net/wireguard/peer.c` and `peerlookup.c` (Linux 6.12.110, pristine,
`.deps/linux`) and the C they call on the modelled paths: `refcount.h` and
`kref.h` (the gets and puts), `rculist.h` (`hlist_del_init_rcu`), `noise.c`
(`wg_noise_handshake_init`, `_clear`, `keypair_create`, `keypair_free_kref`,
`wg_noise_keypair_put`, `wg_noise_keypairs_clear`, `begin_session`),
`timers.c` (`wg_timers_stop`, `mod_peer_timer`), `allowedips.c`
(`wg_allowedips_remove_by_peer`'s head, `wg_allowedips_free`,
`root_remove_peer_lists`), `send.c` (`wg_packet_purge_staged_packets`, the
initiation the flush runs), `dst_cache.c`, `net/core/dev.c` (`napi_disable`),
and the oracle's patches (`kernel/patches/wireguard-hidden-inputs.patch`: the
index draw record) and configuration (`kernel/config-x86_64-net-choice`:
`NR_CPUS=1`, `PREEMPT_NONE`, `TINY_RCU`, no `DEBUG_LIST`, no
`DYNAMIC_DEBUG`, no `PROVE_LOCKING`, `BUG=y`). No build, no checker run, no
guest boot. Line numbers are the C file's and the Lean file's at `ca6b22e`;
`P:` is `Peer.lean`, `R:` is `PeerRemove.lean`, `K:` is `Keypair.lean`,
`Rc:` is `Leanux/Kernel/Refcount.lean`.

The `noise.c` static-identity functions that also live in `Peer.lean`
(`precomputeStaticStatic`, `generatePublic`, `setStaticIdentityPrivateKey`,
`cookiePrecomputeDeviceKeys`, `handshakeZero`, the birthdate helpers) were
walked by the handshake audit (`docs/2026-10-13-audit-handshake.md` 2.8);
they are read here only where `wg_peer_create` reaches them.

Classes, as in the earlier audits: (1) a C choice point with no mirror choice
point and no declared cut; (2) a mirror choice point out of the C's order;
(3) an arm the mirror resolves silently where the C branches on state; (4)
data of a different shape; (5) a hidden input the C reads that the mirror
does not consume there; (6) something the mirror does that the C does not.
**O** = could change an observable outcome on a trace; **I** = internal
correspondence only. Severity: High, Medium, Low. An exclusion recorded in a
design document with its reason is listed in section 4, not counted as a
finding.

## 1. Inventory

| C function | C lines | Mirror | Status |
|---|---|---|---|
| `wg_peer_create` | peer.c 21-69 | `peerCreate` P:260-292, `handshakeInit` P:253-257 | mirrored, order exact; dst_cache failure declared |
| `wg_peer_get_maybe_zero` | peer.c 71-78 | `peerGetMaybeZero` P:212-221 | mirrored; the zero arm unreachable by construction: F2 |
| `peer_make_dead` | peer.c 80-92 | `peerMakeDead` P:295-299 | mirrored, order exact; F4 |
| `peer_remove_after_dead` | peer.c 94-150 | `peerRemoveAfterDead` R:105-118 | mirrored; F1 |
| `wg_peer_remove` | peer.c 156-165 | `peerRemove` R:123-128 | mirrored, order exact |
| `wg_peer_remove_all` | peer.c 167-184 | `peerRemoveAll` R:133-144 | mirrored, order exact |
| `rcu_release` | peer.c 186-198 | none (folded into the release) | `call_rcu` a declared cut; F2, F3 |
| `kref_release` | peer.c 200-221 | `peerPut` P:56-62 | mirrored, order exact |
| `wg_peer_put` (+ `kref_put`, `__refcount_sub_and_test`) | peer.c 223-228 | `peerPut` P:50-56, Rc:10-16 | mirrored |
| `wg_peer_get` (peer.h 74-78) | | `peerGet` P:23-27, Rc:19-26 | mirrored |
| `wg_pubkey_hashtable_add` | peerlookup.c 35-42 | P:290 (`::` at the head) | mirrored |
| `wg_pubkey_hashtable_remove` | peerlookup.c 44-50 | P:298 | mirrored; F4 |
| `wg_pubkey_hashtable_lookup` | peerlookup.c 53-71 | `pubkeyLookup` P:244-249 | mirrored; bucket walk declared |
| `index_bucket` | peerlookup.c 73-81 | `indexBucket` P:121-123 | mirrored |
| `wg_index_hashtable_insert` (+ the draw) | peerlookup.c 119-164 | `indexInsert` P:140-156, `bucketHas` P:131-136 | mirrored; stolen index declared |
| `wg_index_hashtable_replace` | peerlookup.c 166-190 | `indexReplaceHandshake` P:162-167 | mirrored |
| `wg_index_hashtable_remove` | peerlookup.c 192-198 | `indexRemove` P:38-39, `indexRemoveKeypair` P:43-44, `unhashEntry` P:32-34 | mirrored |
| `wg_index_hashtable_lookup` | peerlookup.c 201-226 | `indexLookup` P:225-239 | mirrored; F5 (the store-back at :218) |
| `wg_timers_stop` | timers.c 235-243 | `timersStop` R:100-102 | mirrored |
| the flushes of `handshake_send_wq` | peer.c 106 (timers.c:242), 129 | `drainHandshakeSendWq` R:68-92 | mirrored by the dispatch records |

## 2. Function tables

### 2.1 `wg_peer_create` (peer.c 21-69)

| C | Choice point or input | Mirror | Status |
|---|---|---|---|
| 30-31 | `num_peers >= MAX_PEERS_PER_DEVICE` -> `-ENOMEM` | P:262-263 `.peerCreateMaxPeers`, a declared comparison with both operands; `MAX_PEERS_PER_DEVICE` = `1U << 20` (messages.h:48) = P:20 | match |
| 33-35 | `kmem_cache_zalloc` NULL -> `-ENOMEM` | P:264 `hiddenAlloc .kmemCacheZallocPeer`, `.peerCreateNoMem` | match |
| 36-37 | `dst_cache_init` fails -> `err` | P:269 constant `false` | declared (section 4) |
| 36 (dst_cache.c:150, dst_cache.h:79) | `dst_cache_reset`'s `jiffies` (kind 306) | P:284 `dstCacheReset` | match: consumed before the handshake init and the clock read, the C's order |
| 40 (noise.c:70) | `if (peer_preshared_key)` | P:254 `.handshakeInitHasPsk` | match |
| 40 (noise.c:50-51) | `!has_identity \|\| !curve25519(...)` | P:71, P:75 (short-circuit, the in-place write then the zeroing) | match |
| 55 (noise.h:100-104) | `ktime_get_coarse_boottime_ns` | P:287 `resetLastSentHandshake` (`.resetLastSent`) | match |
| 59, 61, 62 | `list_add_tail`, `wg_pubkey_hashtable_add`, `++num_peers` | P:289-291 | match |

Verified: `kref_init` is `Peer.refcount := 1` (Types.lean:262), `is_dead`
false, the timers, staged queue and handshake state zero by the structure's
defaults; `serial_work_cpu = nr_cpumask_bits` is `serialWorkCpu := none`
(Types.lean:298); `internal_id` comes from the module-global counter
(`Kernel.peerCounter`, the C's file-static `peer_counter`), which is the
right owner. The mirror assigns `internal_id` and the cookie keys (P:271-280)
before `handshakeInit`, where the C does it after (42, 46); no choice point
or hidden input lies between, so this is bookkeeping order, not a finding.
`pr_debug` (63) is compiled out (`DYNAMIC_DEBUG` off).

### 2.2 `wg_peer_get_maybe_zero` (peer.c 71-78) and `kref_get_unless_zero`

| C | Choice point | Mirror | Status |
|---|---|---|---|
| 75 | `!peer` | P:214 `.peerGetMaybeZeroNull` | match |
| refcount.h:145-146 | `if (!old) break` | Rc:42 `.refcountAddNzZero`, operands | match |
| refcount.h:147 | `atomic_try_cmpxchg_relaxed` fails, loop | Rc:43 `.refcountAddNzRetry` false (one CPU) | match |
| refcount.h:152 | `old < 0 \|\| old + i < 0` | Rc:44-45, two decisions; `old + 1 >= 2^31` is the C's overflow | match |
| 75 | `!kref_get_unless_zero` -> NULL | P:219 `.peerGetMaybeZeroDead` | **F2**: the arm exists but no mirror state reaches it |

`peerGet` (P:23-27) is `kref_get` -> `__refcount_add` (refcount.h:182-193):
the `!old` test and the `else if` overflow test, matched by Rc:19-26.

### 2.3 `peer_make_dead` (peer.c 80-92)

| C | Step or choice point | Mirror | Status |
|---|---|---|---|
| 83 | `list_del_init(&peer->peer_list)` (no branch: `DEBUG_LIST` off) | P:296 | match |
| 84-85 (allowedips.c:309-310) | `list_empty(&peer->allowedips_list)` -> return; the walk | P:297 `removeByPeer` (`.removeListEmpty`, then the walk) | match (the walk is `allowedips.c`'s, read only for its head) |
| 86 (peerlookup.c:48, rculist.h:183) | `hlist_del_init_rcu`'s `if (!hlist_unhashed(n))` | P:298, a filter, no decision | **F4** |
| 89 | `WRITE_ONCE(peer->is_dead, true)` | P:299 | match |

The order (list, allowedips, pubkey table, `is_dead`) is the C's.

### 2.4 `peer_remove_after_dead` (peer.c 94-150) and `wg_timers_stop`

| C | Step or choice point | Mirror | Status |
|---|---|---|---|
| 96 | `WARN_ON(!peer->is_dead)` | R:106-107 `.peerRemoveNotDead`, `unsupported` | match (stops where the C warns and goes on; unreachable) |
| 101 (noise.c:151-177) | `wg_noise_keypairs_clear`: next, previous, current, each put `unreference_now` | R:108 -> K:97-106 | match (each put's `!keypair`, `unreference_now` and `kref_put` decisions are K:31-40) |
| 106 (timers.c:237-241) | five `timer_delete_sync`, in the order retransmit, send-keepalive, new-handshake, zero-key, persistent-keepalive | R:101 over `PeerTimer.all` (Types.lean:356-357, the same order) | match (timer internals declared) |
| 106 (timers.c:242) | `flush_work(&peer->clear_peer_work)`: runs nothing unless pending | R:102 (`clearWorkQueue.contains pid`), then the drain up to that item | match |
| 116 | `flush_workqueue(packet_crypt_wq)` (encrypt, decrypt) | none (comment R:110-112) | **F1** |
| 118 | `flush_workqueue(packet_crypt_wq)` (the tx work the first flush queued) | none | **F1** |
| 120 (dev.c:6817-6820) | `napi_disable`: sleeps while `NAPIF_STATE_SCHED` | none (comment R:113) | **F1** |
| 124 | `netif_napi_del` | none | cut (NAPI, module note) |
| 129 | `flush_workqueue(handshake_send_wq)`: every queued item | R:115 `drainHandshakeSendWq none` | match |
| 148 | `--num_peers` | R:116-117 (an `invariant` below zero) | match |
| 149 | `wg_peer_put(peer)` | R:118 | match |

The drain (R:68-92) runs the items in the order the dispatch records name
them, stops on `upTo` after that peer's clear work, and is a hidden mismatch
when a queued item must run and no section names it; this agrees with the
flush semantics the W3 design verified (`insert_wq_barrier`,
`start_flush_work`, its section IV M2). The removed peer's own send worker,
run here after `is_dead`, is correctly not guarded by `is_dead` in
`wg_packet_send_handshake_initiation` (send.c:21-44) and has its timer arm
refused by `mod_peer_timer` (timers.c:34-36), as R:20-28 says.

### 2.5 `wg_peer_remove` (156-165) and `wg_peer_remove_all` (167-184)

| C | Step or choice point | Mirror | Status |
|---|---|---|---|
| 158 | `!peer` | R:124 `.peerRemoveNull` | match |
| 162-164 | `peer_make_dead`, `synchronize_net`, `peer_remove_after_dead` | R:126-128 | match (`synchronize_net` declared) |
| 175 (allowedips.c:258-279) | `wg_allowedips_free`: the two root tests | R:134 `free` (`.freeHasRoot4/6`) | match |
| 177-180 | first loop: each peer made dead, moved to `dead_peers` | R:135-139 `.peerRemoveAllIter1`, true per peer, false at the end | match |
| 181 | `synchronize_net` | R:140 | declared |
| 182-183 | second loop over `dead_peers` | R:141-144 `.peerRemoveAllIter2` | match |

Verified: `dead` is read after `free`, as the C's first loop runs after it;
`list_add_tail` onto `dead_peers` keeps the device's order, which `dead`
keeps; `root_remove_peer_lists` unlinks every node from its peer's list
(`listDel`, AllowedIps.lean:91-94), so each `peer_make_dead`'s
`remove_by_peer` takes the `list_empty` return, as in the C; the first
peer's flushes drain other peers' queued work (the W3 design's M2). No
reference is dropped between the loops, so no peer of `dead` is released
early.

### 2.6 `wg_peer_put` (223-228), `kref_release` (200-221), `rcu_release` (186-198)

| C | Step or choice point | Mirror | Status |
|---|---|---|---|
| 225 | `!peer` | P:51 `.peerPutNull` | match |
| refcount.h:269 | `old > 0 && old == i` | Rc:12-13, short-circuit | match |
| refcount.h:274 | `old <= 0 \|\| old - i < 0` | Rc:14-15, `unsupported` (saturation) | match |
| kref.h:64 (at 227) | released -> `kref_release` | P:56 `.peerKrefPutReleased` | match |
| 211-212 (peerlookup.c:196) | remove `&peer->handshake.entry`: the `hlist_unhashed` test | P:57 `indexRemove pid .handshake` (`.idxRemoveHashed`) | match |
| 217 (send.c:336-338) | `tx_dropped += qlen`, the purge | P:59 | match (`staged` holds values, not skb ids, so nothing leaks from the skb store) |
| 220 | `call_rcu(&peer->rcu, rcu_release)` | P:59 erases the peer at once; P:62 retires its work and timer units | **F2** |
| 191 | `WARN_ON(wg_prev_queue_peek(tx) \|\| wg_prev_queue_peek(rx))` | none | **F3** |
| 190, 196-197 | `dst_cache_destroy`, `memzero_explicit`, `kmem_cache_free` | none | cut (module note) |

The refcount arithmetic holds: the stored count is decremented (P:55) and
the decisions read the old value; the count starts at 1 from `kref_init`,
which is the device's reference dropped at R:118; peer ids are never reused
(`nextPeer`, P:273), so a stale id names nothing rather than another peer.
Retiring the work and timer units at `kref_release` rather than at the RCU
callback is safe: nothing can queue the peer's work once its last reference
is gone, and its addresses are not reusable before the free.

### 2.7 The public-key table (peerlookup.c 10-71)

| C | Step or choice point | Mirror | Status |
|---|---|---|---|
| 39-40 | `hlist_add_head_rcu` into `pubkey_bucket(remote_static)` | P:290, at the head of `peerHashtable` | match: entries with equal keys share a bucket, so the head-first order among equal keys is the C's |
| 48 | `hlist_del_init_rcu` | P:298 | F4 |
| 60-62 | the bucket walk and `!memcmp` per entry | P:248 one `.pubkeyLookupMatch` with the walk's result | declared (section 4) |
| 68 | `wg_peer_get_maybe_zero(peer)` | P:249 | match |

The table is keyed by the 32 bytes of `remote_static`, as the C compares
(62); `remote_static` is immutable after `wg_noise_handshake_init`
(noise.h:86-88), so the mirror's copy of the key is the C's field.

### 2.8 The index table (peerlookup.c 73-226)

| C | Step or choice point | Mirror | Status |
|---|---|---|---|
| 79-80 | `index & (HASH_SIZE - 1)`, 13 bits (peerlookup.h:35) | P:121-123, `% 2^13` over the global list | match: the global list is prepended at insert and rewritten in place at replace, so each bucket's filtered order is the hlist's |
| 125 | `hlist_del_init_rcu(&entry->index_hash)`: the unhashed test | P:142 `.idxInsertHashed` | match |
| 132 | `get_random_u32()`, recorded as the bytes of `entry->index` (patch line 161) | P:148-149 `.indexDraw`, decoded little-endian | match: the record is the `__le32` in memory, and the mirror's value is the raw `u32` the C masks and writes |
| 133 | unlocked walk, per entry | `bucketHas` `.idxInsWalk1` | match |
| 136-138 | collision -> `goto search_unused_slot` (a new draw) | `.idxInsCollide1`, `continue` to the next record | match: record-driven, ends only when the records do |
| 145 | locked walk, per entry | `.idxInsWalk2` | match |
| 148-151 | stolen -> `goto` | P:153 `unsupported` | declared |
| 157 | `hlist_add_head_rcu` | P:154 | match |
| 173-175 | `ret = !hlist_unhashed(&old->index_hash)`; false -> out | P:163-164 `.idxReplaceUnhashed` | match (the caller's false arm declared) |
| 177-186 | `new->index = old->index`, `hlist_replace_rcu`, `INIT_HLIST_NODE(old)` | P:165-166, the row rewritten in place as the keypair's | match on `main` (F5 for the branch) |
| 196 | `wg_index_hashtable_remove`: the unhashed test | P:39, P:44 `.idxRemoveHashed` | match |
| 209 | lookup walk, per entry | P:229 `.idxWalk`, false only when the loop ends without a `break` | match |
| 211 | `iter_entry->index == index` | P:230 `.idxMatch` | match |
| 212-214 | `iter_entry->type & type_mask`, then `break` either way | P:231-233 `.idxTypeMatch` on `kinds.contains` (HANDSHAKE = bit 0, KEYPAIR = bit 1, peerlookup.h:40-41) | match |
| 217 | `if (likely(entry))` | P:235 `.idxFound` | match |
| 218 | `entry->peer = wg_peer_get_maybe_zero(entry->peer)` | P:237, no store | **F5** |
| 219-222 | `if (likely(entry->peer))`, else `entry = NULL` | P:238 `.idxPeerAlive` | match |

## 3. Findings

| # | Sev. | C | Lean | Class | What | Effect |
|---|---|---|---|---|---|---|
| F1 | Medium | peer.c:116, :118, :120 (dev.c:6817-6820) | R:110-113 | 3 | The two `flush_workqueue(packet_crypt_wq)` and `napi_disable` have no mirror arm: the mirror neither runs the queued encrypt, decrypt or tx work (or a scheduled poll) nor stops. The W3 design (`docs/2026-10-06-w3-w12.md` I.8, V.1, V.5) says queued crypt work at a remove is **in reach and deterministic** (a session keepalive queued by an earlier entry of the same message: the first flush runs the encrypt worker, the second the tx work, which sends the datagram) and "stays `unsupported` meanwhile"; no `unsupported` exists. R:30-35 and R:110-112 rest it on `requireNotPending`, which is a no-op since 2026-10-14 (State.lean:91-102). `wgDestruct` has the guard this lacks (Device.lean:264-266). | O in reach: Linux sends the keepalive inside the remove; the mirror leaves the batch queued (it holds a peer reference, so the peer is not released) and runs it wherever the scheduler next finds its section. With records the divergence surfaces later as a hidden mismatch or a record at the wrong site (fail-closed by the instruments, but read as a mirror defect at a distant point); without records (the domain filter) nothing stops. Fix: an `unsupported` before R:113 when `encryptQueue`, `decryptQueue` or `txWorkQueue` is non-empty or the peer's `napiScheduled` is set, and the stale comments corrected. Settled by a run: a W3b-shaped trace (session established, one `wg_set` with peer A's keepalive then a remove) under `evaluator.check --suite wireguard`, expected `unsupported` after the fix. |
| F2 | Low | peer.c:220, :186-198; :75; peerlookup.c:219-222 | P:59, P:219, State.lean:29-32 | 4 | The RCU grace period is collapsed into `kref_release`: the mirror erases the peer when the count reaches zero, while the C keeps it readable at count zero until `rcu_release`. So the C's zero-count arms (`.peerGetMaybeZeroDead`; `.idxPeerAlive` false) cannot be reached by any mirror transition: a peer in the store has a count of at least one, and a lookup that found a released peer would stop at `getPeer`'s `invariant "dangling peer"`, not take the arm. | I on this configuration: with one CPU and no preemption no reader runs between the decrement and the unhash (I checked the argument of `task/index-lookup-fix`'s L 16.6 and agree: the handshake lookups run in a kworker; keypair entries are hashed only while the count is at least one). Fail-noisy, but it names a mirror defect where the C has a defined NULL. It also means that branch's "modelled and unexercised" wording and its two-lookup witness rest on a hand-built state the mirror's own transitions never produce. Either keep the peer in the store at count zero until a modelled callback, or say in the lifecycle design that the arms are unreachable by construction. |
| F3 | Low | peer.c:191 | P:56-62 | 3 | `rcu_release`'s `WARN_ON` on a non-empty `tx_queue` or `rx_queue` has no counterpart: the release erases the peer whatever `txQueue`/`rxQueue` hold. | I: unreachable while every queued batch holds a peer reference (Send.lean:255). If a mirror refcount slip breaks that, skbs naming an erased peer would surface later as `dangling peer`, far from the cause. An `invariant` at P:59 on non-empty queues is the C's own check, fail-closed. |
| F4 | Low | peerlookup.c:48 (rculist.h:183) | P:298 | 1 | `wg_pubkey_hashtable_remove`'s inlined `if (!hlist_unhashed(n))` has no decision; the identical test in `wg_index_hashtable_remove` and `_insert` does (`.idxRemoveHashed`, `.idxInsertHashed`, added for the handshake audit's I2 in 83109aa). | I: constant true on the modelled paths (`peer_make_dead` runs once per peer, after the create's add); both arms leave the entry absent. Add `.pubkeyRemoveHashed` (plain) at :48, or record why the pubkey copy is cut. |
| F5 | Low | peerlookup.c:218; noise.h:31, :66; noise.c:107, :70 | P:237; Types.lean:92-99 | 4, 6 | `wg_peer_get_maybe_zero`'s result is not stored back into `entry->peer`. On `main` this cannot change an outcome: the store writes something new only after a failed get, which F2 makes unreachable. The underlying shape is the handshake audit's I6: the C's entry is embedded in the handshake and in each keypair, so `entry->peer` is the same word as `handshake->entry.peer` and `keypair->entry.peer` (read as `PACKET_PEER(skb)`, Receive.lean:396, Send.lean:101, :255), while the mirror keeps an `IndexEntry.peer` copy in the table row beside `Keypair.peer`, and no handshake entry at all outside the table. | I on `main`. On `task/index-lookup-fix` (82334b3), see the branch assessment below this table: the store-back is made on the row only, and it brings in new divergences on the same unreachable arm. |

**`task/index-lookup-fix` against F5 (read-only).** That branch makes
`IndexEntry.peer : Option PeerId` and writes the get's result back into the
row whose index and kind match. That matches the C's data flow at the row,
but:

- (a) The aliases are not maintained. `Keypair.peer` and the handshake's
  entry keep the old id, so after a failed get the mirror's `PACKET_PEER`
  still names the peer where the C's word is NULL.
- (b) Rows with `peer = none` no longer match `indexRemove`, `indexHashed`
  or the insert's unhash, which all test `e.peer == some pid`. The C
  unhashes by address (`&peer->handshake.entry` at peer.c:211, noise.c:91),
  so a NULLed handshake row would survive its peer's release, and a later
  insert would leave two handshake rows.
- (c) `indexInsert` creates a fresh row with `some pid`, where the C's
  `handshake->entry.peer` would still be NULL. In fact the C would oops
  before that, at `handshake->entry.peer->device` (noise.c:570, :714).
- (d) `indexReplaceHandshake` carries the old row's `peer` into the
  keypair's row, but the C's new entry has `keypair_create`'s peer
  (noise.c:107).
- (e) The NULL dereferences the C would perform (noise.c:91-92, :570, :714,
  :827, :846-851 for a handshake entry; :121-126, :136-137 for a keypair
  entry) have no explicit arm.

The exact shape is the entry as a field of the peer's handshake and of
`Keypair`, with the table holding entry identities (handshake-of-`pid` or
keypair `id`), so that the store-back writes the one word. All of this is on
an arm F2 makes unreachable, so it is Low. It is still not the fix the
branch's commit message describes.

Altitude notes, not counted: `hlist_add_head_rcu`'s `if (first)`
(rculist.h, at peerlookup.c:39, :157) and `hlist_replace_rcu`'s
`if (new->next)` (at :178) are pointer fix-ups inside the list primitives,
with no counterpart in a list-shaped mirror and no effect on what is
hashed. No design names them; one sentence in the census would make them a
declared cut. `__skb_queue_purge`'s dequeue loop (send.c:338) is the same
kind of thing.

### 3.1 Kernel behaviour worth a note (not a tray entry)

`wg_index_hashtable_lookup` writes `entry->peer` (peerlookup.c:218) under
`rcu_read_lock_bh` only, with a plain store into an entry that other CPUs
read with plain loads. On success the store rewrites the same pointer. On
failure it writes NULL into the handshake's or keypair's embedded entry,
which other paths dereference unconditionally (`handshake->entry.peer->device`
at noise.c:91-92, :570, :714; `keypair->entry.peer->device` at :121-126,
:136-137). **Classification: design nuance, with a question.** It is benign
as far as I can see:

- A NULL is written only once the count is zero. For a handshake entry that
  happens only on SMP, between `kref_put`'s decrement and `kref_release`'s
  unhash, and `kref_release` uses `peer->device` (peer.c:211), not
  `entry.peer`.
- A keypair entry is hashed only while the count is at least one.

The question for maintainers is whether the store-back is needed at all,
since a local would do. The store turns a refused reference into a poisoned
field that several paths trust, and under the LKMM it is a data race (KCSAN
on SMP would flag the write against concurrent reads). Not reachable on the
oracle (one CPU). No corpus trace shows it. Found by reading, prompted by
the brief.

## 4. Declared cuts and exclusions verified (not findings)

- `dst_cache_init` failure (peer.c:36-37) as a constant `false` decision:
  [A](2026-10-05-a-alloc.md) 6.4 and 10; census row
  `wg_peer_create.dst_cache_failed` (a).
- The stolen index at insert (peerlookup.c:148-151) and the unhashed replace
  (:173-175 at noise.c:850): census 2026-10-06 P5; handshake audit D1, D3.
  The 64-collision bound: P7 (the mirror's loop is record-driven, so the
  bound is not built in).
- The dead-peer arms (`peer.c:75` second operand, `peerlookup.c:219` false,
  `begin_session`'s `is_dead`): census 2026-10-06 P5, handshake audit D2;
  F2 is about how the mirror's state expresses them, not about their scope.
- The public-key bucket walk (peerlookup.c:60-66) reported as one
  `.pubkeyLookupMatch`: handshake audit D4, netlink audit, Types.lean:17-18.
  Two remarks. The declaration's reason ("a random `siphash` key, so bucket
  order is unobservable") is stale: the key is now a recorded input stored
  in `Device.pubkeyHashKey` (L 429), so the walk could be computed. And the
  one decision is reported even when the bucket is empty and the C makes no
  comparison. Neither changes an outcome, since the false outcome has no
  witness lines (Decision.lean:909).
- `synchronize_net` (peer.c:163, :181) does not sleep on Tiny RCU with
  `PREEMPT_NONE`: L 2.2 and m1; State.lean:181-186.
- `call_rcu` freeing, NAPI add/enable/del, `dst_cache`, timers and work
  items as cut points: Peer.lean:10-14, Types.lean:13-15. `timer_delete_sync`
  internals: handshake audit D5. F1 is about the two crypt flushes and
  `napi_disable`, which the W3 design declares in reach and promises to stop
  on. They are not covered by these cuts.
- `wg_peer_remove_all` with queued work: not reachable in-syscall (W3 design
  IV M2; R:33-35); the drain still runs it as the kernel does.
- Work pending across system calls at a remove: retired as an exclusion
  with `requireNotPending` (State.lean:91-102); the dispatch records place
  it now. That retirement is why R:30-35 is stale (F1).
- The index draw's record (`KCOV_HIDDEN_INDEX_DRAW`, the patch's
  peerlookup.c hunk) is a record-only change of the approved class.

## 5. Verdict

The two modules follow `peer.c` and `peerlookup.c` closely. Every choice
point of `wg_peer_create`, `peer_make_dead`, `wg_peer_remove`,
`wg_peer_remove_all`, `wg_peer_put`/`kref_release` and the index-table
functions is mirrored at the C's line and in the C's order, with the C's
operands where declared:

- the refcount arithmetic, including the short-circuits inside
  `__refcount_sub_and_test` and `__refcount_add_not_zero`;
- the index draw as a recorded hidden input, with the collision retry
  driven by the records;
- the lookup's type mask and its `break`, and the replace's one condition;
- the dead-making order;
- the removal order around the `handshake_send_wq` flushes.

The pubkey table is keyed and ordered as the C's.

Walked: 49 choice points, 3 hidden-input sites (`dst_cache_reset`'s
jiffies, the last-sent clock, the index draw) and 1 data-flow point (the
store-back at peerlookup.c:218), 53 in all. Of these, 42 are matches, 4 are
declared (the dst_cache failure, the stolen index, and the pubkey walk's
loop and comparison) and 7 are findings: the two crypt flushes and
`napi_disable` (F1), the zero-count get (F2), the `rcu_release` WARN (F3),
the pubkey unhash test (F4) and the store-back (F5).

| Severity | Findings |
|---|---|
| High | 0 |
| Medium | 1 (F1) |
| Low | 4 (F2-F5) |
| In all | 5 |

By class: class 1, 1 (F4); class 3, 2 (F1, F3); class 4, 2 (F2, F5, the
latter also class 6). Only F1 can change an observable outcome, and it is in
reach.

Fix first:

1. **F1.** An `unsupported` at the crypt flushes and at `napi_disable`, as
   the W3 design already promises, with R:30-35 and R:110-112 corrected.
2. **F3.** The C's own `WARN_ON` as an `invariant` at the release.
3. **F2 and F5 together.** Decide whether the zero-count window is
   represented (the peer kept at count zero until a modelled RCU callback,
   and the index entry made a field of its owner) or declared unreachable by
   construction. `task/index-lookup-fix` should not land as is: per F5 (b),
   it adds a divergence on the arm it targets.
