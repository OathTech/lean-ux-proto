# 03 — `wg_index_hashtable_lookup` stores the result of a refused peer reference back into the shared entry with a plain write under the RCU read lock, poisoning a field several paths dereference without a check

Target: Linux 6.12.110, `drivers/net/wireguard/peerlookup.c`,
`drivers/net/wireguard/noise.c`, `drivers/net/wireguard/noise.h`.
Configuration where it matters: SMP (the store and a concurrent reader on
another CPU); on the single-CPU oracle (`kernel/config-x86_64-net-choice`,
`CONFIG_SMP` off) the refused reference cannot happen. State: **Draft**,
not filed. Drafted 2026-10-15.

No patch branch (README §5).

## Affected code (pristine 6.12.110)

- `peerlookup.c:203-226`, `wg_index_hashtable_lookup`: under
  `rcu_read_lock_bh()` (:208) the bucket walk finds the entry, then
  `entry->peer = wg_peer_get_maybe_zero(entry->peer);` (:218) writes the
  get's result into the entry it found, and returns NULL when the get
  refused (:219-222). The store is a plain assignment, not `WRITE_ONCE`,
  under a read lock that excludes nothing but a grace period.
- `peer.c:71-78`, `wg_peer_get_maybe_zero`: NULL when `peer` is NULL or
  `kref_get_unless_zero` refuses (the count is already zero).
- `noise.h:30-31`, `:65-66`: the `struct index_hashtable_entry` is embedded
  in `struct noise_keypair` and in `struct noise_handshake`, so the word the
  lookup writes is `keypair->entry.peer` and `handshake->entry.peer`.
- Readers that dereference that word with no NULL test:
  `handshake->entry.peer->device` at `noise.c:91-92`
  (`wg_noise_handshake_clear`), `:570` and `:714` (the index inserts of
  `create_initiation` and `create_response`), `:827`
  (`keypair_create(handshake->entry.peer)`) and `:846-851` (the replace);
  `keypair->entry.peer->device` at `:121-126` (`keypair_free_kref`) and
  `:136-137` (`wg_noise_keypair_put`'s `unreference_now`); `PACKET_PEER(skb)`
  in the data paths (`queueing.h`).

## Classification

**DESIGN NUANCE, with a QUESTION.** The store-back is deliberate: the
function returns the entry and the caller reads `entry->peer` as the
reference it now holds (`:219-220` publishes it through `*peer` in the
same statement). Its argument for benignity holds as far as we can see:

- A NULL is written only after the get refused, which needs the count at
  zero. For a handshake entry that is possible only between
  `kref_put`'s decrement and `kref_release`'s unhash of the same entry
  (`peer.c:200-221`, the unhash at `:211-212`), a window that exists only
  on SMP or under preemption; `kref_release` itself reaches the device
  through `peer->device` (`:211`), not through `entry.peer`.
- A keypair entry is hashed only while its keypair is referenced; the
  entry's peer word outlives nothing it should not.

The question for the maintainers is whether the store is needed at all: a
local would carry the got pointer to the caller just as well, and the store
turns a refused reference into a NULL in a field that `wg_noise_handshake_clear`,
the two index inserts, `keypair_create` and the keypair release
dereference unconditionally. Under the kernel memory model the plain store
races with the plain loads of a concurrent lookup on another CPU (two
lookups of the same entry store the same value, so the race is benign in
effect, but KCSAN would report it).

## Reproducer

None in this corpus. On the oracle's single CPU without preemption the
refused get cannot occur (the lifecycle design, section 16.6, with the
lines), so no trace reaches the store of a NULL. A reader without this
repository would need an SMP machine and a race between `wg_peer_put`'s
last put of a peer and a handshake-kind lookup of that peer's entry on
another CPU, then a path that dereferences the entry's peer word; KCSAN on
an SMP build is the practical way to see the race itself.

## Expected versus actual

Expected: a lookup that refuses a reference leaves the shared entry as it
found it. Actual: it writes NULL into the embedded entry's peer word, which
later readers trust.

## Impact

None observed; none reachable on one CPU. On SMP, a data race in a field
that is read without synchronisation, with the consequences bounded by the
reference-count argument above. Attack feasibility: none identified.

## How this repository found it

The correspondence audit of `Leanux/WG/Peer.lean` against `peer.c` and
`peerlookup.c` (`docs/2026-10-15-audit-peer.md`, section 3.1), while
settling how the mirror should represent the store-back the binary
adequacy grind had found missing (the index-lookup fix of 2026-10-14).
Rule Zero, read in order: the mirror was wrong first (it kept a copy of the
word and did not store back; fixed); the kernel's own behaviour is this
report; the former was the finding, the latter is a question.

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so.
