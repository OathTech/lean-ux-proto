# Hidden inputs recorded at the source — design, 2026-10-03

Status: **proposed** [AGENT], for the user's decisions in section 7.
Principle agreed by the user on 2026-10-03.

## 1. The principle

Some Linux paths depend on values that are not in the trace:
- randomness;
- clocks;
- external inputs;
- later, scheduling.

[USER 2026-10-03] The mirror is a deterministic function of the trace plus
every hidden input the C consumed. Linux is in the lab, so the target is
instrumented to **record each hidden input at its source**: the value, plus
the identity of the call site. The mirror consumes the record, in order, at
the corresponding point. That read is part of the data and control
correspondence (way-forward plan, section 3).

Rejected as the primary mechanism:
- **Controlling the source** (a seeded RNG): it changes the system under
  test, and it does not extend to clocks or schedules.
- **Inferring values from outputs**: only works where a value happens to be
  emitted, and misses values that never leave the kernel (an ephemeral
  private key).

Today, hidden inputs are **assumed**: `envOk`, `World.timing`, and the send
worker's contract in `Env.runHandshakeWorkers`. Scheduling is **controlled**:
one CPU, `PREEMPT_NONE`, waits, and races declared outside the domain. This
design replaces assumptions with records where that pays.

## 2. Inventory (WireGuard; the FD slice has none beyond allocation)

Mirror-visible values (in packet bytes, state, decisions or the dump):

| Source | Site | Flows into |
|---|---|---|
| `curve25519_generate_secret` (32 random bytes, then clamped) | `noise.c:541` (initiation), `:688` (response) | ephemeral key, every encrypted field, `mix_dh`'s null test |
| `get_random_u32`, repeated on a collision | `peerlookup.c:132` | `sender_index`, index buckets; `wg_index_hashtable_lookup` (now `unsupported` once an entry exists) |
| `ktime_get_real_ts64` in `tai64n_now` | `noise.c:501` | the initiation's encrypted timestamp |
| `ktime_get_real_ts64` | `timers.c:197` | the dump's `last_handshake` (the mirror hard-codes `[0,0]`, which is wrong once wg0 completes an initiator handshake) |
| `ktime_get_coarse_boottime_ns` | `send.c:29,39,89,102`; `noise.c:396,637,650` | the rate-limit and flood tests and the keypair birthdate (today the `lastSentExpired` flag and the `Timing` contract) |

Not mirror-visible within the 4 s bound:
- the rekey jitter (`timers.c:150,186`), `jiffies` expiries, and the cookie
  and ratelimiter paths (under load, `unsupported`);
- keys drawn while the fixture is set up, outside the KCOV window;
- randomness below the cut (IP ident, UDP ports).

That last group is why hooks go at WireGuard's call sites, not inside
`random.c`.

## 3. The instrument

The constraints (checked in `kernel/kcov.c`):
- KCOV records only when the task's mode matches the hook (`check_kcov_mode`,
  `:170-191`). Calling the existing comparison hook in a coverage-mode run
  records nothing, and the coverage hook records only a return address.
- Remote sections are copied entry by entry, in order, into the trace's area
  at `kcov_remote_stop`.
- `kcov.c` is not instrumented (`kernel/Makefile:35`), so code added there
  adds no coverage points.

**Recommended: `kcov_record(site, data, len)` in `kcov.c`**, writing tagged
entries into whichever KCOV area is active:
- in coverage mode: a header word with non-canonical top bits (never a
  kernel PC), then the payload words;
- in comparison mode: four-word records whose type has bit 63 set.

It inherits from KCOV the per-operation reset, the remote copy, attribution
to the trace's handle, and ordering within the stream. It is about 40 lines,
with no locks, allocation or sleeping.

Hooks go on existing lines, the same technique as B2's patch, so the
coverage maps keep every line number:
- `noise.c:541`, `:688`, `:501`;
- `peerlookup.c:132`;
- later, the time sites.

**Plain fail-open hazard:** outside a KCOV context, `kcov_record` drops the
value silently, as coverage does. It is noisy only where the mirror expects a
record: underflow is an error.

Rejected alternatives:
- a side buffer or new KCOV mode (ioctl and mmap surgery, for nothing extra);
- ftrace (not configured);
- a debugfs ring (re-implements KCOV's handle logic, and needs a reader fd
  that breaks the fd fixture);
- printk (text, console side effects, no per-operation reset).

**The send worker** (now an environment contract) gets a remote section:
`kcov_remote_start(wg->kcov_handle)` around `send.c:51`, with the handle
captured in `wg_newlink`. The trace process inherits it from the guest's
parent. KCOV accepts only the common and USB handle subsystems
(`kcov_check_handle`, `:570-584`), so the handle lives in the device. The
crypt and tx workers would follow later.

The patch touches `kcov.c` and `kcov.h`, which add lines. Those files are
outside the anchored `kcov.json` files, so the shift is harmless to coverage,
but `scripts/apply-kernel-patch.py` rejects any line-count change. It needs
an allowlist for files that `kcov.json` does not anchor.

## 4. The two-run problem

The guest runs each trace twice: once collecting coverage (A1, A2) and once
collecting comparisons (A3). The two runs draw different random values.

**Recommended: record in both runs, and run the mirror twice.**
- Coverage run's records → mirror run 1 → A1 and A2.
- Comparison run's records → mirror run 2 → A3.

The children's returns stay required to be equal, since those are
deterministic.

Plumbing:
- `guest.c` splits tagged entries out before deduplication, and prints
  `LEANUX_HIDDEN` / `LEANUX_RHIDDEN` rows.
- `linux.py` merges the remote rows without deduplication.
- `check.py` passes each run's records to its own mirror run.
- A new stop kind, `hidden_mismatch`.

## 5. The mirror side

```lean
inductive HiddenSite | initEphemeral | respEphemeral | tai64nNow | indexDraw | ...
def hidden (site : HiddenSite) : M (List UInt8)
```

`hidden` consumes the operation's next record: task stream first, then
remote, in position order. It fails noisily on:
- a different site;
- a wrong length;
- underflow;
- leftovers at the end of the operation.

Site identity:
- **A declared site table**, printed by `leanux-model --hidden-sites`, like
  `--decisions`.
- **A cross-check:** the evaluator matches each record's hook address
  (innermost frame) against the declared file and line. That way the patch
  and the Lean table cannot drift apart silently.

The domain filter runs before Linux, so it has no records. There, `hidden`
returns a fixed, clamped placeholder. If the placeholder misled the filter,
the authoritative run still stops noisily. (A `hidden_dependent` flag on the
verdict was proposed; it is not implemented, since nothing would read it.)

## 6. Migration and scheduling

Recorded, in order of payoff:
1. The response ephemeral: stage C's 92 response bytes become comparable,
   closing its "contents not compared" gap.
2. The index draws, with the insert and bucket walk mirrored: this lifts the
   index-lookup `unsupported`.
3. The send worker becomes mirrored C (`create_initiation` with every value)
   rather than a contract.
4. Time: `last_sent_handshake`, the flood test, the birthdate and
   `last_handshake` become values instead of the `lastSentExpired` flag and
   the `Timing` contract.

`envOk` stays assumed: without fault injection, a recorded success bit buys
nothing.

**Scheduling.** On one CPU with `PREEMPT_NONE`, the remote stream's order is
already the order in which work items ran. A section record at each wrapper
(naming the worker) makes the environment a record-driven scheduler.

That also allows a guest change. Today the guest waits only in `wg_observe`,
before the reset, which would discard a section that ran during the wait.
Instead, it waits inside the operation that queues the work, as `wg_inject`
already does. Most uses of `requireNotPending` could then retire. (Retired
2026-10-14: docs/2026-10-11-dispatch-order.md, the last section.)

Hard later:
- RCU interleavings between readers and writers;
- atomics such as nonce counters;
- timers firing;
- multiple CPUs. A global sequence number in `kcov_record` could order
  records across CPUs.

## 7. Staged plan, and decisions

1. **Feasibility probe** in `.worktrees/hidden-inputs`, building a kernel
   under the worktree's `.artifacts`. The shared oracle is untouched. It
   consists of `kcov_record`, the four hooks, the send worker's section, and
   the guest changes (split the records, print full handshake datagrams,
   wait inside queuing operations).

   It proves feasibility if:
   - each response operation shows one clamped 32-byte response-ephemeral
     record, plus at least one index draw, in both children, with addresses
     resolving to the declared lines;
   - the initiation at the listener is reproduced byte for byte by
     `harness/noise.py` from the send worker's records, with no mirror change;
   - the existing check still passes on the probe kernel, with any changed
     witness spans recorded.

   A throwaway audit variant hooks the RNG itself, to enumerate every caller
   inside the windows and confirm the inventory.
2. **The instrument and evaluator:** a new oracle kernel profile and identity
   file, the applier allowlist, the guest, harness and check plumbing, and
   the Lean `hidden` API with its site table and cross-check.
3. **First consumer:** the send worker mirrored with every value, plus the
   response bytes.

   What it alone catches: a timestamp without `ALIGN_DOWN`, MAC1 over the
   wrong range, a wrong byte order, a skipped hash step. Each of those is a
   byte mismatch on a path that is an unchecked contract today. (An
   unclamped ephemeral cannot be caught: the hook follows the clamp, so the
   mirror instead requires each recorded secret to be clamped.)

   Negative control: shuffled or dropped records must stop with
   `hidden_mismatch`.

   Limit: the index-collision arm stays never evaluated.
4. **The initiator role:** `consume_response`, `begin_session` as initiator,
   and the keepalive through the crypt workers. The response depends on
   wg0's random values, so the harness must respond live. Either an
   in-guest C Noise responder, or a second serial channel to the Python
   initiator.

Decisions for the user:
- the oracle kernel change (step 2), as with every oracle change;
- relaxing the applier for files `kcov.json` does not anchor;
- the device handle (recommended) vs a USB-subsystem handle;
- wait placement and duration;
- the live responder mechanism (step 4);
- whether the time sites come with step 3 or later.

## 8. Feasibility probe: results [AGENT 2026-10-03]

The user approved the probe with the recommended choices: the device-struct
handle, waiting inside queuing operations, and the applier allowlist.

**Setup:**
- **Kernel:** profile `net-hidden`, built into the worktree's `.artifacts`
  (`kcov_record` at `ffffffff810f1a40`). The shared oracle is untouched.
- **Patch:** `kernel/patches/wireguard-hidden-inputs.patch` (sha256
  `108f6b74…` for the probe; `91a412ba…` after the send-worker section was
  extended to cover its `wg_peer_put`), applied on top of the B2 patch. Every anchored file keeps its
  line count; only `kcov.c` and `kcov.h` grow.
- **Guest:** splits records out before deduplication, waits 100 ms inside
  `wg_set`, `wg_up` and `wg_xmit`, and prints every datagram's bytes.
- **Analysis:** `scripts/probe-hidden-inputs.py`.

Results on the WireGuard suite (52 traces, run `probe2`):

| Criterion | Result |
|---|---|
| Records arrive in both children | yes. Per child: 18 initiation ephemerals, 17 clock reads, 29 index draws, 12 response ephemerals. Identical counts in both children; the values differ between them, as expected. |
| Call sites resolve to the declared hook lines | all records |
| Each handshake response carries a clamped response ephemeral and an index draw (remote stream, both children) | 12 / 12 |
| wg0's initiations at the listeners, rebuilt by `harness/noise.py` from the records | 15 / 15 distinct initiations, byte for byte |
| The send worker's records land in the operation that queued it | yes (`wg_xmit` 14, `wg_up` 2, `wg_set` 2) |
| Existing check on the probe kernel | 39 / 52 agree. The 13 failures are exactly the traces whose send worker ran. |

Notes:
- **One initiation failed after drawing its ephemeral** (`b1_low_order_peer`).
  With a low-order remote key, `create_initiation`'s ephemeral-static DH
  (`es`) is null, so it stops before the clock read and the index insert. The record sequence shows exactly the C's path.
- **No index collision occurred** (29 draws for 29 inserts), so the collision
  arm stays unexercised, as expected.
- **No witness span changed:** every stage C trace that does not queue the
  send worker agrees.
- **A guest bug in the probe was found and fixed:** a stale datagram buffer
  printed the previous observation's bytes again.
- **The audit variant was not run** (RNG hooks enumerating every caller).

**What the failures mean for the plan.** The send worker's section exposes
its code: `create_initiation`'s `kdf` and `mix_dh`, the send path, and the
keepalive timers. The mirror still treats it as an environment contract. So
the new oracle cannot replace the current one until step 3 mirrors the send
worker: **steps 2 and 3 land together.**

## 9. The instrument and its first consumer: results [AGENT 2026-10-03]

The user approved continuing as recommended. Steps 2 and 3 are implemented
on this branch; the change to the oracle needs the user's approval.

**What was built:**
- **Patch.** The send worker's section now also covers its final
  `wg_peer_put`, since the mirror reports that put's decisions. The patch's
  sha256 is `91a412ba…`. The proposed identity is in
  `kernel/identity-x86_64-net-hidden.txt`.
- **Guest.** Datagram and reply bytes are part of `wg_observe`'s
  observation.
- **Evaluator.**
  - The mirror runs once per guest child's records.
  - Each record's innermost call site is checked against
    `leanux-model --hidden-sites`.
  - Exit 5 is `hidden_mismatch`.
- **Mirror.**
  - The `hidden` oracle. Ephemeral records must be clamped, as the C
    guarantees at the hook.
  - The send worker with every value: `create_initiation`, MAC1, the rate
    limit, timers, and the index insert.
  - The handshake response with every value.
  - The index hashtable (insert, replace, remove, lookup) replaces the
    per-peer flag. Cookie and data lookups are now mirrored, no longer
    `unsupported`.
  - The environment runs send workers at the end of the operations that
    wait for them, and delivers datagrams over loopback.

**Full check** on `f7a25d4` (clean tree), kernel `net-hidden` (`vmlinux`
`fce9ecc4…`):

| Check | Result |
|---|---|
| Behavior, now including the bytes of every initiation and response | 1,325 / 1,325 traces agree (38,968 operations) |
| Control flow (task and remote) | all agree |
| Operands | 320,600 pairs match |
| WireGuard candidates rejected by the domain filter | none (stage C: 13, races with pending workers) |

**Mutants:** 23 of 25 are rejected. B2-M3 and C-M3 survive, as documented
before.
- **The new mutants:**
  - H-M1 to H-M4 change bytes: the unrounded timestamp, the MAC1 range, a
    big-endian index, the skipped PSK hash. Each is rejected by behavior,
    on 9 to 19 traces.
  - H-M5 omits a timer call. It is rejected by control flow.
  - H-M6, the negative control, reads the clock first. It is rejected with
    `hidden_mismatch`.
- **Three earlier mutants are now rejected through the record channel:**
  W5, B1-M1 and C-M1 take a different path, so the mirror asks for records
  Linux did not make. The record sequence is itself path evidence.
- **Retargeted:** B1-M4 targeted the removed send-worker contract. It now
  makes the mirrored worker ignore a null ephemeral-static DH, and a mirror
  invariant rejects it.

**What paid for itself:**
- **The records** made wg0's initiation and response bytes comparable. They
  turned the send worker from a contract into mirrored C, and lifted the
  index-lookup exclusion.
- **The two-run scheme** keeps A3 on the send worker's comparisons (1,249 to
  1,289 pairs on the WireGuard suite).

**Review.** An independent Fable review found one wrong state update: the
peer's release did not remove its handshake index entry (`peer.c:211`). It
is fixed. Every other finding is fixed or recorded here.

**Gaps:**
- **No in-domain trace can name a live index.** Traces are written before
  the run, so a lookup that finds an entry, and the bucket walk over one,
  stay unexercised.
- **The rate-limit return shares the epilogue,** so its true outcome has no
  witness.
- **`kcov_record` drops values outside any KCOV context.** Only the
  mirror's underflow notices.
- **Clocks other than `tai64n_now` are still assumed** (the
  `lastSentExpired` flag, `World.timing`).
