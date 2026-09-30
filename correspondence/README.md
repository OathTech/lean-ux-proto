# Configured source and correspondence

These files relate the mirror to the native x86-64 Linux 6.12.110 build at commit
`fa5b06866b643cce7072a4e7c6be7ee3f0f1b95c`. The governing principle is in
[AGENTS.md](../AGENTS.md): abstract away C semantic detail, but keep data and
control-flow choice points aligned with the C. The design rules are in section 3
of the [way-forward plan](../docs/2026-09-29-way-forward.md).

## Where the correspondence lives

The correspondence lives in the Lean sources, not in a separate registry.

- **State.** `Leanux/Kernel/Defs.lean` has one structure per C struct:
  - `Fdtable`, `FilesStruct`, `Task`, `File` and `EventfdCtx`;
  - fields named as in the C;
  - pointers replaced by identities into finite owned stores (`TreeMap`);
  - fixed-size arrays for `fd[]` and the bitmaps;
  - `f_count` and `kref` kept explicitly;
  - `f_op`, `f_inode` and `private_data` as separate fields, written where
    the C writes them.

  The state is finite and comparable.
- **Functions.** `Leanux/FS/*.lean` has one Lean function per C function on the
  path, in modules named after the C files (for example `File.lean` for
  `fs/file.c`). Each doc comment gives the C lines it mirrors. Lock
  acquire/release, RCU and cut-point contracts are noted at the C's position.
- **Decisions.** `Leanux/Kernel/Decision.lean` has one constructor per C
  decision point. Each has its label, its condition site, and the source spans
  that run only for each outcome. The mirror records `⟨decision, outcome⟩`
  where the C evaluates the condition, in the C's order.
- **Unsupported paths.** Paths the mirror does not model end in
  `Stop.outsideDomain`, carrying the C site; mirror defects end in
  `Stop.invariant`. Neither is ever a silent default. Examples of paths
  outside the domain: blocking waits, table expansion, and waiters on the
  wait queue.
- **Environment.** Outcomes decided by the environment consult an explicit
  oracle (`EnvSite`); the harness oracle says every site succeeds. Examples:
  allocation, `ida_alloc`, `access_ok`, and user copies.

## Control-flow check (A2)

`python3 -m evaluator.check` reads the decision table from `leanux-model
--decisions`. It computes from the built kernel image which source lines own a
KCOV instrumentation point, and in which (inlined) functions
(`evaluator/coverage.py`). The scan:
- includes split bodies (`.cold`, `.part`);
- includes call sites of callees that tail-jump, directly or conditionally,
  into `__sanitizer_cov_trace_pc`;
- fails if a listed function or a called symbol is missing, or if a function
  owns no point.

`kcov.json` lists the anchored files and the functions to scan.

**Which points count** [AGENT 2026-09-30, WireGuard stage A]:
- Only PCs whose outermost DWARF frame is a listed function witness
  decisions, in A2, the order check and A3. The instrumentation map is built
  from the same functions. The netlink core inlines the same header helpers
  (refcounts on skbs and sockets), which would otherwise pollute witnesses.
- A point whose outermost frame names a header line lies outside every inline
  range. The compiler merged a block, such as the join after an inlined `if`,
  and the line table gives it the header's last line. Such points count
  neither in the map nor as witnesses. On the current kernel this drops 6
  of 1,075 points; one of them would falsely witness `fdput.fdput_fput=1`.
- A decision's C function may own no point only if `kcov.json` lists it in
  `branch_free_functions` and both outcomes are declared `branch_free`. Today
  that is `fls128`.

An outcome's **witnesses** are the instrumented lines of its span. Blank lines,
braces, labels and comments are dropped from spans; statements are kept.

**Loading the table** fails unless:
- labels are unique;
- spans are in anchored files, inside the file, within a window around the
  condition line, and do not overlap between outcomes;
- the condition line is a statement;
- every decision's C function (the label prefix) owns instrumentation.

**The reason rule.** A side with no witnesses must declare why (below), and a
declared reason on a witnessed side fails. So a reason can neither be missing
nor hide evidence.

**Per operation**, each of the following fails the check:
- a decision reported more than once;
- a reported outcome that covers none of its witnesses;
- a reported outcome whose opposite outcome's witnesses are covered;
- a decision the mirror did not report, but whose witnesses Linux covered;
- a covered line inside a span that the instrumentation map does not know
  (raw coverage: any function, any attribution);
- a span line of an anchored `.c` file covered by a function not listed in
  `kcov.json` (a modeled path running outside the listed functions);
- an unknown label, or an operation with no decision;
- coverage only outside the anchored files.

**Order.** The guest records each PC once, at its first execution, in
execution order. Within each C function, the mirror's witnessed decisions must
appear in the mirror's order at their first covered witness in Linux's
execution.

**Operands (A3).** Each trace is rerun with `KCOV_TRACE_CMP`, and the rerun's
return values and read bytes must be identical. The decision table declares
which decisions are C value comparisons (`Decision.comparison`): the relation
as written (`lhs REL rhs`, or a mask test), and whether the right-hand side is
a compile-time constant. There are 80 such decisions (`leanux-model --decisions`).

Exactly the declared decisions report `(lhs, rhs)` (`branchCmp`); a missing
or undeclared operand pair fails. Some comparison record must match, where the
record's *innermost* source frame is the decision's condition line:
- Both operands must fit the recorded width; nothing is truncated.
- **Constant records** (KCOV puts the constant in arg1) need a declared
  constant. The variable must equal `lhs` exactly, and the constant may differ
  from `rhs` only as the relation allows (`x < 8` may appear as `x <= 7`).
- **Non-constant records** may list the operands in either order. The compiler
  canonicalizes operand order: `nr < max_fds` is recorded as `(max_fds, nr)`.

Decisions whose condition is not a comparison at that line report no
operands. Examples:
- pointer and NULL tests;
- `__fget_light`'s caller-dependent mask;
- the branch-free select in `eventfd_ctx_do_read`;
- `atomic_long_inc_not_zero`'s result.

`alloc_empty_file.nr_files_at_max` is deliberately not declared: its operands
are the system-wide `nr_files` and the boot-sized `max_files` (observed as
24,192), which the mirror does not model.

**Reasons** (`Unobservable` in `Leanux/Kernel/Decision.lean`):

| Reason | Meaning |
|---|---|
| `shared_continuation` | The outcome continues into code the other outcome also runs. |
| `shared_operand` | A short-circuit operand sharing its line or body. |
| `branch_free` | The value is selected without a branch. |
| `no_instrumentation` | The span owns no point; verified. |
| `compiler_shared` | A shared block is attributed to the span's line; commented at the decision. |
| `outside_domain` | A `BUG_ON` trap. |
| `constant_folded` | The configured build folds the test away. |
| `same_line` | A `WARN_ONCE` body on the condition's line. |
| `inline_helper` | Evaluated in a helper outside the span window. |

**Residual gaps**, which coverage alone cannot close:
- An unobservable outcome could be reported where the C never evaluates it,
  or omitted where it does. This affects arms like one-line `return -EINVAL;`
  error exits, which in this build own no instrumentation point. A
  "decision was reached" rule was evaluated and rejected: under DWARF
  attribution, condition-line coverage fails for 11 decisions whose condition
  lines are instrumented.
- Witnesses are keyed by source line, not by inline context. Within the
  listed functions, a header helper inlined at two sites shares its witnesses.
  Header span lines run by *unlisted* functions are ignored, not flagged,
  because header helpers are inlined everywhere (`fdput` into 83 functions,
  the refcount helpers into hundreds). A modeled path through an unlisted
  function that only runs header decisions is therefore not detected; the
  function list is kept complete by review.
- Covered lines in listed functions that belong to no span are not checked,
  so an unmodeled branch is caught only if it shares a span line.
- Order is compared only within a C function. Across functions, an arm's first
  witness can follow the decisions of a call nested inside it. Ties and
  unwitnessed steps are counted in the report (`order:` entries), not checked.
- A non-constant comparison's operand order cannot be checked, because the
  compiler reorders it. A swapped relation is caught by the outcome check,
  except when the operands are equal.
- Matching is existential over the records at the condition line. A C site
  evaluated several times in one operation, while the mirror reports it once,
  is not detected by A3.

These are mitigated by structural review of each function against the C.

The report's `decision_coverage` lists, per decision, how often each outcome
occurred. It also lists which outcomes KCOV can witness, which decisions the
corpus never evaluates, and which it sees with one outcome only.

## Configured source capture

`scripts/in-bundle python3 scripts/capture-correspondence.py`:
- reads the accepted kernel build's `.cmd` records;
- preprocesses the modeled translation units serially with the exact GCC
  command;
- writes `.i` files, line maps, the include closure with hashes, and a
  comparison of every source input against the pinned archive.

`--verify PATH` rechecks a captured manifest. `capture-v1.json` records the
retained capture. It is source provenance and a fixed C text for later proof
work, not evidence of agreement.

## Domain facts

The trace domain has these properties. `contracts/scope-v1.json` records the
same facts in machine-readable form.
- Fixture descriptors 0–7 are reserved. They are modeled as fixture files whose
  operations are outside the slice.
- `RLIMIT_NOFILE` is 32, while the initial table capacity is 64.
- Eventfds are nonblocking.
- The file status is computed as in the C: `O_RDWR | O_NONBLOCK` = 2050.
- Close-on-exec is descriptor-local.
- Descriptor references keep their number after close.

## WireGuard stage A abstractions

The mirror enters at `wg_set_device` and at the dump callbacks, with the
attributes `harness/wg.py` encodes. The following are cut points, stated at
their code:
- the generic-netlink core, policy validation and the dump machinery;
- the socket layer beyond `fdget`/`fdput` of descriptor 7;
- timers, work queues, NAPI, packet queues, `dst_cache`, RCU freeing;
- the index hashtable and the `hlist` helpers of the public-key hashtable. Their
  branches (`hlist_unhashed`, `if (first)`, an empty staged-packet purge) live
  in unanchored headers. They are constant on these paths, except the bucket
  order, which depends on a random key.
- the public-key lookup's bucket walk, reported as one `match` decision with
  the walk's result;
- the cookie keys (BLAKE2s);
- Curve25519, computed by an RFC 7748 reference (the build runs the x86-64
  implementation).

`swap_endian` in `wg_allowedips_insert_v4`/`_v6` has a constant width, so the
choice folds away and is not reported there; `wg_allowedips_read_node` reports
it. The device is down throughout: `netif_running` is false, and any path that
would send, open sockets or arm timers is `unsupported`. A dump larger than
3,000 bytes is `unsupported`, so the dump is always one message.

## WireGuard stage B1 abstractions (transmit and routing)

The fixture's sender sends UDP datagrams, and after `wg_up` the default routes
on wg0 take every non-local destination into `wg_xmit`. The following are cut
points, stated at their code:
- the IP and UDP output path, and `ip_tunnel_parse_protocol`. The protocol
  therefore always matches, so `wg_xmit.bad_protocol` is never true. An
  `AF_PACKET` sender would reach it, but this kernel has no `CONFIG_PACKET`.
- `dev_change_flags`, `__dev_open`, and `wg_socket_init` on a fixed, free
  port;
- ICMP generation on the error paths;
- queue locking, `skb_orphan`, and the timers the worker arms.

**The handshake worker is a contract**, applied when `wg_observe` has waited
for it (`runHandshakeWorkers` in `Leanux/WG/Send.lean`). It runs in a
kworker, outside per-task KCOV, so its decisions are not reported. It makes
`last_sent_handshake` current. It sends a 148-byte initiation iff the device
has an identity, the precomputed static-static is nonzero and the peer has an
endpoint, and a sent initiation adds to `tx_bytes`. Stage B2's remote
coverage can check the contract itself.

**Races are outside the domain.** Between queueing a peer's handshake and the
next `wg_observe`, the worker may run at any time. The exception is work
queued earlier in the same system call, before the call slept: the kernel is
`CONFIG_PREEMPT_NONE` on one CPU, so that work cannot have run yet.
`synchronize_net` and `flush_workqueue` (peer removal) end the exception. So the following are
`unsupported` while it is pending:
- queueing again;
- changing the identity, the endpoint or the static-static key;
- clearing the handshake;
- removing the peer;
- dumping.

`last_sent_handshake` is modeled as "expired" or "current", under the harness's
bound: a trace fails as an environment failure if it runs longer than 4 s after
`wg_up`, below `REKEY_TIMEOUT` (5 s). Endpoints other than loopback are
outside the domain once a handshake is sent, because the worker would route
them back into wg0.

**Harness facts** found on Linux:
- The kernel's RNG must be ready before any trace, since the worker calls
  `wait_for_random_bytes()`; the guest blocks on `getrandom` at batch start.
- Temporary sockets opened between operations must not use `SOCK_CLOEXEC`:
  `close` leaves the close-on-exec bit set, and the next descriptor
  allocation would observe it.
- The persistent-keepalive timer can fire within the bound: the worker arms it
  when it sends. It changes nothing observable, because once a handshake is
  queued the staged queue is never empty (no session drains it). So the
  timer's `wg_packet_send_keepalive` allocates nothing, and its requeue finds
  `last_sent_handshake` current. Stage B2, which completes sessions, will
  break this invariant.
- The 0.4 s wait is the harness's only timing assumption. A worker slower than
  that shows as a mismatch, since the datagram appears at the next observe;
  it is never an agreement.
