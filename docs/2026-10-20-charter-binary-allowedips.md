# Scaling binary refinement through the allowed-IPs component

Status: closed early as an experimental result; neither checkpoint A nor B
completed. See the [closing report](2026-10-20-binary-allowedips.md#experimental-close-and-landing-preparation)
for the measured result and redirection to a typed heap view. The target below
is retained as the original calibration target, not an achieved claim.
Independently reviewed; F2/F3 clarified below. The F1 mirror-counter
correction landed on main at `1f766662` and its binary witness now passes;
the original finding and unrestricted intended scope remain recorded below.
Worktree `.worktrees/binary-allowedips`, branch
`task/binary-allowedips`, starting from landed main
`1a69cebb93fc6c5b5adf010562c709e126413c3e`.
Start: 2026-10-20 01:25:17 UTC (preparation included).

[USER 2026-10-20] Continue the binary refinement experiment in a fresh worktree,
write and independently review this scaling charter, resolve findings, and
execute it. The objective is refinement of the mirrored WireGuard subsystem
under deliberately unrealistic context assumptions, with evidence about how
proof cost scales.

[AGENT 2026-10-20] Use allowed-IPs insertion followed by closure of the
allowed-IPs component as the next target. It reuses the proved lookup and
common-bits arithmetic while introducing allocation, structural mutation,
rollback, peer lists and reclamation. These are more informative scaling tests
than strengthening realistic caller or concurrency guarantees.

## Claim and completion criteria

For each supported operation, an executable entry assertion relates the actual
binary state to the actual mirror state. Given an accepted mirror execution and
the named sequential environment, decoder, permission and service hypotheses,
the compiled operation under Kraken reaches its ABI return with the same result
and reconstructed allowed-IPs state. The proof also exports its write frame,
consumed external inputs, updated identity interpretation and resources needed
for subsequent calls. Tests are for discovering these definitions; the theorem
must prove the same definitions, without a certificate checker or an assumption
that the desired execution or postcondition already holds.

Checkpoint A is complete refinement of `wg_allowedips_insert_v4`,
`wg_allowedips_insert_v6`, and their compiled `add` body, followed by the existing
lookup on the retained physical heap. Every mirror-supported insertion path is
included: invalid prefix/null-peer results at the internal entry, empty root,
exact-prefix reassignment, child attachment, covering-parent insertion,
intermediate-node insertion, all three allocation-failure sites, and rollback
after the second allocation fails. IPv4 and IPv6 are both required. A wrapper
with a successful return only is not completion of A.

Checkpoint B closes the mirrored allowed-IPs component: removal by peer,
clearing both roots, node readout, source/destination lookup wrappers and any
initialization modeled by the mirror. WireGuard-owned helpers and reclamation
callbacks reached by those operations are included; generic kernel allocation,
freeing and RCU queue management remain explicit environment services. Compose
arbitrary finite accepted sequences over one retained heap and evolving identity
interpretation. Include mixed-family trees, repeated updates, allocation
failures, deletion followed by address reuse, and clearing/reinsertion.

Each checkpoint ends with a function/sequence theorem, satisfying concrete entry
witnesses executed to return, a report of measured costs, and an exact trust
surface. No new completed function is counted merely because its physical
instruction regions or selected concrete paths run.

## Scope and trust boundary

Use Lean 4.35.0, the landed split mirror, read-only s5 oracle and the private
Kraken pin in `dependencies/sources.lock.json`. Keep existing image identities
and layouts checked by the existing scripts. Extend ISA support only when an
actual instruction demands it, in this worktree's private Kraken checkout with
focused semantic tests and reproducible patches. Never change shared inputs.

Assume serialized invocations and explicit external service outcomes. There is
no goal to prove realistic kernel contexts, allocator internals, interrupt
delivery or concurrent RCU. The theorem states these hypotheses openly. Existing
broader permission premises may be reused; strengthening first-return safety
is not a prerequisite for new WireGuard coverage. Retain proved callback
contracts and instantiate further width variants where the new image needs them.

Every new environmental premise is a named declaration in `binary/TrustBase.lean`
and appears in the headline, directly or through a printed named structure.
Allocator contracts describe failure or the returned zeroed allocation and its
ownership/frame; they cannot assume the trie linkage performed by WireGuard.
Free/RCU contracts specify release or enqueue effects, not correctness of
WireGuard's traversal, unlinking or callback bodies. Record the chosen deferred
release schedule and distinguish it from logical unreachability. Prove that
abstracting unreachable retired objects preserves subsequent supported reads.

Reconstruction covers the allowed-IPs projection only: roots, sequence counter,
node prefixes and keys, children, packed parents, node/peer ownership lists and
peer fields actually read or written. Unchanged WireGuard state is handled by
frames. Names and allocation identities have explicit provenance from entry
memory and actual allocation/release events. Mirror allocation counters can be
ghost state with proved updates; do not fabricate bytes or read the expected
mirror result to reconstruct binary state. Reuse of a retired address must not
silently identify two live mirror nodes.

Boundary correspondence is a proof convenience. Internal decision records stay
a separate differential-test channel, not an obligatory lockstep simulation.
No memory rematerialization or assumed fresh correspondence between calls.
Finite runtime traversal limits must be justified by the heap invariant for
universal proofs, and exhaustion fails loudly in tests.

Keep Rule Zero: a discrepancy is first a candidate mirror defect. Report and
minimize it, preserve its regression, and do not change the mirror or narrow
Pre/R to hide it. Machine-width edges, legitimate aliases, failed allocations
and dead-peer behavior are not silently excluded. If the intended theorem
requires a new domain restriction or target abstraction, expose the issue for
decision before claiming the affected path. Continue independent obligations.

## Execution sequence

### Operation interfaces and accepted domain (review F3)

| Binary entry | Mirror operation | Argument and result observation |
| --- | --- | --- |
| `wg_allowedips_insert_v4` / `_v6` | `insert 4` / `insert 6` | Decode the 4/16 network-order address bytes, the low 8-bit CIDR and a peer identity; compare signed 32-bit errno/success and the full allowed-IPs projection. |
| `add.isra.0` | `add` | Decode the actual root-slot pointer, width, key, byte CIDR and nullable peer; the NULL-peer error is an internal-entry case, not an invented public-wrapper argument. |
| `wg_allowedips_remove_by_peer` | `removeByPeer` | Resolve the peer from the entry pointer; the C return is void, so compare state and frame, not arbitrary RAX. |
| `wg_allowedips_free` | `free` | Both roots come from the same table; compare detached live state and new pending reclamations; C return is void. |
| `wg_allowedips_read_node` | `readNode` | Decode the live node; map mirror families 4/6 to target AF_INET/AF_INET6 2/10; compare the output CIDR byte and exactly 4/16 address bytes, preserving the other bytes. |
| `wg_allowedips_lookup_dst` | `lookupDst` | Decode protocol, network-header location and destination bytes from the supplied skb/header resource; map IPv4/IPv6 protocols to 4/6, other protocols to the source's miss case. Compare nullable peer pointer and count effect. |
| `wg_allowedips_lookup_src` | `lookupSrc` | Decode protocol and packet bytes at the actual network header, with mapped length covering the source address; compare nullable peer pointer and count effect. |
| `wg_allowedips_init` | Initial allowed-IPs value in device construction | Compare NULL roots and sequence 1; this is an initialization correspondence lemma, not a nonexistent mirror call. |

Addresses, CIDRs, protocols and output pointers arise from their ABI widths and
actual mapped bytes, not arbitrary unbounded source integers. The source's
explicit dying-peer lookup retry refusal remains outside accepted-run
termination and retains its executable binary-retry test. It is not a proved
returning path. Node/peer identities themselves remain unbounded logical names.

Checkpoint A must derive lookup's root from the table bytes preserved by
insertion. Lift the existing narrower lookup reconstruction to the new component
assertion using the proved lookup write frame: roots, sequence, packed parents
and ownership lists must remain related. Check that extended assertion on both
sides of each runtime lookup. Count this work as composition, not fresh
instruction semantics.

### Retired resources and the serialized schedule (review F2)

Maintain distinct live, retired and released allocations. Logical removal from
the mirror node store moves the physical resource to a retired-node or
retired-forest resource. The latter retains the actual child graph and bytes
that `root_free_rcu` will read; it is not reconstructed as live mirror nodes.
The `peer_list`/`rcu` union changes ownership when enqueued. The queue service
may write its declared union fields while preserving the callback's required
child bytes and allocation extent. Other calls frame those pending resources.

The environment supplies an explicit sequence of callback-dispatch events
between, never within, anchored API calls. A dispatch must name a pending node
or root callback. Its actual WireGuard body executes under Kraken; it stutters
on the already-erased mirror projection and consumes the retired resource.
Only an observed generic free-service call releases the allocation and makes
the address reusable. Rollback's direct free likewise releases its allocation.
No reuse is allowed merely because the object is unreachable. Finite API
sequences may leave named pending resources; draining them is an explicit
extension of the event sequence, not an implicit eventual-progress assumption.
Test clear, a later callback and reuse, as well as individual-node callbacks.
This model deliberately does not establish real RCU scheduling correctness.

### Review disposition

The independent review is
[2026-10-20-review-binary-allowedips-charter.md](2026-10-20-review-binary-allowedips-charter.md).
F2 is addressed by the lifecycle/schedule above; F3 by the operation inventory
and extended lookup-frame obligation. Their implementation remains work to do.
F1 is accepted as a Rule Zero finding: the current mirror uses Nat addition for
a physical u64 sequence counter observed by the dump. Exact unrestricted
closure requires a mirror correction or a separately approved target change.
Do not impose a non-wrapping Pre, silently take a modulo projection, or claim
that the review is clean. Execute and retain the boundary witness and report
the required mirror-lane action; continue the other segments meanwhile.

### Work order

1. Review this charter independently. Record each finding and its disposition.
   Bootstrap the private dependency and inventory the actual s5 symbol/call
   graph, layouts and existing executable/proof interfaces while review runs.
2. Build the extended executable reconstruction and allocation-event interface.
   Generate image/layout terms from the pinned ELF. Extend the paired runner
   for the new operations and retain the real machine state across calls.
   First exercise empty-root insertion, exact replacement and split/rollback.
3. Run the existing corpus's relevant operations through the mirror/kernel
   three-way comparison before relying on function probes. Add labeled
   constructed variations for shape, family, allocation failures and reuse.
   Failures identify the first violated assertion or unexpected binary exit.
   Capture selected real entry/service/return states through the existing QEMU
   capture machinery; clearly distinguish constructed states, recorded service
   substitutions and fully interpreted instructions.
4. Prove the tested insertion segments and loop invariant, compose both wrappers,
   and establish insertion-to-lookup without reestablishing correspondence by
   assumption. Use accepted mirror runs and the same executable assertions.
   Discharge ordinary shared coverage callbacks from their image proofs. Close A.
5. Extend to remove/clear/readout/wrappers and the WireGuard reclamation helpers.
   Test the evolving interpretation, lists and retirement assertions before
   proving the mutations. Compose the finite-sequence theorem and close B.
6. Review the resulting surface independently, fix findings, run scoped
   validation, prepare an exact-commit export, and report the result and costs.
   The external kernel gate remains the user's run outside Nono; continue
   independent work while that input is pending, without claiming acceptance.

## Scaling experiments and measurement

The deliverable is the refinement. Mechanisms earn their place by reducing a
measured repeated obligation in this work, not by prospective generality.

- Treat a segment as an execution result plus a compact mutation/frame/resource
  postcondition. Retain facts needed by consumers so a stronger composition does
  not require duplicating instruction proofs or every bookkeeping script.
- Factor tested update lemmas for list splices, packed parent slots and decoding
  after writes. Require two concrete uses before investing in a general tactic.
  Lemmas express reusable facts; tactics perform predictable search/iteration.
- Separate symbolic memory normalization from semantic invariant discovery.
  Diagnose slow reductions with small examples and narrower simp sets. Resource
  limits are a last resort, scoped to one declaration with an explanation.
- Keep capture and concrete execution costs visible; optimize only an observed
  bottleneck and preserve the meaning and completeness of the comparison.

Record wall-clock checkpoints for reconstruction/tests, invariant failures,
physical proof development, composition, validation and review. Record reused
versus newly proved functions/regions separately, source volume as a secondary
diagnostic, and how many invariants changed after proof began. Separate local
build, kernel replay and user external acceptance. Failed runs, KILLED banners
and timeouts are failures. Do not turn instructions per hour into a campaign
forecast. The central comparisons are new-function completion cost and the
additional cost of composing already proved operations.

## Validation and work discipline

Use the existing standalone binary gate, printed statements/trust diff, headline
axiom check and fresh kernel replay. Only the three standard axioms are allowed;
no sorry, native reduction axiom, unsafe proof path or kernel bypass. Extend the
existing gate's roots for the new surface, not a second audit framework. The
claim-point external gate is `lake check --from-export` over a successful
leanexport of that surface and its complete declaration closure. Document the
exact command and source commit; do not reuse old acceptance for new proofs.

Run builds/checks through `capped`, with `LEANUX_QEMU_SLOTS=16` for guest tests.
Keep one writer build per worktree to avoid artifact races; use Lake's ordinary
job parallelism without changing the root mirror's `-j1` setting. No global
configuration/cache changes, no main development, no push and no editing other
worktrees. A new capture hook is record-only work and must retain explicit image
identity; behavior-changing oracle work requires separate authorization.

Use one result-register row and one increment report,
`docs/2026-10-20-binary-allowedips.md`, distinguishing A, B and partial work.
Record conclusions and reproduction commands, not giant traces. Commit useful
checkpoints and remove disposable artifacts when their conclusions are recorded.

The initial calibration checkpoint is after four elapsed hours from the start,
2026-10-20 05:25:17 UTC, or completion of A if earlier. It reports progress and
remaining costs and does not silently end the authorized work. Further work
continues toward B; reassess at each function completion. Stop speculative
mechanism work when its next use is unclear or its cost exceeds the repeated
obligation. If a semantic mismatch prevents the stated result, or a scope change
is needed, commit a reproducible finding and seek the necessary decision while
continuing independent work. Never report a partial proof as charter completion.
