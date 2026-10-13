# WireGuard proof campaign

## Progress

Worktree `.worktrees/proofs-campaign`, branch `proofs/campaign`; base mirror
`c85e86b`. The [charter](2026-10-13-charter-proof-campaign.md) defines the
campaign. No mirror or kernel edits, no integration into main, no push.

| Result | Progress |
| --- | --- |
| R1 anti-replay | Complete with the intentional inclusive-floor correction; recorded replay, independent review and 24-statement proof gate pass over c85e86b. |
| R2 lifetime safety | Keypair operation endpoints, peer reference helpers, packet primitives and stale-cursor finding checked (47-statement gate); caller/lifecycle and internal-access coverage in progress. This is not yet the whole R2 claim. |
| R3 cryptokey routing | Read-only trie investigation; path proofs follow R2. |
| R4 delivery | Not started; drop characterisation waiting on W7 full-ring tier's explanation of the two drops. |
| R5 key lifetime | Not started; time half waiting on review items 7 and 8 on the timer model. |
| R6 flood resistance | Not started. |

## R1 — anti-replay uniqueness and the inclusive floor

[AGENT 2026-10-13] Reuse the existing pure counter-window model, exact S2
refinement, finite mirror-call refinement and committed runner observer for
R1. Add arithmetic bounds in the reusable `WG/CounterWindow` layer and export
the result from `WG/AntiReplay/Statements.lean`. This keeps the new proof
obligation at the small replay-state projection.

The original wording excludes counters **at or below** highest seen minus
8128. The proved wording excludes counters **strictly below** that boundary;
an unseen counter at equality may be accepted. Both the mirror's strict
`ctrTooOld` comparison and Linux `receive.c:counter_validate` implement this
inclusive edge, and Linux's `selftest/counter.c` explicitly tests acceptance
of zero after counters 1 through `COUNTER_WINDOW_SIZE`. This is an intentional
design nuance, not a mirror/kernel disagreement. The arithmetic statement
uses the one-based stored high-water mark to avoid natural-number subtraction
at an empty window.

**Architecture and refinement.** `CounterWindow/Bounds` proves the arithmetic
guard and preserves the 128-word bitmap through finite calls. The existing
`mirrorCalls_refines` identifies those calls with `accepted` and `finish`,
including the exact projected final state. `Keypairs/Evolution/Bounds` adds
`FloorHistory`: every earlier accepted nonce is at most 8128 above every later
one in the same allocation lifetime. `Inv.remembers` supplies the old
high-water bound; the validator's acceptance guard supplies the new bound.
`Evolution.floor` composes this through lifecycle and validator transitions;
the outer runner proof carries the invariant through the already checked
observer. `runner_floor` discharges all syscall contracts. Together with
`runner_uniqueness`, it quantifies over every successful original execution,
including arbitrary accepted record schedules and slot reuse. No new observer
copies or history fields were added. Committed-call coverage and discarded
scheduler probes retain the independently reviewed ReplayWindow interpretation.

**Rule Zero boundary witness.** A six-operation trace configures and brings up
wg0, observes its initiation, injects the recorded response, then injects valid
keepalives with wire counters 8200 and 72. Both return true in allocation
lifetime 1. The second is exactly at `8200 − 8128`. The record stream is a
reconstruction from the tracked `CONTENDED_ROAM_CMP` capture, with the two
authenticated datagrams from `rx_window.json`, widened legacy section identities
and monotonically adjusted clocks for the second data operation. This is an
accepted **non-placeholder mirror replay**, not a new Linux capture. The
original and logged runners produce identical JSON. The terminal theorem
`inclusive_boundary_witness` separately proves, by kernel reduction, that the
pure empty-window run `[8129, 1, 0, 1]` accepts exactly `[8129, 1]`.

Reproduce the recorded replay without QEMU or retained dumps:

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r1-inclusive-floor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/Logged/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

**Validation and effort.** The proof gate passes: 102 build jobs, 24 terminal
declarations (9 new R1 theorems), dependencies confined to the three permitted
standard axioms, token/import/default-target checks clean. The mirror is
byte-identical to `c85e86b`; ReplayWindow and R1 are current, no result lag.
The required fast unit tier ran 88 tests in 21 seconds, OK with one skip.
The initial build failed because its dependency scan preceded the newly added
root import; a fresh build resolved that dependency. Five local compile passes
resolved proof syntax and elaboration issues. R1 took roughly fifteen elapsed
minutes with bounded worker investigation and proof implementation; replay itself
took under one second. No differential check or guest was run.

**Independent review.** A worker uninvolved in the R1 implementation reviewed
the proof/source correspondence and observer coverage in two read-only passes.
No correctness defect was found. Its two reporting requests are addressed
above: distinguish the pure and runner witness counters, and identify the
record stream as reconstructed rather than a fresh Linux capture. It did not
run the build or gate; those results are the coordinator's checks.

**Ranked mirror-shape recommendations.** None: the existing named validator,
replay-state projection and proof-side lifetime evolution already make R1
routine. An observer/history field or a changed comparison in the mirror
would not preserve altitude and is not proposed.

## R2 — lifetime identity and retained references (in progress)

[AGENT 2026-10-13] Separate store identity from retained-reference provenance.
The existing keypair evolution can establish that a released allocation does
not return to the store, but this does not establish that a saved numeric slot
still denotes the allocation for which its reference was acquired. Keep both
obligations visible; do not count a counterexample to the latter as a proof or
refutation of the former.

**Checked component.** `Keypairs/Identity` derives monotonic allocation
frontiers, old-identity provenance, absence preservation and fresh reuse from
the existing `Evolution` relation. Its original-syscall and syscall-plus-ambient
corollaries discharge the evolution contract through ReplayWindow's S3.
A subsequent successful original getter cannot return an already absent,
previously allocated identity. The reachable-state `Inv` premise supplies the
frontier bound when starting with a resident identity. These are keypair-store
and operation-endpoint statements. They do not assert safety of every transient
access inside an operation. The peer and packet components below cover named
helper families; caller/lifecycle and internal-access obligations remain in
progress, not hidden hypotheses of a completed R2 result.

**Peer and packet primitive checkpoint.** `WG/Lifetimes/Store` is a reusable
allocation-frontier model. `Transition` preserves the provenance of every old
identity that remains; `Retained` only removes identities, with an unchanged
frontier. `Actions` composes contracts over finite sequences of **actual
successful original helper executions**, rather than assuming abstract store
steps. `Peers/Primitives` proves current getter identity, a conditional setter
contract, and retention/removal through `getPeer`, `peerGet`, and `peerPut`.
The raw setter is unconditional in the mirror: its proof therefore requires
that the replacement's identity equals the current resident's identity.

`Packets/Primitives` proves exact executions and contracts for all eight
TX/RX allocation, lookup, update and free helpers. Its independently stated
invariant bounds resident ids by the shared `nextSkb` allocation frontier.
It proves freshness, absence preservation and, directly, that after an actual
free no later successful primitive sequence can make a getter at that slot
succeed. These packet statements keep one device epoch; they do not cover
device deletion/recreation. The invariant does not assume TX/RX disjointness,
and the post-free proof uses same-slot emptiness rather than global absence.
Peer allocation, other callers and every internal access still need closure.

[AGENT 2026-10-13] Share projection contracts and allocation-frontier algebra
between peer and packet stores; preserve the fixed-device scope until the
original device lifecycle is proved. This avoids claiming raw skb numbers
identify allocations across device replacement.

**Concrete reference finding.** An eight-operation, explicitly recorded mirror
run creates 28 peers, starts a stepped dump, deletes wg0, creates a replacement
wg0, creates 27 replacement peers and receives a chunk, resuming the pending
dump. The receive returns the already queued first chunk; continuation
generation performs the destructive release. The first
dump retains raw peer slot 26, allocation identity 27, with two references.
Deletion removes the device while leaving the socket's dump cursor active.
The replacement device reuses slot 26 for allocation identity 55, live with
one reference. Resuming the dump calls `peerPut` on that new peer: its store
entry disappears while both the configured peer list and public-key table
still name slot 26. The old allocation does **not** reappear. This is a
retained-reference retargeting and table-coherence bug, not the charter's
narrower example of reading an old object after release.

The divergence is between accepted mirror input and the declared fixture
domain. `harness/guest.c` rejects deletion while a stepped dump is pending
(`wg_delete_with_dump_pending`); the W1/W2 design already calls for a
corresponding mirror rejection. `Env.wgDelete` currently checks worker idleness
but not the pending dump. Linux's dump context retains `ctx->wg`, whereas the
mirror context retains a Boolean and the resumed operation obtains the current
device. This is a mirror-domain finding, not evidence of a Linux lifetime bug.
No kernel experiment was run.

**Witness and refinement.** `Logged/Checkpoints` adds one read-only projection
after each original syscall, ambient step and all per-operation guards.
`checkpoint_runner_erasure` proves equality with the original runner's entire
JSON or indexed error for arbitrary projections and initial logs.
`checkpoint_observation_exact` proves the exact singleton append. Independent
source review confirms that this is the only added executable line; the
one-per-operation source coverage is not inferred from erasure alone.
`LifetimeSafety/Replay.lean` asserts the five relevant committed checkpoints,
the total checkpoint count and exact original JSON equality. The generated
record stream is synthetic, explicit and non-placeholder, not a Linux capture.

The terminal `stale_cursor_retargets_replacement` is a separate kernel-reduced
local witness: the actual `wgGetDeviceDone` callback on a retained cursor
releases replacement identity 55 and leaves the list/hash entries. The full
recorded trace reaches the same erroneous `peerPut` through the resume cleanup
in `wgGetDeviceDump`; these are distinct call sites and are not conflated.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

**Validation and effort so far.** The replay accepts and all assertions pass
in under one second. The gate passes 35 terminal statements (11 in R2), with
106 build jobs and only permitted standard axioms. The required fast unit tier
ran 88 tests, OK with one skip. The mirror remains byte-identical to `c85e86b`, and the existing
results are current with no lag. This checkpoint took about half an hour of
source investigation, three keypair compile passes and first-pass builds of
the checkpoint observer and local witness. The campaign continues with peer
and packet identity projections before claiming whole-result completion.

**Primitive checkpoint validation.** The full proof gate passes with 110
build jobs and 47 terminal statements (23 in R2), using only permitted standard
axioms. A separate read-only review found no defect in the shared store,
original-helper contracts or post-free corollaries; its requested scope limits
and module-heading correction are incorporated above. The implementation took
about 40 minutes and 19 compile/gate passes. A repeated anonymous hypothesis
unpacking tactic looped; that build was stopped by its verified PID and the
proof repaired. Other failed passes were proof elaboration/interface errors,
including duplicate generated match lemmas fixed by importing the existing
frame module before proving the peer contracts. No mirror semantics changed.
The required fast unit tier ran 88 tests, OK with one skip. R1, ReplayWindow and
the checked R2 components remain current over `c85e86b`; no result lag.

**Ranked mirror-shape recommendations.** (1) Restore the documented rejection
of device deletion with a pending stepped dump: altitude-preserving fixture
domain enforcement, outside this proof campaign's edit authority. (2) If that
domain is intentionally expanded, retain the actual device lifetime in the
dump context and discharge its reference at completion, following the C:
altitude-preserving, but a separate mirror design and differential-check task.
(3) Keep named allocation, deletion and same-object field-update boundaries
for all three stores: altitude-preserving operational structure that reduces
proof-side framing. No production history field is proposed.

**Independent checkpoint review.** A read-only worker found no defect in the
identity lemmas, generalized erasure or replay assertions. Its scope findings
are retained above: endpoint absence is not internal-access safety, and the
isolated callback is not the replay's call site. Its correction to the final
receive's queue behavior is incorporated; no finding is left undispositioned.
