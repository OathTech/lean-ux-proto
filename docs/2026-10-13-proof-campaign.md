# WireGuard proof campaign

## Progress

Worktree `.worktrees/proofs-campaign`, branch `proofs/campaign`; base mirror
`c85e86b`. The [charter](2026-10-13-charter-proof-campaign.md) defines the
campaign. No mirror or kernel edits, no integration into main, no push.

| Result | Progress |
| --- | --- |
| R1 anti-replay | Complete with the intentional inclusive-floor correction; recorded replay, independent review and 24-statement proof gate pass over c85e86b. |
| R2 lifetime safety | Read-only architecture investigation. |
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
