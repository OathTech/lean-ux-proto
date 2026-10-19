# Independent review of proof campaign 1's landing

[AGENT, reviewer, Claude Opus 5.5, 2026-10-17]. Verdict: **land with the
named changes** (section 3). No finding blocks the landing. Five should-fix
items are wording, docstring and gate-hardening changes plus routing two
suspected mirror defects to the mirror lane. None of them changes a proved
statement.

## 0. What was reviewed and how

- Branch `proofs/campaign` at `6a357a90`. Its merge base with `main` is
  `b3f56807`, so the branch is current over main. I read it through Git and
  built a detached copy, `.worktrees/review-campaign1`, which is now removed.
  I did not enter the campaign's own worktree.
- I read the following against the C in `.deps/linux` (6.12.110): the charter
  (`docs/2026-10-13-charter-proof-campaign.md`), the campaign report
  (`docs/2026-10-13-proof-campaign.md`), the retrofit report and its findings
  (`docs/2026-10-16-proof-state-split*.md`), the register (`docs/proofs.md`),
  the R3/R4 extension reports (`docs/2026-10-17-r3-*`, `-r4-*`), the earlier
  reviews (`2026-10-13-review-r5-counterexamples.md`,
  `2026-10-12-spike-window-review.md`), the split design, and the mirror on
  main.
- Commands I ran in the detached copy:

| Check | Command | Result |
| --- | --- | --- |
| Proof gate | `capped -m 64G -- scripts/in-bundle scripts/proof-gate` | `Build completed successfully (973 jobs)`; `proof gate: PASS (860 terminal statements, axioms within ['Classical.choice', 'Quot.sound', 'propext'])`; exit 0; 16m25s wall clock on the contended host. Axiom sets: 849 × {propext, Classical.choice, Quot.sound}, 7 × {propext, Quot.sound}, 4 × {propext} |
| Kernel replay | `capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs` | exit 0, 1m55s, no output |
| Independent axiom audit | a Lean script that walks `env.header.moduleData` for each `Statements` module and the three findings/counterexample modules the root imports, then runs `collectAxioms` on every non-internal theorem and definition | 860 Statements declarations, the same count as the gate's regex list, so the gate misses none. The 58 declarations in `ReplayWindow.Counterexamples`, `Queues.RxCleanupFindings` and `Queues.PlaceholderFindings` use standard axioms only. Non-standard total: 0 |
| All published witnesses | the eleven recipes in the campaign report and `docs/2026-10-17-r4-full-ring.md` (R1 floor; R2 ×2; R4 GRO; R5 ×5; R6; W7), each `lake env lean --run …` | all exit 0, each in 0–15 s. Each one asserts original/observer JSON equality and its own endpoint checks |
| Mirror untouched | `git log --no-merges main..6a357a90 -- <mirror paths>`; for each of the 14 merges, `git diff <main-side parent> <merge> -- <mirror paths>` | no non-merge commit touches the mirror; every merge's mirror tree equals its main-side parent |
| Retype faithfulness | terminal-name diff for every `Statements.lean` between the validated pre-split baseline `00641c6` and `6a357a90`; textual diff of the R1, R5, R6 and window statements | ReplayWindow 15/15, R1 9/9, R5 13/13 and R6 6/6 names survive. Their statements change only `World` → `WGWorld × Ambient` threading, with the same premises and conclusions. R3 keeps all 141 old names. R2 loses 6 names (finding 9). R4 withdraws 1 name (finding 9) |

The branch's diff against main outside `Leanux/Proofs/` is wider than "the
gate script and the lake target". It contains:
- `scripts/proof-gate`;
- `lakefile.toml`, with the `LeanuxProofs` lib outside `defaultTargets`;
- `AGENTS.md` (+11 lines: the gate paragraph returns);
- `README.md` and `REPRODUCING.md`;
- a 20-line "Proof-domain qualification" inserted into the mirror lane's
  `docs/2026-10-13-review-items-7-8.md`;
- one trailing blank line removed from the split design;
- 34 new Markdown docs;
- two Python generators under `docs/`.

None of this is Lean code outside the proof tree. The user should know the
merge carries a standing-rule change to AGENTS.md (finding 13).

## 1. The six results as proved

What each headline theorem says, compared with what the charter asked. "Hypotheses" means premises beyond the mirror's own definitions.

**R1, anti-replay. Charter: no counter accepted twice in a lifetime, and nothing at or below highest − W accepted.**
`AntiReplay/Statements.lean:29` `runner_uniqueness` and `:39` `runner_floor`
quantify over every trace accepted by `Runner.executeTrace`. They give
uniqueness and `earlier.nonce ≤ later.nonce + COUNTER_WINDOW_SIZE` for any
two acceptances under one allocation identity, with no other hypothesis. The
pure and validator forms carry `backtrack.size = 128`, a shape fact that the
runner form discharges. The proved floor is inclusive. The C accepts equality:
`receive.c:306–310` increments `their_counter` and rejects only on
`W + their + 1 < counter` (counter = highest + 1). So the charter's "at or
below" is a **statement artefact**, correctly classified. The kernel
reduction `inclusive_boundary_witness` (`:91`, `decide`, pure model) and the
accepted runner replay (8200 then 72, re-run) both show it. The register row
states the difference.

**R2, lifetime safety. Charter: no later step reads or writes a released identity; a reused slot is a new identity.**
`LifetimeSafety/Statements.lean:1901` `runner_initialized_access_safety` holds
for every typed trace and both placeholder settings from the fixture, with no
other hypothesis. `:1892` `runner_audit_erasure` ties the observer to
`Runner.executeTrace`. The property is about allocation stamps
(`Lifetimes/Events.lean:17–23`): no read, write or allocate event carries a
released stamp.

What it does not exclude is a stale scalar slot that resolves to a
replacement object. The register row says this ("Raw-reference
affiliation/credit is a separate stronger property"). The historical Rule
Zero finding (a stale dump cursor) was a mirror defect. The mirror lane fixed
it in `c047e64` with user signoff, the guest confirmed the guard, and the
campaign did not edit the mirror. That is the three-clause reading working as
intended.

**R3, cryptokey routing. Charter: the trie agrees with the insert/remove history; a delivered packet's inner source is in the sender's allowed IPs; an outgoing packet goes to the owner of the longest matching prefix.**
- Trie half: there are refinement theorems from the original fixture for
  finite create/insert/remove/release/clear histories. The runner form is
  `parsed_initialized_routing_execution` (`:2503`).
- Incoming: `parsed_initialized_incoming_authorization` (`:4432`). Every
  Stack entry in the observer's journal has an earlier consume of the same
  receipt. The source address's flat longest-prefix winner, computed from the
  routing history strictly before that point, is the consuming peer.
- Outgoing: `parsed_initialized_transmit_authorization` (`:4643`). Every
  completed handoff selects the history's longest-prefix winner, and every
  packet's destination equals the routed address.

The hypotheses are `TraceAddressShape`, which successful `parseTrace`
discharges, and both placeholder settings. This is the charter's claim in
full strength, quantified over observer events (finding 3).

**R4, delivery. Charter: per peer and keypair, in receive order to the stack; no loss or duplication except at named drop arms.**
- Conservation: `DeliveryOrder/Statements.lean:3625`
  `accepted_runner_all_ingress_fates`. From acceptance alone, every accepted
  carrier is either in the final funded ledger (pending) or removed by an
  actual poll with a release certificate (`AdmissionRelease.Fate`,
  `Queues/AdmissionRelease.lean:16–20`). Stamp uniqueness excludes duplicate
  Stack entries. Neither eventual delivery nor fairness is claimed, and the
  register says so.
- Order: refuted after GRO. The accepted witness `ReplayGro` (re-run) has a
  held one-byte ACK on flow 40001 and a later SYN on flow 40002. The helper
  equation `original_gro_held_then_normal` (`:430`) is kernel-checked under
  the real classifier hypotheses. The property the C actually has, FIFO
  through the per-peer `prev_queue` up to `napi_gro_receive`, is proved only
  per poll: `original_poll_buffered_entry_subsequence` (`:536`). No run-wide
  pre-GRO order theorem exists (finding 1).
- W7: `two_carried_full_ring_result` (`:3688`) is kernel-checked for
  arbitrary payloads from two consumed-but-uncleared slots: 1022 successes,
  then two refusals. The finite accepted episode itself is compiled evidence
  (finding 6).

**R5, key lifetime. Charter: no encrypt or decrypt past `REJECT_AFTER_TIME`/`_MESSAGES`; no use of material after the zero timer until a new handshake.**
Thirteen local contracts, each about a single function: guards, staging
certificates, AEAD-attempt coverage and erasures. There is no run-wide
theorem. All three unconditional readings are refuted by accepted replays
(re-run): nonce R and R+1 authenticate before validator rejection; a keepalive
staged at 311 s is encrypted at 322 s after recorded expiry; packet-held
material is used after zero and clear. Classification: finding 7.

**R6, flood resistance. Charter: under load, an initiation with an invalid MAC2 gets only a cookie reply; retransmission stops after `MAX_TIMER_HANDSHAKES` attempts.**
`FloodResistance/Statements.lean:41` gives the exact cookie-only suffix and
`:53` shows the full Noise view is preserved, for any actual under-load run.
Its hypotheses are `FailedMac2`, an actual load and make_cookie execution, the
MAC1 match and the MAC2 mismatch. These are not strengthenings. The literal
retry limit is refuted. The C gives up on `attempts > MAX` (`timers.c:46`) and
itself reports `MAX + 2` attempts (`:49`): a **statement artefact**. A
replacement bound (at most MAX + 2 initiations) is not proved.

## 2. Findings

### Blocking

None.

### Should-fix before landing

**1. The R4 register row and README misstate R4. The C-level order property is proved only per poll.**

Evidence:
- The branch README contradicts the register.
  - `README.md:58` says "initialized conservation remains open".
  - The register row and `accepted_runner_all_ingress_fates` say
    conservation is proved.
- The R4 row says "Chronological GRO order is refuted".
  - It does not say what order is proved.
  - WireGuard's own promise is FIFO through `prev_queue` to
    `napi_gro_receive`, and GRO reorders only across flows.
  - That promise holds only per poll (`:536`).
  - Charter §3 expects the reshaped property to be proved ("prove the property
    the code has"), or else left unproved and recorded as such.

What settles it:
- Fix the README line.
- Add one sentence to the R4 row: run-wide pre-GRO order is not claimed; the
  per-poll subsequence theorem is the order result.
- A run-wide pre-GRO FIFO theorem is optional follow-on work for the proof
  tree.

**2. Two suspected mirror defects in GRO appear only as "unconfirmed source concerns" (`docs/2026-10-13-proof-campaign.md:921`). The C supports both.**

The first concern is zero-payload flushing.
- `tcp_offload.c:318,379`: a lone segment has `mss = 1`, so `flush = len < mss`
  is true for a zero-payload segment. That segment is taken at once.
- `Leanux/WG/RxData.lean:392–402`: `groTakenAtOnce` ignores length, so the
  mirror holds a pure ACK.

The second concern is same-flow ordering.
- `tcp_offload.c:385–386` and `gro.c:546–556`: Linux completes a held
  same-flow segment (`pp`) before a flushing segment goes to normal.
- `RxData.lean:404–412`: `napiGroReceive` sends the flushing segment to
  normal without checking the held chain. The same flow then reorders in the
  mirror where Linux keeps it in order.

Effect on the campaign and on the corpus:
- The R4 witness avoids both triggers (one-byte payload, distinct flows), so
  the refutation stands under the C reading as well.
- `docs/2026-10-06-w5-w6-receive.md:969` notes that on the single-CPU oracle
  a poll normally sees one packet. The corpus may therefore never exercise
  either path.
- This is clause 1 of Rule Zero, to be settled by the differential check, not
  by the proof tree.

What settles it: list both items in the register (or decisions) as open
mirror-lane questions, then run the differential check or record an explicit
exclusion. No proof change is needed.

**3. The universal quantifiers in R2, R3 and R4 range over observer events. Coverage of the observers rests on review, not on a kernel-checked theorem.**

What the proofs establish, and what they do not:
- The erasure theorems (`ErasesOuter`, `Logged/PrefixOuter.lean:16`) show
  that each observer does not change behaviour.
- They do not show that the observer emits an event at every access, Stack
  entry or handoff.
- The R3 outgoing report says this outright: "complete handoff coverage
  follows … independently reviewed wiring of all three executable wgXmit call
  sites. No separate converse reachability theorem". The R3 row says it in one
  clause.
- The R2 and R4 rows rest on the same kind of instrumentation and say nothing.

What settles it:
- Add one sentence per row, or once under Results, naming observer coverage
  as reviewed rather than proved.
- Optionally add a cheap source-factor theorem enumerating the call sites
  later.

**4. Seven R3 headline terminals have no docstring, contrary to charter §5.1.**

The undocumented terminals:
- `CryptokeyRouting/Statements.lean:4607–4643`: `initialized_transmit_checks`,
  its parsed form, `_rx_projection`, `_executable`, `_receipt`,
  `initialized_transmit_authorization` and
  `parsed_initialized_transmit_authorization`. The last is R3's outgoing
  headline.
- Also `ReplayWindow/Statements.lean:138,144`.

What settles it: docstrings only.

**5. The gate's token scan has demonstrable blind spots.**

The gate conforms to the AGENTS.md paragraph: it checks the build, the axioms
of every `Statements` declaration, the forbidden tokens, outside imports, root
coverage and non-default membership. But I ran `scripts/proof-gate`'s own
`strip_comments`/`FORBIDDEN` on test lines, and three cases slip through:
- `invariant "--x" >>= fun _ => sorry` scans as `invariant "`, finding
  nothing. The stripper is not string-aware. Real lines exist where this
  happens:
  - `Queues/HolderRetirement.lean:48`;
  - `Lifetimes/PeerRemoval.lean:70`;
  - `Peers/CreationAccess.lean:148–149`;
  - `Lifetimes/PeerAllocationFrames.lean:211`.
- `by decide +native` (the current spelling of `native_decide`) finds nothing.
- `sorryAx _ false` finds nothing.

The axiom check covers anything a `Statements` theorem depends on. It does
not cover the findings and counterexample modules the root imports, and those
carry the refutation theorems. My audit shows all of these clean today.

What settles it:
- Make the stripper skip string literals.
- Add `+native`, `ofReduceBool`, `sorryAx`, `trustCompiler` and
  `skipKernelTC` to the token list.
- Print axioms for every declaration of every module the root imports
  directly.

All three are cheap. The AGENTS.md paragraph should change with them, so this
needs the user's word.

### Notes

**6. Most runner-level counterexamples sit outside the kernel and outside the gate.**

The runner-level witnesses for R2, R4 (GRO, W7), R5 and R6 run through
`lean --run`, which trusts the interpreter and compiler. They use generated
records, not captures. The nine `Replay*.lean` modules are outside the root's
import closure: 907 of the 916 proof files are imported, and the nine left
out are exactly these executables. So the gate never compiles them, and they
could rot silently. The reports say this for W7 ("compiled execution
evidence").

What is kernel-checked: the R1 witness, R4's GRO equation and W7 geometry,
and the cleanup-totality fixtures (`decide +kernel` on constructed worlds,
which they say).

All eleven pass today. A speedbump script that runs the eleven recipes at
claim points (under a minute) would keep them reproducible.

**7. R5's classification needs a domain caveat.**

The three refutations are correct as statement artefacts on the C path:
`send.c:356–373` checks at staging, `noise.c:112–177` holds refcounted
material, and the AEAD comes before the wire-nonce check. I concur with the
2026-10-13 review.

The coherent post-clear witness is different. It stages at 311 s and
encrypts after the zero timer at 672 s, so it needs a staging-to-crypt
latency of at least about 360 s. The environment admits that latency with no
virtual-time bound. That is a looseness in the accepted-record domain, an
open clause-1 question, not a property of the C.

The branch records it as a "qualification of the accepted-record domain"
inside the mirror lane's review doc
(`docs/2026-10-13-review-items-7-8.md:356`). The campaign report's line
"These are charter-statement artefacts" (`:1005`) should carry that caveat,
and the mirror lane should decide whether to bound it or accept it.

**8. R6's refutation is stronger than the register says.**

`corpus/wireguard/d3_retransmit_gives_up.json` (20 `wg_advance`s, in the
differentially checked `wireguard` suite) already shows the give-up
behaviour on Linux. The register could cite it rather than only "not a Linux
capture".

**9. Retrofit: the deletions are type-justified, but the current report no longer discloses all of them.**

R2's six terminals: `filesystem_family_*` and `filesystem_local_family_*`
(`wg_frame`, `exact_lift`, `allocation_preserves`).
- They were deleted at `9aac8d5f`.
- They are implied by `FS.M := StateT FSWorld TaskM`
  (`Kernel/Defs.lean:1848`), which cannot touch WG state. That matches the
  design's deletion rule.
- The current retrofit report and register give 202 as "119 retyped + 83
  retained" without saying the old total was 208. The earlier report text
  (`9aac8d5f:docs/2026-10-16-proof-state-split.md:55,522`) did say so.

R4's `original_rx_cleanup_credit_discharge`:
- It was withdrawn because its third conjunct is false over arbitrary states.
- It is replaced by three claims and a kernel-reduced counterexample
  (`DeliveryOrder/Statements.lean:1818`).
- It is disclosed. No initialized failure is claimed.

The retyped statements I compared keep their claims.

**10. The gate's runtime is understated.**

AGENTS.md's "about three minutes" was 16m25s here, on a contended host
running a second copy. The gate's own `lake env lean` axiom step is not
wrapped by `capped`.

**11. Register rows.**

All seven rows name `b3f56807` and "current", which is accurate at main
`b3f5680`. The rows do not name the branch; the header does. This is moot
once the tree is on main.

The register calls all 860 terminals "headline declarations", which hides
the roughly fifteen theorems that carry the claims. Naming the headline
theorems in each row would help readers.

**12. The placeholder scheduler can leave work pending.**

`Queues/PlaceholderFindings.lean` shows the placeholder-mode `afterBatch`
returning with a queued RX packet and pending NAPI from an arbitrary funded
world. It is not claimed to be initialized-reachable. It is a small
environment-model observation for the mirror lane.

**13. Process.**

Two process violations disclosed in the R4 report:
- a writer resumed without a snapshot;
- an edit was made before preservation.

Both were followed by snapshots under `refs/snapshots/…`. The merge also
restores AGENTS.md's proof-gate paragraph, which is a standing rule.

## 3. Verdict

**Land with the named changes**: findings 1, 3 and 4 (register, README and
docstring text), finding 2 (record the two GRO items as open mirror-lane
questions), and finding 5 (harden the token scan and extend the axiom
print). With that, the user can sign off on finding 5's change to the AGENTS
gate paragraph, or defer finding 5 if they prefer to keep the paragraph
as is.

The reason the landing is sound:
- The gate passes and the fresh kernel replay passes.
- No proved statement relies on a non-standard axiom, `sorry` or
  `native_decide`.
- The mirror is byte-identical to main.
- Every refutation reproduces and is correctly classified at the C level.
- Every weakening from the charter is stated somewhere in the register or
  reports.

The changes make the register say exactly what is proved and route the
mirror suspicions the campaign surfaced to where Rule Zero settles them.

## 4. What the six results establish about the mirror

For every typed trace the executable runner accepts, from the fixture:
- (R1) the replay window never accepts a wire counter twice in one key
  lifetime, and it accepts nothing more than one window behind any earlier
  acceptance, with equality allowed as in the C;
- (R2) no peer, keypair or packet access resolves an identity released
  earlier;
- (R3) the allowed-IP trie answers what the configuration history justifies;
  every packet the mirror hands to the stack has an inner source owned by the
  peer that sent it; every packet it sends goes to the longest-prefix owner of
  its destination;
- (R4) every packet admitted to the receive pipeline is either still queued
  or was removed by a real poll with its release, and none reaches the stack
  twice.

Two things are only shown locally:
- (R6) under load, an initiation failing MAC2 gets a cookie reply and
  nothing else;
- (R5) the key-age and message-limit checks sit exactly where the C puts
  them: before AEAD on receive, at staging on transmit.

Four literal claims from the charter are false of the mirror and of the C as
written, each with a replayable counterexample: the exclusive floor,
chronological post-GRO order, unconditional key-lifetime enforcement, and the
retry count. The W7 full-ring episode is characterised exactly.

Four things are not established:
- eventual delivery or fairness;
- run-wide WireGuard FIFO before GRO;
- universal R5/R6 replacement bounds;
- anything about the C beyond the mirror.

Also, the "every" in R2–R4 rests on reviewed observer coverage, not on a
proof.
