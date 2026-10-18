# Paired index-table subsystem: execution report

Status: in progress on `task/binary-pair-runner`, implementing the
[increment charter](2026-10-18-charter-paired-index-subsystem.md).
The complete sequential removal theorem builds under its named premises.
Its linked and unhashed concrete entry witnesses now check and execute to
return. Complete replacement and the lookup bridge now build and pass their paired
runtime checks. The general shared-reconstruction sequence theorem now checks and its mixed
runtime witnesses pass. Actual mutator captures and the final export/report
remain open.

## Start and time limits

[USER 2026-10-18] Resume implementation of the charter within its agreed
scope and record the start so the stopping checkpoint is explicit.

Execution began **2026-10-18 05:54:16 UTC**, from clean charter commit
`95a554c0` (implementation baseline `b630836f`).

- First-day reassessment: **2026-10-19 05:54:16 UTC** (24 elapsed hours).
- Outer planning checkpoint: **2026-10-20 05:54:16 UTC** (48 elapsed hours).
  If incomplete then, report the unfinished obligations and reassess; do not
  silently extend the run or label a smaller result complete.
- Supporting runtime investigation: initially **two hours of focused work**,
  counted separately from proof work, builds and the earlier pause.

Elapsed time includes overlapping activities and is not a person-hour or CPU
estimate. Internal stage completions are progress checkpoints, not stop points.
Substantive correctness or scope blockers are reported when discovered.

## Baseline

Mirror pin `cb2348e` still lags main
`77c9b55594787bd5b371575e2eca1a8d77b3c991`. Kraken is clean at
`7ebba06a30eaf08c10b26b28ca14bfee1c791576`; the binary package uses Lean
v4.35.0. The approved s4 oracle remains read-only. No merge or push.

Existing results and their limits are recorded in the charter and
[previous increment report](2026-10-18-plan-paired-call-increment.md).
The previous increment's external export gate remains pending; it must not
be attributed to the acceptance of the earlier boundary modules.

## Work record

| UTC checkpoint | Activity and result |
| --- | --- |
| 2026-10-18 05:54:16 | Start; inspected the clean tree, charter, pins and executable bucket decoder. First task: reconstruct the bucket after unlinking, then close the full removal call. |
| 2026-10-18 06:25:21 | Reconstruction stage: the concrete predecessor/successor/clear memory effect preserves the executable index reconstruction and ownership flags. Focus and finite list shape are derived from successful decoding. Full machine-call composition is still open. |
| 2026-10-18 06:57 | All 25 removal instructions composed through entry, both linkage paths, services and return; `remove_checked` builds. |
| 2026-10-18 07:01 | Explicit-environment removal wrapper builds. Concrete linked/unhashed witness execution exposed saturation accounting in the runner; fixed using the existing executable coverage write plan. |
| 2026-10-18 07:14 | Replacement runner passes the recorded-prefix three-way check and 24 calls across two seeds; whole-call proof still open. |
| 2026-10-18 07:48 | Formal linked/unhashed removal Pre witnesses and their execution theorem check; exact witness execution passes again. Replacement bucket reconstruction checks. |

Runtime-investigation time used: zero at this checkpoint.

## Completion tracking

| Charter criterion | State |
| --- | --- |
| A: complete removal adequacy and executed witnesses | Complete locally: whole-call `remove_checked`, explicit-environment `remove_simulation`, positive linked/unhashed Pre witnesses and `Witness.executes` check. The witness states execute to return. External acceptance and actual mutator captures remain in E. |
| B: complete replacement adequacy and measured reuse | Complete locally: all 41 instructions, failure and all positions; explicit environment wrapper, linked/unhashed Pre witnesses, exact witness execution and fresh kernel replay pass. Reuse and marginal cost below. |
| C: lookup under the common executable relation | Complete theorem and explicit environment wrapper build. Both recorded-prefix suites pass through the new assertion, including dead-then-NULL and collisions. Fresh replay of the environment/headline closure passes. |
| D: finite call-sequence theorem and retained-heap execution | Complete locally: `Sequence.sequence_checked`, actual histories and explicit environment/access premises. Eight ten-call mixed sequences pass; fresh kernel replay passes. |
| E: actual mutator captures, trust checks and cost report | Open |

Final theorem statements, named hypotheses, measurements, findings and
reproduction commands will replace these open entries as the work proceeds.

## Reconstruction stage

`UnlinkFocus.reconstruct` and `UnlinkFocus.ownership` prove the effect of
the concrete byte stores in `unlinkMemory`: overwrite the predecessor,
repair a non-NULL successor, and clear the removed owner's predecessor word.
They cover all list positions, including sole entries, and frame every
other bucket, owner peer word and count. `reconstruct_focus` extracts the
physical focus from a source member and successful reconstruction; it does
not ask the caller to supply the intended list shape.

The runtime `reconstruct` definition and source `target` are unchanged.
`reconstruct_normal` proves a list-traversal normal form of the existing
imperative decoder. The finite chain and neighbour lemmas invert that
decoder and return to it after the splice. `bucket_erase` is used by the
concrete bucket proof; local after-state word equations are discharged by
`unlink_word` and the checked storage separation, not assumed as a future
successful decode.

[AGENT 2026-10-18] Add `storageCheck` to removal's physical readiness. It
checks separation of the table, each embedded entry and each peer-count
field, including separation within a containing peer allocation. These
immutable address checks support the actual store frame. They impose no
condition on membership, peer words or count values. This refinement was
identified during proof work, then exercised by the paired runner; it was
not a counterexample discovered first by workload execution. It is outside
the source observation and does not change the dead-peer domain.

Validation at this stage:

- Targeted Lean builds pass with standard axioms and no new warnings.
  Inherited warnings remain visible.
- All 54 paired removal calls pass, totalling 4,550 executed instructions
  under two undefined-value seeds. The repeated-removal and collision-chain
  cases retain their heaps. Paired runtime was 1.663 seconds on this shared
  host; this is not an optimization claim.
- The selected recorded-prefix calls still pass the independent three-way
  coverage/decision comparison. They are source-materialized entries,
  not captured mutator memory and not execution of intervening callers.
- The stale-owner rejection remains exercised. A targeted count/entry
  overlap is rejected by the new storage check before reconstruction.
- Fresh local kernel replay passed for `PairUnlinkReconstruct` and
  `PairUnlinkOwnership`. External acceptance is not
  claimed for this increment.

The first reconstruction stage took about 31 elapsed minutes from the
recorded start, including overlapping builds and validation. No additional
instruction coverage or complete new function is claimed: connecting this
memory effect to the whole compiled removal remains the next task. Routine
Lean elaboration failures were fixed before the passing builds. An initial
fresh-replay command incorrectly supplied two modules; it failed explicitly
and was corrected to one module per invocation.

`PairIndexFrame` additionally derives preservation of reconstruction and
ownership from byte equality on the finite index-storage cover. It is the
frame needed to compose the unlink effect with stack, coverage and preempt
updates; it adds no source-observation clause.

Reproduce from the worktree root (with `capped` on shared boxes):

```sh
(cd binary && capped lake build binary-pair-remove PairUnlinkOwnership)
capped python3 binary/remove_probe.py --check .artifacts/check/binary-remove-20261018
(cd binary && capped lake env leanchecker --fresh PairUnlinkOwnership)
```

The recording is ephemeral; its regeneration command is in the previous
increment's removal calibration. No runtime-optimization budget has been used.


## Complete removal execution stage

`PairRemoveAdequacy.remove_checked` starts from `Remove.Pre`, the successful
execution of the same `callBoundary` used by the runner. Its decoder premise
pins all 25 removal instructions. It proves finite Kraken execution through
the prologue, the old predecessor test, both successor cases, the complete
unlink segment and the tail call to BH enable. The source side is the actual
accepted `WG.indexRemove` execution. The unlinked entry path leaves the
projection unchanged; the linked path establishes the exact filtered source
table through the preceding reconstruction lemmas.

The postcondition exports ABI return, restored preempt state, the conditional
pending-softirq word, both phases of the coverage-buffer invariant, saved
stack words and return-slot mapping, executable reconstruction and ownership,
and equality outside the index storage plus stack/service footprint.
The heap footprint is conservative; the reconstructed data are exact.

`PairRemoveEnvironment.remove_simulation` lifts that result to an actual
instruction history with explicit serialized-environment and permission
hypotheses. `TrustBase.IndexRemoveDecoderAgreement` names the new image premise.
`TrustBase.ReturningCallPermissions` states access validity for actual finite
histories that complete this ABI call, including service interiors. It does
not assume such a run exists or that its source result or reconstruction is
correct. This conditional environment premise is not a proof of access
safety from a concrete permissions map. The existing `TracePcContract` and
`BhEnableContract` remain explicit; executing their bodies in tests does not
discharge their image proofs.

The reusable physical layer now includes bounded stack-save frames,
coverage callback effects, phase-indexed call readiness, external-write
separation and derivation of those facts from executable checks. Raw regions
and removal control-flow composition remain function-specific. An early
proof attempt spent the default heartbeat budget simplifying a complete
memory expression; replacing that search with two explicit rewrites closed
the same obligation. The timeout was a failed attempt, not validation.

The exact synthetic witness states have one allocated keypair with a NULL
peer word, either solely linked or already unhashed. They use the actual
four-word KCOV capacity, including saturation across repeated removal. Their
execution passes eight calls and 554 instructions across two undefined-value
seeds. A hardirq-state corruption is rejected by the entry check. Formal
proofs `Witness.check_linked` and `check_unhashed` establish Pre.
`Witness.executes` specializes the complete-call theorem to these states and
the actual accepted source run, retaining the named image/service hypotheses.

This witness execution found a runner defect: its removal coverage history
counted callbacks even when the real buffer had saturated. The runtime now
uses `TrustBase.KcovPlan` to decide whether a PC is stored, as the existing
allowed-IPs runner does. The actual capacity, entry domain and proof statement
were retained. The 54-call regression and selected-prefix three-way comparison
still pass (4,550 instructions; 2.483 seconds on this run).

Fresh local kernel replay passed for `PairIndexFrame`, `PairRemovePre`,
`PairRemoveFinish`, `PairRemoveAdequacy` and `PairRemoveEnvironment`. The
last two precede the runtime-only saturation-accounting change and will be
replayed with the final closure. Headline axiom output lists only `propext`,
`Quot.sound` and `Classical.choice`. External acceptance remains pending.

About 31 elapsed minutes established the reconstruction effect and a further
32 established the whole-call execution theorem. These are overlapping
agent/build intervals, not person-hours, fresh-function campaign throughput,
or a final removal cost: witness checking and capture work remain. Actual
captured mutator entry/return replay is still open. This sequential result
also does not prove allocation, freeing, RCU, compiled callers, arbitrary
kernel contexts, or the remaining sequence theorem. No mirror or oracle
change was made.


## Witness normalization and replacement progress

The final witness module builds in 1.8 seconds and its axiom reports contain
only the standard three axioms. Development was much more expensive: attempts
to reduce the entire concrete decoder expanded the 8,192-bucket table, and a
later reflexive proof of the concrete register comparison caused kernel
normalization to grow without completing. One build exited 137; several owned
Lean processes were deliberately terminated after their memory growth exposed
the same problem. All are failures, not successful checks. Bounded diagnostic
attempts also failed with kernel timeouts. The cap was not raised.

The fixes preserve the executable assertion and positive states: prove generic
normal forms and guard introduction lemmas, prove empty buckets uniformly,
and use a small kernel-reduced decision proof for the concrete register guard.
No native evaluation axiom is used. This is an additional proof-development
cost discovered after the function theorem, not a performance improvement to
captured workload replay. The interval from whole-call composition to the
accepted witness overlapped replacement work, so it is not an additive
fresh-function timing.

Replacement now has its own ELF-derived coverage profile and paired runner.
The `c_remove_after_handshake` recording passes (one trace, six operations,
29 operand pairs, 23 comparison rows). The paired cases pass 24 complete
calls and 2,174 instructions in 1.173 seconds, across two undefined-value
seeds, covering successful replacement in every position, absent old entries,
repeated replacement and an independently NULL new-owner peer word. A wrong
new kind is rejected even though the lookup-only projection accepts that
unlinked entry. The three-way preparation initially failed on a wrong label,
then on selection of the task stream; the replacement belongs to operation 2's
remote worker stream. Both were fixed explicitly, with other-stream coverage
rejected. These failed attempts did not count as passing comparisons.

The recorded case reconstructs a pre-replacement index projection from a
completed source prefix. It is not an actual captured entry memory or a
captured whole World, and it does not execute the compiled caller. Actual
entry/return capture remains criterion E.

[AGENT 2026-10-18] Successful replacement requires an allocated, unlinked
keypair entry with the initialized keypair kind and mapped index/next words.
Failure does not require that freshness condition. This follows the actual
caller shape: `noise.c` creates and initializes the new keypair (lines 98–112)
and supplies its embedded entry at the session-install call (lines 850–852);
`peerlookup.c` performs replacement at lines 166–190. The two owner peer words
remain independent. This is explicit caller readiness, not a restriction on
NULL or dead-peer lookup states.

`PairBucketReplace` reuses the finite chain and decoder. `PairWordPlan`
generalizes exact word-store effects to chronological store lists, preserving
repeated destinations. `PairReplaceReconstruct` proves all bucket/order
changes and frames the independent owner words and peer counts. Storage,
slot separation, pointer bounds, neighbor identities and decoder-normal-form
lemmas are reused from removal. Replacement's concrete store order and local
neighbor equations remain bespoke. `PairReplaceOwnership` now proves the matching hashed-flag transfer, including
successor rewiring and independent unlinked owners. The following stage closes
the complete call.

## Complete replacement (08:18–08:24 UTC)

`PairReplaceAdequacy.replace_checked` composes all 41 anchored instructions
and the named services through return, for failure and success at every list
position. Its postcondition exports the matching low-byte Boolean result,
restored ABI, both coverage phases, preempt and pending state, reconstruction,
owner flags and a physical frame. `PairReplaceEnvironment.replace_simulation`
adds the explicit serialized-environment and access hypotheses. The new named
trust premise is `IndexReplaceDecoderAgreement`; the existing PC-coverage and
BH-enable contracts remain unproved hypotheses. No ordinary helper is assumed.

`PairReplaceWitness.check_linked`, `check_unhashed` and `executes` prove the
positive entry states and specialize the full execution theorem. The module
builds in 2.5 seconds with only the standard three axioms. Its exact concrete
states execute eight calls and 614 instructions across two undefined-value
seeds, including repeated replacement and saturation of the actual four-word
coverage allocation. A corrupted hardirq state is rejected. The new owner has
an independent NULL peer word. A nonzero high part of the saved result register
checks that the Boolean contract uses the ABI low byte rather than assuming
the entire return register is zero or one.

The complete theorem first built at approximately 08:18 UTC, about 64 elapsed
minutes after the 07:14 runtime checkpoint. That interval overlaps the removal
witness work and cannot be added to it as independent effort. Replacement
reuses storage separation, finite chains, executable decoder normal forms,
stack saving, callback readiness and the source/physical frame mechanisms.
`PairCallSlot` isolates the repeated instrumentation-call-slot update. Concrete
instruction effects, their register wiring and segment composition remain
bespoke. A failed broad simplification of the store segment was replaced by
explicit load/store and integer-width rewrites; no semantics or assertion was
weakened to close it. Whole-subsystem composition, lookup integration and actual
mutator captures remain open. Runtime-optimization time used remains zero.
Fresh local kernel replay of `PairReplaceWitness` and
`PairReplaceEnvironment`, including their imported closures, passed at
08:26 UTC. External acceptance is pending. The pinned mirror and Kraken
commits and the reported lag against main remain unchanged; Kraken is clean.

Reproduce the replacement witnesses:

```sh
(cd binary && capped lake build PairReplaceWitness PairReplaceEnvironment binary-pair-replace-witness)
capped binary/.lake/build/bin/binary-pair-replace-witness .tmp/binary-replace/input.json
(cd binary && capped lake env leanchecker --fresh PairReplaceWitness)
(cd binary && capped lake env leanchecker --fresh PairReplaceEnvironment)
```

Reproduce the added tests from the worktree root:

```sh
(cd binary && capped lake build PairRemoveWitness PairReplaceReconstruct binary-pair-remove-witness binary-pair-replace)
capped binary/.lake/build/bin/binary-pair-remove-witness .tmp/binary-remove/input.json
LEANUX_KERNEL_DIR="$PWD/.artifacts/kernel-net-choice-s4" LEANUX_QEMU_SLOTS=16 \
  capped scripts/in-bundle python3 -B -m evaluator.check --suite wireguard \
    --binary-coverage --binary-profile index-replace --trace c_remove_after_handshake \
    --out .artifacts/check/binary-replace-20261018
capped python3 -B binary/replace_probe.py --check .artifacts/check/binary-replace-20261018
capped python3 -B binary/generate_index_mutators.py --check
capped scripts/in-bundle python3 -B -m unittest harness.test_linux
```

Set `LEANUX_KERNEL_DIR` to the approved shared build if it is not available at
the displayed worktree path. The generated-image comparison passes. Harness
unit checks pass 13 tests with one existing skip. Inherited warnings, including
unused simplification arguments in `PairRemoveRegion`, remain visible; new
modules add no suppression. Fresh local kernel replay passes for `PairRemoveWitness`,
`PairRemoveEnvironment` and `PairReplaceReconstruct`, covering their imported
closures. This is not external gate acceptance.

## Lookup through the common reconstruction (C)

The lookup bridge was developed approximately 08:27–08:53 UTC, overlapping
builds. `PairLookupAdequacy.lookup_checked` derives every original physical
entry premise from the executable `IndexLookup.callBoundary`; the old
focused relation is not an independent hypothesis. It uses the existing
complete sequential lookup execution, then proves that its actual writes
and accepted source updates reestablish the full executable reconstruction
and every owner linkage flag. `PairLookupEnvironment.lookup_simulation`
exposes serialized-environment and actual-history permission hypotheses.
The five callback contracts and anchored decoder premise remain named in
`TrustBase.lean`; no new callback or reconstruction assumption was added.

[AGENT 2026-10-18] For the retained-heap subsystem, a live lookup's peer output
word belongs to the caller and is separate from the index heap, stack and
service metadata. Linux's relevant callers use a local peer variable
(`receive.c:509–519`, `noise.c:747–750`). The executable check enforces this
allocation discipline only when the accepted path writes the output. This
is an explicit subsystem caller condition; the original M1 statement and
its alias-permitting domain remain unchanged. No dead-peer or NULL state
is excluded. Address interpretation compatibility is also checked: embedded
owner addresses must agree with the existing physical theorem's offsets.
These immutable checks are physical readiness, not extra source observations.

The proof splits source changes into bucket/identity preservation and the
selected owner/count updates. A generic keyed-list decoder lemma reconstructs
all owners and counts. Byte frames preserve the buckets, remaining scalar
fields and linkage flags. This avoids adding whole-World clauses or requiring
relation equality at intermediate pointer stores.

Composition work exposed an omitted export: M1 supplies coverage-buffer
readiness for the phases its selected path uses. A later call can use another
phase. `PairLookupReadiness.coverage_after` now carries both phases, using the
actual write frame for the unused phase and leaving capacity metadata intact.
The new postcondition also exports restored preempt state, pending-softirq
state, exact interface results and the physical frame. General preservation
of scratch mapping is being developed for D, rather than assumed of future
entries.

Validation:

- `PairLookupAdequacy` and `PairLookupEnvironment` build; printed axioms are
  only `propext`, `Classical.choice`, `Quot.sound`.
- The first test attempt mistakenly selected the other trace's recording;
  the trace-identity check failed noisily. After correcting the selection,
  `d1_second_response` passed the independent three-way check and 48 paired
  calls, 22,404 instructions, 94 loop headers, 15 controls, in 5.267 seconds.
- `d1_wrong_receiver_index_same_bucket` passed its independent three-way check
  and 48 paired calls, 21,774 instructions, 94 headers, in 5.274 seconds.
  All 17 controls pass, including new unmapped-output and output-alias checks.
- These are recorded-prefix materializations plus labelled synthetic cases,
  not captured kernel heaps. The suite runs both undefined-value seeds,
  repeated live/dead/NULL lookups and collision depths 1, 3 and 8.

Reproduce from the worktree root, selecting the matching saved recording:

```sh
LEANUX_QEMU_SLOTS=16 capped python3 -B binary/pair_run.py \
  --trace d1_second_response --check .artifacts/check/binary-tv-20261016-234706
LEANUX_QEMU_SLOTS=16 capped python3 -B binary/pair_run.py \
  --trace d1_wrong_receiver_index_same_bucket --check .artifacts/check/binary-tv-20261016-235330
```

Omit `--check` to regenerate a recording; set `LEANUX_KERNEL_DIR` to the
approved s4 build. No external gate acceptance is claimed for this increment.

Fresh `leanchecker --fresh PairLookupEnvironment` completed successfully at
approximately 08:57 UTC, covering the headline and its new reconstruction
closure. This is local replay, not the external export gate.

## Retained-heap finite composition (D)

Composition and its supporting lemmas were developed approximately
08:55–09:14 UTC. This overlaps builds and replay; it is not additive CPU or
person time. `PairSequenceAdequacy.sequence_checked` now proves arbitrary
finite admissible lists of the three actual mirror functions over one Names
interpretation and one retained heap. It returns the ordered interface
observations, per-call actual instruction histories with the explicit
serialized environment and access premise, endpoint reconstruction, reusable
physical readiness and a frame for the complete sequence. Its proof is list
induction over the accepted mirror program; no fixed call count or test fuel
is in the theorem.

`AdmissibleSequence` follows accepted **source** prefixes. Its only additional
caller conditions are representable lookup queries, named owner arguments,
and the new keypair being absent when its handshake replacement succeeds.
It contains no binary state, future Pre or successful binary run. The initial
executable check establishes all physical resources once; the proof derives
each next function's executable Pre. The single `install` caller transition
writes ABI registers and its return slot. It never reconstructs heap memory
from the source. Its heap/service frame is proved and it is also the runner's
actual caller setup.

Three useful composition mechanisms emerged:

- `MemoryInvariant.eventually_mapped` proves, directly from all scalar and
  AVX interpreter cases, that ordinary mapped memory survives successful
  Kraken execution. It then strengthens any existing whole execution,
  including the instruction executions promised by named service contracts.
  MMIO is rejected by this `All` semantics. This introduces no new assumption
  and avoids revisiting earlier physical regions for scratch mapping.
- `KindFrame` carries immutable type tags of **unlinked** allocated entries.
  The common observation does not read them while unlinked, but a later
  successful replacement does. The three postconditions now export their
  preservation using existing combined-store/frame lemmas. These are physical
  frame facts, not extra clauses of R.
- Completeness lemmas for the existing callback and frame checks turn the
  maintained physical predicates back into the same executable entry checks.
  No second independent relation or success premise is introduced.

[AGENT 2026-10-18] The fixed-universe sequence's initial resource check includes
next/index mappings and owner-kind tags for its allocated entries, maximum
scratch mapping, and the separate caller output word. It checks the four
stack sizes used by these anchors (4, 5, 6 and 13 words). The caller return
slot is also separate from service inputs because caller setup writes it.
These are upfront resources for arbitrary later calls, not restrictions on
live/dead membership or peer counts. `ReturningDomainPermissions` names the
existing per-call permission premise over explicitly caller-prepared entries;
its domain has no successful-run or reconstruction premise. Callback-image
proofs and real caller entry realism remain outside this experiment.

Validation and size at this internal checkpoint:

- `sequence_checked` builds with only `propext`, `Classical.choice`,
  `Quot.sound`. Fresh `leanchecker --fresh PairSequenceAdequacy` passes over
  the full headline closure, including the strengthened function posts.
- The three independent function comparisons pass before mixed execution.
  Eight ten-call sequences pass: two undefined-value seeds, live and dead
  source peers, actual fixture capacities 1024 and 4. There are 80 calls and
  21,268 executed instructions, taking 2.872 seconds for the paired sequences.
- Each sequence includes lookup, successful replacement, old-kind lookup,
  new-kind lookup, unsuccessful replacement with the new owner already
  linked, removal, repeated removal, miss, lookup of a surviving colliding
  entry, and removal of the now-unlinked handshake. Names and heap persist.
- Capacity 4 is a labelled synthetic saturation case, not a claim of
  unchanged-capture acceleration. Actual service instructions execute.
- New sequence/check/frame/invariant Lean modules total 1,101 lines, including
  the runtime suite and 233 lines for the ISA memory invariant. These counts
  exclude the small strengthening edits to existing headlines. The finite
  composition module itself is 86 lines; the resource derivation is most of
  the work. Builds had ordinary elaboration corrections, no killed process
  or timeout in this stage.

Reproduce after building `binary-pair-sequence`, `binary-pair-remove` and
`binary-pair-replace`:

```sh
LEANUX_QEMU_SLOTS=16 capped python3 -B binary/sequence_probe.py \
  --lookup-check .artifacts/check/binary-tv-20261016-234706 \
  --remove-check .artifacts/check/binary-remove-20261018 \
  --replace-check .artifacts/check/binary-replace-20261018
(cd binary && capped lake env leanchecker --fresh PairSequenceAdequacy)
```

Set `LEANUX_KERNEL_DIR` to the approved s4 build. The script runs each
function's existing independent comparison, checks that decoder inputs agree,
and then executes the combined image input. These remain synthetic sequences
built from a recorded-prefix projection, not uninterrupted captured operation
execution. At 09:14 UTC, main and Kraken pins/lag remain as recorded above;
Kraken is clean. No external gate acceptance is claimed.
