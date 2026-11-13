# Binary verification: execution-based assessment

Assessment and recommendations [AGENT 2026-11-13]. Development and tests
are on `task/binary-assessment-20261113`, with a separate disposable checkout
of the archive. No mirror, oracle, theorem, standing rule, main branch or
remote is changed. The small accompanying commands evaluate existing
predicates or expose a capture option; they do not repair their inputs.

## Scope and standard of evidence

| Tree | Assessed revision | Scope |
| --- | --- | --- |
| Current main | `9ca4b0655d8a` | October binary experiment; 944 Lean files under `binary/` |
| `archive/restart-2026-11` | `6248d601a289` | November C1 insertion and C2 receive-window results |
| `archive/whole-driver-pilot-2026-11-12` | `8b498e7ec207` | Whole-driver attempt, subsequent joint-premise repairs and trace checker; 1,727 binary Lean files |
| `archive/foundation-packet-2026-11-12` | `fb903d5c9d04` | Foundation proposal and its review |

The foundation packet and pilot are sibling descendants of `0eff097f`.
The pilot archive has the later trace checker that the foundation archive
lacks. Its results must not be attributed retrospectively to the initial
design or confused with a successful whole-driver result.

An existing audit at
`task/audit-restart:docs/2026-11-13-audit-since-restart.md` supplies useful
additional evidence. Below, **fresh** means executed in this assessment;
**reported** means evidence in that audit or another cited report, not
rerun here; **inspection** means reading the statements and their callers.
No independent reviewer was commissioned for this assessment.

Four questions need different answers:

1. Can the premises hold together at all? A toy witness can answer this.
2. Do they hold at the fixed image parameters on actual captured states?
3. Do those runs satisfy the conclusions, including frames and hand-overs?
4. Does this cover the intended workload and use the intended mirror?

A checked implication answers none of these automatically. Conversely,
a rejected capture does not refute a theorem whose explicit execution
model excludes that capture. It does refute an unqualified claim that the
result describes that execution. Tests of two undefined-value seeds are
finite tests; universal quantification comes from the proof.

## Verdict on the current work

**Keep the October foundation, but treat it as a collection of narrow,
sequential conditional results, not a verified WireGuard subsystem.**
There is substantial executed evidence and no basis for declaring all its
models vacuous. In particular, freshly captured lookup hit and miss states
pass the actual checked-entry theorem's predicate with the full, unchanged
32 MiB coverage allocation. Several larger applicability claims remain
unestablished.

| Current component | Assessment | Outstanding limit |
| --- | --- | --- |
| Index lookup and peer-get | Has proved entry witnesses and executable correspondence tests. Real lookup hit and miss states freshly pass the later checked-entry theorem's actual predicate. | Original headline retains service and permission hypotheses. NULL-owner and some mode/kind combinations lack a complete theorem witness; those gaps are not proofs of impossibility. |
| Index removal and replacement | Executable entry checks are the checks used by the proofs, and captured executions exercise them. | Captures cover selected invocations, under serialized execution. They are not a general kernel-caller or concurrent-context proof. |
| Five coverage/BH callbacks | Image-body contracts are proved; generated cases exercise their readiness domains. | Decoding and Kraken's ISA semantics remain trusted. These contracts do not model arbitrary interrupts or the entire BH-enable slow path. |
| Allowed-IPs lookup | The actual capture runner calls the theorem's entry checker and checks internal boundaries, reconstruction and return. | Dying-peer retry can be refused by the source experiment. This is not universal acceptance of every kernel lookup. |
| Index insertion | Conditional full-function and retained-heap theorems; real random-service instruction execution is tested. | `RandomReturnContract`, `RandomInputCoupling` and the chosen `inputAt` interpretation remain universal hypotheses. Concrete successful draws and a `Pre` witness do not establish their joint satisfaction for all relevant executions. |
| Retained-heap sequences | Resource preservation and later entry conditions are derived, rather than postulated independently at every call. | Caller ABI installation is constructed, with a fixed allocation interpretation and source admissibility. These are not captured complete Linux call sequences. |
| Allowed-IPs mutation components | Tested placement, reassignment, initialization/publication and return segments are useful. | No complete insertion theorem exists on current main; allocator transitions are supplied. Individual component success cannot be added up into full-function adequacy. |
| Lookup transport of replay/lifetime fields | A conditional frame theorem. | Initial representation and separation are additional hypotheses. No fresh captured admission of their whole conjunction was established here, and it is not a whole-receive result. |

The source for these distinctions is principally `LookupAdequacy`,
`LookupSnapshotTransport`, `PairCallbackAdequacy`, `PairLookupPre`,
`PairSequenceCheck`, `PairInsertWitnessExecution`, `PairInsertCapture`,
`PairAllowedipsLookupAdequacy` and `PairAllowedipsInsertCapture`.
The existing binary README generally states these limits correctly.

### A gap between the lookup test and its theorem

`PairCapture.run` calls `Pair.lookupFrom`. That runner checks reconstructed
memory, ABI, loop correspondence and the resulting execution, but it does
not call `IndexLookup.callBoundary`. The later theorem's `Pre` is exactly
successful execution of that latter check. `PairLookupPre.pre_lookup`
derives the original `Pre_lookup` from it.

The ordinary lookup capture also captures only a prefix of the coverage
buffer. The physical entry predicate can require the whole allocation to
be mapped. A missing byte in a partial snapshot is missing evidence, not
evidence that Linux left it unmapped. Reducing the captured capacity word
would test a different state.

The assessment used a temporary wrapper to enable the existing capture
helper's full-allocation option. It captured both hit and miss with the
original capacity of 4,194,304 words (32 MiB). The current
`binary/capture_lookup.py` defaults to full allocation, so the redundant
wrapper is excluded from the landing package.
`binary/assessment/LookupEntry.lean` then invokes the existing
`callBoundary`, checks source acceptance, and verifies that a wrong entry
PC is rejected. It does not redefine the predicate or manufacture memory.

**Fresh:** the unchanged predicate accepts both the captured hit (source
answer `handshake 0`) and miss (`none`), and rejects the wrong-PC control
on both. This is evidence against entry-premise vacuity for those
invocations; it does not discharge
the original headline's universal permission or service hypotheses.
Separately, the documented partial-buffer capture/replay recipe passes
fresh hit and miss executions at both undefined-value seeds (506 and 191
instructions). The full-buffer instruction replay did not complete; the
entry checks and partial-buffer replays are distinct tests on separate
captures, not one successful end-to-end check of every premise and result.

### What a passing capture does and does not establish

The October captures deliberately defer interrupts and timers within the
call. Their return comparisons cover captured bytes, registers and
instruction histories. They do not establish a frame over unobserved
native RAM or acceptance under ordinary interrupt scheduling.

Some mutator replays reconstruct the initial source state from captured
memory, with identities supplied by the recorded prefix. That is useful
evidence that a represented binary state is admitted. It is a different
claim from independently replaying the entire real execution's mirror
state through the actual caller and every intervening kernel action.

The mutation capture supplies a native allocator transition and checks a
restricted frame on captured bytes. It does not execute the allocator
under Kraken or discharge a universal allocator contract. Current docs
explicitly acknowledge this; keep that distinction when reusing the code.

In contrast, the fresh index-insertion replay does execute the two random
service calls from captured private memory: 1,338 interpreted instructions,
including the collision/retry path, at both undefined-value seeds. It
checks 33,626,368 captured return bytes, consumes the two recorded draws,
checks their values against the independent recording, and rejects a
changed interrupt-flag endpoint. This is a useful concrete service witness;
it still does not discharge the headline's universally quantified random
coupling and return-contract hypotheses.

## What failed in the archive

### C2: useful arithmetic result, an exit clause that fails on real runs

**Fresh:** the s5 `C2Headline` and clean-image `RtC2Headline` build; the
clean-image statement tests execute 486 constructed cases without a
failure. The adversarial suite builds 1,215 states at 135 layouts, admits
and runs 1,062, and checks 306 second visits with no replay accepted.

A fresh, unforced clean-image two-device capture contains **65 visits**.
All 65 match the mirror's acceptance and window update and the interpreted
general registers. **Three violate `Rt.C2.Kept.count`.** For example,
entry count `0x80000100` should become `0x80000300` under that predicate;
the captured exit is `0x300`. The need-resched bit was cleared during the
visit. No guest counter or register was forced in this run.

The archived `RtC2Captured.lean` explicitly accepts this alternative and
prints a deviation, then reports zero failures and exits zero. That is
evidence for a weaker arithmetic/result claim, **not a passing test of
the stated `Kept`**. The assessment's `check_rt_c2.py` checks the exact
equation and exits 1 on these three records. This checks one conjunct;
the capture does not contain enough memory to check the full native frame.

The theorem's instruction semantics excludes interrupts, so this is not
a contradiction in Lean. It is an applicability failure against ordinary
executions. The previous audit independently reports the same issue on
s5: 11 of 144 naturally scheduled visits violate `Kept`, whereas their
arithmetic result matches. Its additional whole-frame measurements were
not rerun here.

**Revival:** C2 is the best small proof candidate. First settle the exact
execution scope and frame. A weaker preserved-count/result theorem may be
a corollary of the existing proof; that does not supply the frame needed
for later composition. Keep a separate natural-scheduling capture and
report deviations as failed conjuncts. Keypair address reuse must start a
new lifetime; `WindowRetained` cannot silently bridge reallocation.

### C1: a conditional hybrid, not the image's allocator theorem

**Inspection:** `Allocator.Idle` is an arbitrary proposition over memory,
live nodes and future records. `AllocatorContract` assumes eventual
instruction execution of allocations and frees plus a universal frame.
The proved witness supplies a stub allocator and artificial heap. It
establishes satisfiability for that hybrid, not for Linux's allocator.

**Reported and source-checked:** the prior audit's fresh s5 allocations
execute `rdtsc` and successful allocations execute `cmpxchg16b`; neither
instruction is supported by the relevant Kraken source. The native service
transitions installed by the capture checker are therefore not the
instruction executions assumed by the theorem. At those real service
states, either the service contract is false or `Idle` excludes them. The
headline consequently gives no result for those executions. This is a
substantive redesign issue, not a missing `simp` lemma.

Other limits are visible in the capture checker and report: most coverage
checks shorten the capacity word; allocator arena/depth are fitted from
the run's observed changes; peers cannot generally be created between
insertions; captured lookups use constructed callers. The previous audit
reports 20 admitted insertion calls out of 26, 22 relevant allocations
and one free, and 33 interpreted lookups on captured heaps. These counts
are **not fresh results of this assessment**.

**Fresh:** the archived documented `Statements/C1/run-tests.sh` fails
before testing, because its text grep flags a word in a comment in
`StatementC1Vacuity.lean`. This is a separate test-runner bug, not the
reason the allocator model is inapplicable.

**Revival:** retain algorithmic lemmas and capture machinery as candidates.
Replace the allocator interface with a deliberately scoped, executable
transition contract or extend the semantics enough to execute the actual
service. Fix arenas, identities, ownership and bounds before the test;
test held-out calls, including failures and peers created between calls.
Do not reintroduce the existing headline as a real-image claim.

### Whole-driver pilot: late repairs helped, but the composed result still fails

The original incompatibilities are substantive. The archive preserves
proofs of conflicts involving static work lists, socket ownership,
worker registration and lock-list order (`PilotJointNewlinkGaps`,
`PilotJointSocket`, `PilotJointSockStop`, `PilotJointMetJoins`).
The foundation review also distinguishes global premise compatibility
from a starting state for each invocation at the joint invariant.

The later archive repairs many of these. **Fresh:**
`PilotJointPremises`, `PilotTraceMain` and `ParamCopyEq` rebuild from a
private dependency checkout, in 683 jobs without warnings. It would be
incorrect to report all the original contradictions as still present at
that tip.

But the composition is `Eventually (Returns ... ∨ Exited ...)`, and an
exit makes no claim about the rest of the plan. The canonical joint
witness's allocation stubs return NULL: it cannot demonstrate the useful
newlink/open/receive continuation. The arena alternative and conditional
`Owed` BLAKE2s contracts are additional models, not captured kernel services.
`Compatible` alone does not prove a joint invariant and each entry's
`Starts` are jointly inhabited and reachable along the same run.

**Fresh end-to-end pilot capture:** the clean-image workload finishes,
with 717 records, zero lost records, six entries and 139 snapshots.
The checker evaluates 1,312 named predicates at 5,316 points. It finds
**one failing predicate at both of its two call sites**:
`contract.setup_udp_tunnel_sock.wrote`. The callee writes `sk_user_data`
at socket offset `0x268`; the shared representation makes that byte the
driver's, while the contract omits it from the write set. There are no
listed exits or departures from the claim in this small run. Thus the
latest pilot admits a great deal of this small execution, but **the
joint contract still fails**. The checker exits zero by design, so its
result must be read from the verdict table, not the shell status.

The archive's broader trace report records another essential fact:
ordinary handshake/corpus/device-lifecycle runs soon leave the claim's
entry set or domains. Its six corpus guests cover 110 of 148 traces,
but leave at `wg_set_device`; a no-peer stop domain is not a verification
of peer teardown. Those broad runs were not repeated here. The successful
prefix denominator must remain visible; counting only in-domain points
would hide the practical coverage failure.

There are also mismatches beyond one write-set repair. The trace replay
chooses some ghost state and a zero depth, inserts moves where the sample
plan has none, and some views take values from the next capture. Those
choices can be legitimate witnesses to existential claims, but are not
independent tests of fixed predicted transitions. Five open-side contract
families omit access conditions for kernel objects; the source itself
notes that the resulting universal service assertion is not true of all
states its entry conditions admit.

### A second specification was substituted without the needed bridge

`ParamCopyEq` proves 74 equalities when the copied functions use
`Models.mirror`. **Fresh:** its compilation and `generate_copy.py --check`
pass. But `WDAdapter` runs the copy at `Models.ofAnswers`/`Models.fed`,
using answers obtained from callees. The equalities at `Models.mirror`
do not establish equality at that different instance. Tests can show
consistency with the supplied answers without testing whether the
original mirror would supply them.

**Revival:** the dependency inventory and generated copy may be useful.
The missing bridge is a proof and execution obligation. Until it exists,
describe the target as the parameterized copy with supplied services,
not as equivalence to the project's operational mirror.

## What to recover, and in what order

| Candidate | Recommendation | First acceptance experiment |
| --- | --- | --- |
| Saved clean image, decoding and layout generators | Recover separately. Both generator checks pass freshly: 45 clean modules (43 functions, 2,220 instructions), plus 11 retargeted modules. | Compare live bytes at every executed range, including init text, and record the exact image/semantics pin. ELF equality alone does not cover runtime patching. |
| Kraken instruction patches | Recover individually as trust-base changes. Existing CPU tests and independent review are valuable reported evidence; this assessment rebuilt their consumers but did not repeat the full ISA/host suite. | Rerun semantic, native and fault tests at the chosen pin; preserve disclosed unsupported forms and stop behavior. |
| Capture and predicate-checking mechanism | High-value recovery candidate. The pilot checker detects a real failure using the claim's definitions and proved checker correspondences. | Make absent clauses, missing capture coverage and mismatched dispatch visible as failures of validation; keep the captured-predicate inventory aligned with the statement. |
| C2 core | First proof candidate, with a corrected explicit scope. | Exact entry/exit checks on natural and serialized captures, plus replay, boundary and lifetime-change cases. |
| Clean-image trie/index functions | Recover after their own captured entry checks; clean-image bytes alone do not transfer an s5 witness. `RtAip` rebuilds freshly. | Test actual entry memory rather than reconstructing an entry from a mid-function stop; refusal counts must make claim validation red. |
| C1 insertion lemmas and October mutation pieces | Recover selectively after service-interface design. | Allocations, failure/rollback and subsequent lookup from one retained real heap, without fitted write sets. |
| Whole-driver contract schema, classes, plan and headline | Do not resume as the accepted foundation. | A small real joined execution with every entry, contract, invariant, hand-over and conclusion evaluated together at fixed parameters. |

The older contract evaluator has weaker behavior than the later pilot
checker: unregistered contract names can produce no verdict, non-evaluable
clauses do not make the process fail, and a write clause can pass on only
the bytes common to partial snapshots. `RtAip`'s captured test can also
exit zero with premise/source refusals. These are reasons to reuse the
mechanism carefully, not reasons to accept its old green totals.

## Proposed review and build process

This is a proposal, not a silent amendment of the standing rules.

1. **Choose one complete path and its exact observable claim.** For a
   first restart use C2, or a single insertion followed by lookup. Name
   ordinary versus deferred-interrupt execution, image, numeric parameters,
   state/identity representation, services and what a scope exit means.
2. **Make the statement executable before commissioning its proof.** Run
   its own predicates or a proved equivalent checker on fresh states.
   Report expected invocations, admitted invocations, refusals, failures,
   exits and unevaluated clauses separately. Check the full conjunction at
   the fixed parameters, not each conjunct with a different witness.
   A non-executable universal service/permission premise is an unresolved
   exception under the current rule, not something finite samples have
   discharged; list it explicitly and settle its treatment first.
3. **Test composition as execution.** Retain heap and identity mappings
   across calls. Evaluate the actual postcondition and next precondition
   on the same intervening states. Include success, failure, reuse,
   teardown and an ordinary scheduling sample. Do not stop at `Post → Pre`
   over an uninhabited invariant or an immediate failure exit.
4. **Review the statement, capture and checker together.** An independent
   reviewer should be able to select another workload, inspect all
   quantifiers and challenge any scope restriction. Have them inspect
   source acceptance, ghost reconstruction and service substitutions, not
   just the proof. Give setup and objectives, not a prescribed verdict.
5. **Freeze that small interface; then prove it.** A discovered mismatch
   returns to the executable model and differential evidence. Do not
   weaken a premise or enlarge a write set merely to close a proof. Every
   necessary specification change needs its affected captures rerun.
6. **Keep validation small and consequential.** Builds/axiom checks/kernel
   replay remain trust checks; runtime admission is the existing rule's
   pre-proof evidence. Add a few targeted negative controls (wrong
   byte/PC, dropped clause, wrong identity, unexpected exit). Do not build
   another large audit bureaucracy or make whole-driver coverage a
   per-edit gate.
7. **Integrate one reviewed unit at a time.** Present the exact statement,
   proof scope, fresh capture counts, refusals, remaining hypotheses and
   mirror lag together. Main still requires concrete user signoff.

The restart criterion should be behavioral: a useful composed real run
passes the unchanged chosen predicates. Agent-hours, proof lines and the
number of closed implications are secondary. Stop and report when the
pilot mostly exits, when the real image cannot meet a service premise,
or when checking requires repairing captures or choosing parameters from
the outcomes being checked.

## Validation and reproduction

Fresh results in this assessment:

| Check | Result |
| --- | --- |
| Private October dependency bootstrap | Exact nine-patch pin reconstructed locally |
| Current binary default build | PASS, 1,119 jobs, no warnings |
| Current binary executables | PASS, 655 jobs |
| Binary trust gate | PASS, 71 terminal statements, standard axioms only, printed surface unchanged |
| Fresh kernel replay of `LookupSnapshotTransport` | PASS |
| Fresh kernel replay of `PairCallbackSurface` | PASS |
| Fresh kernel replay of `AllowedipsInsertionSurface` | PASS |
| Binary Python tests | PASS, 15 |
| Mirror/harness unit tests | PASS, 149 tests, one existing skip; initial attempt failed because the fixed-width test executable was absent, then built and rerun once |
| Six October image/layout generators | PASS against saved s5 |
| Seven fresh differential recordings | PASS, 54 operations across the seven profile runs (five distinct workload names) |
| Callback suite | PASS, 3,032 coverage cases, 50 BH cases, 51,935 instructions; negative controls exercised |
| Constructed mutation suite | PASS, 66 insertion/lookup pairs, 24 isolated root pairs; 28 root, 20 exact, 10 child-publication and 10 child-resource checks |
| Sequence-wrap regression | PASS, eight cases |
| Standard captured lookup hit / miss replays | PASS, 506 / 191 instructions at both seeds and 870,372 return bytes each; partial coverage-buffer snapshots |
| Captured IPv4 / IPv6 trie replays | PASS, 1,592 / 1,510 instructions; both seeds, theorem entry check, 814,496 / 819,428 captured return bytes |
| Captured index removal / replacement | PASS, 100 / 115 instructions; both seeds, executable entry checks and 33,625,468 / 33,625,500 captured return bytes; four negative controls per function |
| Captured partial trie insertion | PASS, 254 instructions at both seeds and 822,856 return bytes; allocator transition supplied, no complete insertion theorem |
| Captured index insertion | PASS, 1,338 instructions, two executed random services, both seeds, 33,626,368 return bytes; changed interrupt-flag control rejected |
| Full-buffer index lookup instruction replay | FAIL to complete: SIGKILL under both 12 and 32 GiB caps; no semantic verdict |
| Direct lookup entry premises | PASS for hit and miss on original full 4,194,304-word buffers; source acceptance and wrong-PC controls checked |
| Archive joint premises/trace checker/parameterized equalities | PASS, 683 jobs |
| Archive s5/clean C2 and clean trie roots | PASS, 427 jobs |
| Clean-image generators / generated mirror copy | PASS, 45 + 11 modules / 14 files |
| Archived C1 documented test command | FAIL before execution: comment-sensitive guard |
| Archived pilot on a fresh real boot | FAIL: one predicate at two points out of 5,316; complete workload, no lost records |
| Archived clean C2 on fresh natural visits | Core result matches 65/65; exact `Kept.count` FAILS on 3/65 |

All heavy jobs used `capped`. The full-buffer lookup instruction replay
died with SIGKILL under a 12 GiB cap and again on its one infrastructure
retry under 32 GiB. Neither is counted as a pass; neither supplies a model
counterexample. The child was killed without a semantic diagnostic, so
the precise cause is unconfirmed. No third identical replay was attempted.
The archive bootstrap initially tried an unavailable network fetch; the
exact locked upstream object was obtained from an existing local project
checkout, and all sixteen patches were replayed into a private dependency.
No shared dependency or global configuration was changed.

Representative reproduction commands, from a task checkout with the saved
images and the documented dependencies:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
cap scripts/in-bundle /usr/bin/python3 -B binary/run.py --bootstrap-only
cap scripts/in-bundle lake -d binary build
cap scripts/in-bundle /usr/bin/python3 scripts/binary-proof-gate
cap scripts/in-bundle lake -d binary env leanchecker --fresh LookupSnapshotTransport
cap scripts/in-bundle lake -d binary env leanchecker --fresh PairCallbackSurface
cap scripts/in-bundle lake -d binary env leanchecker --fresh AllowedipsInsertionSurface
cap scripts/in-bundle lake build leanux-model leanux-fixed-width-tests
cap scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux harness.test_d1_keys
```

Use `binary/REPRODUCING.md` for the independent recordings and capture
recipes. The assessment used `d1_second_response`,
`d1_wrong_receiver_index_same_bucket`, `b1_trie_routing`,
`c_remove_after_handshake` and `s2_index_collision`, under their respective
index, allowedips, index-remove, index-replace, index-insert and
allowedips-insert profiles. Use fresh output directories. For the direct
lookup check, use the current `binary/capture_lookup.py` command without
`--partial-coverage`. Prepare the source prefix from
that boot without running the full instruction replay (the latter failed
to complete here):

```sh
cap scripts/in-bundle python3 -B -c '
import json, sys
from pathlib import Path
sys.path.insert(0, "binary")
from pair_capture import source_prefix
capture, original = map(Path, sys.argv[1:])
probe = source_prefix(json.loads(original.read_text()), capture / "boot.log")
(capture / "assessment-input.json").write_text(json.dumps(probe) + "\n")
' CAPTURE .tmp/binary-pair/d1_second_response/input.json
```

Then evaluate the unchanged entry predicate, using the probe's layouts:

```sh
CAPPED_MEM_MAX=32G cap scripts/in-bundle lake -d binary env lean --run \
  binary/assessment/LookupEntry.lean CAPTURE/assessment-input.json \
  CAPTURE/snapshot.json .tmp/binary-pair/d1_second_response/layouts.json
```

Substitute `d1_wrong_receiver_index_same_bucket` and its capture for the
miss. Capture creation checks the pinned image; the Lean entry checker
evaluates memory/premises, not the image's identity or the full return.

From a worktree at the pilot archive revision:

```sh
cap scripts/in-bundle lake -d binary build PilotTraceMain PilotJointPremises ParamCopyEq RtC2Headline RtAip C2Headline
LEANUX_BINARY_TARGET=net-clean-2 cap scripts/in-bundle /usr/bin/python3 -B binary/contracts/wd_check.py run --out .tmp/wd
LEANUX_BINARY_TARGET=net-clean-2 cap scripts/in-bundle /usr/bin/python3 -B binary/workloads/two_device.py --out .artifacts/c2-assessment --prepare-only
LEANUX_BINARY_TARGET=net-clean-2 cap scripts/in-bundle /usr/bin/python3 -B binary/packets/rt-c2/rt_c2_capture.py --command .artifacts/c2-assessment/qemu-command.json --out .tmp/rc2 --first 128
cap sh binary/packets/rt-c2/check
cap sh binary/packets/rt-c2/captured .tmp/rc2/visits.jsonl
```

Then run this assessment's `binary/assessment/check_rt_c2.py` on that
`visits.jsonl`. Timing affects the number of visits and interruptions;
zero interruptions in another run would not invalidate the counterexample.
The pilot command intentionally returns zero with failing verdicts: read
`check/summary.json` and `check/failures.jsonl`.

Raw captures, logs and build outputs are ephemeral; the conclusions and
recipes are the retained artifact. No external sandboxed `lake check`
acceptance is claimed for the current tree. Historical external acceptance
is specific to the commits/closures named in the existing binary README.
The larger mirror proof register's lag is unchanged; this assessment is
not an audit of all mirror proofs, ISA semantics or kernel behavior.
