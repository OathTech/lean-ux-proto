# Pre-release review

2026-10-14 — **[AGENT, independent review]**

The project is worth releasing as a research prototype, but several stronger
descriptions of its evidence are vulnerable to fair criticism. The best response
is to repair the small checker and instrumentation gaps, explain the remaining
observational limits beside the headline, and make the domain restrictions earn
their place. Merely declaring an exclusion does not justify it. The absence of a
C-to-mirror proof is an acknowledged boundary, not the finding of this review.

The three most damaging criticisms are these, in order. Each attacks something
the project currently presents as a strength, rather than demanding verification
of all Linux.

## 1. “Your fail-closed coverage boundary can silently miss an unlisted function.”

**Damage: very high. Fairness: established, narrowly reproducible defect in the
advertised contract.** Linux developers, verification researchers and security
reviewers would all reasonably lead with this.

The [decision census, section 6](2026-10-13-decision-census.md#6-the-anchored-file-boundary)
says that a PC in an anchored file outside a listed function is a problem.
The standing rules similarly name “an unlisted function covered” among the
fail-closed instruments. In `evaluator/check.py:935–1060`, however,
`control_flow` intersects both unmapped and foreign coverage with `span_lines`,
the union of **already declared decision outcome spans**. A previously unlisted
function at another line of the same anchored C file is not rejected by that
rule. `decision_functions_run` also considers only functions already owning
declarations, through listed code. Neither operation establishes completeness
of the declarations against the anchored C.

A synthetic probe using the existing `EvaluationChecks.control_flow_fixture`
confirmed the distinction:

| Added attributable coverage | Checker problems |
| --- | --- |
| Unlisted function covering declared `fs/eventfd.c:224` | `span lines covered by an unlisted function` |
| Unlisted function covering `fs/eventfd.c:999`, outside every declared span | `[]` |

The second line is synthetic, not a claim that line 999 in the real file runs.
It isolates the acceptance rule. The surrounding normal decisions and witnesses
are present in both probes. The existing test tests the first case only.

**Fix.** Make the foreign-function check operate on attributable anchored C
coverage independently of decision-span membership. Classify legitimate helper
cuts explicitly and locally; do not replace the intersection with a blanket
exception for “environment.” Add the two contrasting cases above to the existing
checker unit tests. For listed functions, use a small source review to identify
undeclared choices; a new large completeness framework is unnecessary. Report
unclassified covered code as a failure of the claimed boundary.

**Completion evidence:** the outside-span probe is rejected, ordinary covered
cuts still have a named justification, and the relevant differential suites
pass. Until then, say “unlisted functions intersecting declared spans are
rejected,” not “unlisted functions are rejected.” This is a real check gap,
but does **not** establish that an existing passing Linux run had a wrong result.
Calling every prior result worthless would be unfair.

## 2. “You recover an input from the answer, then call the resulting equality an independent check.”

**Damage: very high. Fairness: established for timer-arm sensitivity; broader
schedule overfitting remains a risk, not a demonstrated false pass.** This is
the strongest response to the project's “exact environment rule” discipline.

`Leanux/WG/State.lean:134–153`, `armTimer`, reads `J_m` and expiry `e` from
the arm record, reconstructs the caller's read as `J_c = e - delay`, permits
`J_m - J_c` to be 0 or 1, and stores `J_c + delay`. The stored expiry equals
the recorded expiry by construction. The [items 7–8 note, section 4](2026-10-13-review-items-7-8.md)
calls the equality publication evidence and says a wrong delay mismatches.
That statement is too strong:

| Same record: `J_m = 100`, `e = 110` | Recovered `J_c` | Gap | Stored expiry |
| --- | --- | --- | --- |
| Mirror delay 10 | 100 | 0, accepted | 110 |
| Mirror delay 11 | 99 | 1, accepted | 110 |

These small values avoid wraparound; the example is an algebraic consequence of
the actual function, not an executed whole-kernel mutant. Both admissible delays
produce the same arm update. Conversely, a one-tick real gap can hide a delay
one tick too small. D3-M8 changes the delay by an entire rekey interval; its
rejection cannot establish one-tick sensitivity. Renaming the one-tick freedom
“admissibility” does not remove it from the evidence.

There are related, distinct reconstruction choices:

- `napiIrqExit` consumes a supplementary before-put vector. `section_agreement`
  selects that vector using **comparison operands**, not just hidden-input
  records. The selected vector is now replayed as one complete execution,
  repairing the old stitched-evidence defect. That is valuable, but some
  validation evidence is also used to select the execution being validated.
- `Activation.consistent` tries suspended activations against the remaining
  records. `cryptAhead` uses an upcoming timer-arm site to infer earlier
  encryption, executing the missing iteration at the later TX boundary.
  The recorded guards and ambiguity failures are useful. They still require an
  argument about which effects may move across that boundary, not merely that
  the next record now matches. The current crypt-ahead regression rearranges a
  capture; the integration record says that schedule did not recur in three
  live tier runs. This is useful deterministic regression evidence, distinct
  from a fresh kernel confirmation of the inferred execution.

**Fix.** Record the actual caller-side jiffies read used to calculate expiry,
then compute expiry from it and compare with the publication record. Keep the
separate `mod_timer` read if it is useful. A focused plus/minus-one arm-delay
mutation should distinguish the changed computation. This is a source-input
record, not a new timing tolerance. For NAPI and worker-yield ambiguities, prefer
a source record identifying the placement/iteration; otherwise publish the
small reconstruction relation, its alternatives and its independence/commutation
argument. Keep one full replay and negative examples for inconsistent choices.

**Completion evidence:** different admitted delays no longer disappear into a
reconstructed input; a placement is either source-recorded or openly identified
as a witness selected from observations. Pending that work, describe this as
deterministic **reconstruction from records and comparison evidence**, with
named ambiguities. “A deterministic function” alone is not evidence of unique
correspondence: a deterministic selection algorithm can choose among several
possible executions. This does not mean all recorded randomness or clocks are
untrustworthy; most are genuine source reads.

## 3. “The model decides which experiments count, and ordinary difficult behavior is outside the domain.”

**Damage: very high if the release sounds like coverage of single-CPU WireGuard
as a whole. Fairness: strong methodological and scope criticism, not an allegation
of concealed failures.** Kernel and security reviewers will care particularly
about the excluded compositions.

`load_traces` draws three times the requested generated count, asks the mirror's
placeholder-mode `--domain` which candidates it accepts, and takes the first
requested number of accepted candidates. It reports filtering reasons only
through the last selected candidate. Invariant failures abort and an admitted
trace that later fails is not quietly removed: those are good safeguards.
Nevertheless, this is sampling **conditional on the implementation's own
domain prediction**, not an independently specified Linux workload. A newly
introduced `unsupported` can reduce the challenge set while preserving the
headline agreement count. Placeholder scheduling need not characterize all
recorded schedules of a candidate.

The restrictions also go well beyond one CPU: pending-handshake interactions,
several peers' NAPI polls in one softirq, lifecycle operations with work pending,
one device, nonblocking FD operation patterns, selected routes, selected packet
layouts and finite wait windows. For example, `requireNotPending` rejects a
receive racing a previously queued handshake worker; this includes ordinary
simultaneous initiation, not only SMP races. The receive path also explicitly
stops at a full NAPI budget. These choices can be sensible staging decisions,
but “the fixture does not generate it” is not a profound reason to exclude it
from an otherwise broad subsystem claim.

The [census](2026-10-13-decision-census.md) is useful but its denominator is
declared mirror decisions, not independently enumerated C choices. Its initial
run has 842 exercised witnessable outcomes, 139 witnessable but unexercised,
1,219 unobservable outcomes taken and 564 unobservable outcomes never taken.
The later trace changes those first counts; none is a percentage of Linux
correctness. “Known gaps: 0” means an empty per-operation line-exemption list,
not absence of modeling or coverage gaps.

**Fix.** Keep safety filtering, but pair the selected suite with a small fixed
set of independently chosen boundary/composition cases. Track candidate count,
selected count and rejection reasons as a cheap report when the domain changes.
Do not execute hanging cases blindly: use the existing child/timeout isolation
or classify them explicitly. Make domain shrinkage visible without creating a
new universal gate. Put the most consequential exclusions in the release's
front-page scope table. Challenge each restriction using the assessment below;
close cheap ordinary cases before adding more passing variants of existing ones.

**Completion evidence:** a newly excluded ordinary case cannot disappear merely
by being replaced by another generated success; reviewers can tell why a case
is excluded independently of “the mirror stopped.” It would be unfair to demand
that a prototype model every Linux execution. It is fair to demand that its
chosen domain is useful, defensible, and smaller than the phrase “single CPU”
alone suggests.

## Review scope and ranking

The inspected baseline is `main` **7a926724d5b288bb8b00ab622335e19ded1538b8**.
Work is on `task/pre-release-review` in `.worktrees/pre-release-review`.
The committed campaign snapshots inspected read-only are
`proofs/campaign` **615fb7cf8ac11e519dadb37e8aec19ea6174d06a** and
`task/mutation` **17528964eecabddaa13c471896e02ed39e7a8934**. Branches may
advance; campaign references below mean these snapshots, not their current HEADs.

Starting material: README, AGENTS, the document index and proof register, both
proof charters, the simulation-target review, decision census, compiler
experiment and all four October 13 correspondence audits. Follow-up inspection
covered the checker, harness, environment, affected mirror functions, proof
statements and selected supporting definitions, mutation scripts, configuration,
reproduction guide and upstream tray. This is not an exhaustive C audit or a
fresh validation of the entire proof tree.

The last three integration records were read. The crypt-ahead failure,
1025-receive placement ceiling, order-sensitive sentinel classification and
recorded replay tests have landed; they are not charged again as open defects.
The handshake-ring conversion, nine census arms needing guest/steer work and
the compiler reader's second phase are named follow-ons, not forgotten work.
The campaign's lifetime closure, routing history/removal and packet paths, and
delivery pipeline conservation are in progress. The mutation campaign's lack
of final results at its snapshot is likewise not a finding. Assume each target
will be proved or have its blocker written before sharing; the concern below
is what the resulting statements actually warrant.

Ranking combines potential public damage with strength of the criticism, not
estimated implementation cost. “Established” means source-confirmed or locally
probed; “risk” means a concrete reason for further validation, not a discovered
Linux bug.

| Rank | Critique | Damage | Fairness / evidence |
| --- | --- | --- | --- |
| 1 | Unlisted anchored code can evade the stated fail-closed boundary | Very high | Established checker probe |
| 2 | Reconstructed timer inputs absorb a one-tick error; some schedule choices use comparison evidence | Very high | Established source/algebra; general overfitting unproved |
| 3 | Self-selected domain and unwarranted ordinary exclusions | Very high | Established selection and stops; release framing matters |
| 4 | Property names and Rule Zero dispositions can overstate proved security | Very high | Established statement boundaries; no proof falsity found |
| 5 | Order, multiplicity and two-run projection losses weaken differential claims | High | Established checker/harness behavior |
| 6 | A real mirror/guest domain mismatch is already documented on the proof branch | High | Source-confirmed; accepted witness reported by campaign |
| 7 | The patched oracle needs a clearly stated trust boundary | High | Established boundary; no malicious/incorrect patch alleged |
| 8 | Flood evidence does not establish general flood resistance | High | Established special-case checking and exclusions |
| 9 | Compiler stability is described as a fact about C | High | Experiment's own results do not support that inference |
| 10 | Sentinels measure detection examples, not the probability of finding a defect | Medium–high | Established design; campaign unfinished by agreement |
| 11 | eBPF/seccomp naming can imply a much larger security result | Medium–high | Established service and configuration limits |
| 12 | Some audit findings remain, and declaration counts hide them | Medium–high | Source-confirmed residual choices |
| 13 | Kernel-tray language exceeds the measured reproducer | Medium–high | Established wording/evidence mismatch |
| 14 | Release instructions and proof status disagree | Medium | Established documentation drift |

## 4. Proofs: distinguish the theorem, its boundary, and the security interpretation

**Likely criticism:** “You have mechanically proved a convenient reformulation
and retained the original security headline.” This would be devastating if true.
The campaign is substantially better than that accusation: it records original
and revised wording, retires a false chronological theorem, distinguishes
generated witnesses from captures, and states important premises explicitly.
The remaining risk is in summarizing that work for readers who will not inspect
hundreds of declarations.

The following is the required statement-level reading, rather than a complaint
that the open proofs have not finished:

| Result | What the inspected statements establish | What must not be inferred; proposed presentation/fix |
| --- | --- | --- |
| Landed ReplayWindow S1 | For a successful `executeTrace`, an exactly erased logged execution has a duplicate-free committed validator-acceptance history, keyed by allocation lifetime and wire nonce. This includes validator successes whose packets are subsequently dropped. | Not authenticated delivery, uniqueness of cryptographic key bytes across allocation lifetimes, or all Linux executions. Call it validator replay freedom per allocation lifetime. Keep the observer-to-original connection and explain its event boundary. |
| S2 | Refinement from `counterValidate` to the Lean `CounterWindow.step` rule, with an allocated keypair and a 128-word bitmap. | “The C's rule” is an informal source identification of `step`, not a theorem about compiled `receive.c`. Link the C rule and say the refinement is entirely within Lean. The size premise is reasonable; explain that reachable allocation establishes it. |
| S3 | Framing for surviving old cells of nonreceive calls, and other keypairs during a validator call; whole-operation evolution includes ambient work. | Not literal equality of every keypair store through allocation/deletion, nor a claim that a batch receives only one packet. The lifetime-aware revision is justified and should replace the literal original wording in summaries. |
| R1 | Uniqueness and an inclusive window floor. The boundary witness accepts unseen equality at highest minus 8128. | The charter's “at or below” rejection was false. This correction is legitimate, explicit and small. Keep the original wording and the equality witness visible; do not repeat the old inequality in publicity. |
| R2 | Endpoint identity results and local access contracts have explicit resident/allocation and callback premises. | Even eventual whole-run resolved-access safety is not automatically ownership of every saved scalar ID or C memory safety. The campaign itself distinguishes reference retargeting from resurrection. Require the final advertised property to name which of these it proves. Its current closure work is not a review finding. |
| R3 | Lookup/insertion relates represented tries to an independently defined flat-prefix winner, under shape, address bounds, fresh-ID and resident-target premises. | A trie winner labelled with a raw peer slot is not yet cryptographic identity authorization. Final packet-path results must bind that slot to the live peer/keypair identity and establish premises from supported histories. Do not market a pure trie result alone as cryptokey-routing security. The remaining refinements are already in progress. |
| R4 | Local queue/poll provenance, selected GRO order and callback-entry facts; the original post-GRO chronological statement was explicitly retired. | Callback entry is not successful delivery, local ordinals are not global packet identities, and a finite run may end with pending obligations. Normal-before-held GRO ordering is materially different from chronological arrival order. Keep the retired statement, replacement boundary and counterexample side by side after conservation lands. |
| R5 | Thirteen local contracts about admission clocks/counters, original execution and observers; accepted mirror witnesses refute literal encryption-age and post-zero-use wording. | “Resolved under Rule Zero” is not “key lifetime enforcement proved” in the charter's original sense. RX checks stored counter before AEAD, wire nonce later; TX checks age at staging, not at later encryption; queued references may outlive clearing published slots. Name the proved admission contracts and the false original claims separately. A later use theorem needs the transport/ownership connection or a written blocker. |
| R6 | Under an actual load-phase execution and actual MAC predicates, an invalid-MAC2 initiation takes the cookie suffix and preserves the Noise view on normal completion; invalid MAC1 is also covered. | `FailedMac2` includes actual prefix/clock/cookie execution premises. It does not assume the final Noise-preservation conclusion, so calling the theorem circular would be unfair. It also does not show real load reaches this prefix, bounded CPU/memory cost, availability, or a universal retry-episode theorem. The 19-retry/20-initiation witness corrects literal `MAX_TIMER_HANDSHAKES=18` wording; it is a counterexample, not by itself the corrected universal bound. |

`S1` quantifies over successful runner executions, including the placeholder
parameter. This is a strong universal statement **over that executable**;
arbitrary admitted record streams need not be realizable kernel schedules.
A failed runner can discard an intermediate World under `StateT ... (Except
Stop)`. Thus a success-conditioned theorem alone says nothing about the
successful prefix of a later stopped run. The campaign's failure-retaining
local observers are a useful response, but their coverage must be stated per
result, not transferred to every theorem by association.

For security claims, source intent also needs its own authority. The
[WireGuard paper, sections 6.2–6.4](https://www.wireguard.com/papers/wireguard.pdf)
describes transport-age limits, session rotation/zeroing and retransmission.
Those descriptions make the R5/R6 questions reasonable. They do not establish
the reachability of a generated scheduler witness in Linux. Conversely,
“unrealistic worker latency” without a bound is not a proof of impossibility.
Use the paper as protocol intent, the pinned C as implementation behavior,
and the Lean theorem as a fact about its definitions. The paper is not a
specification of every implementation boundary in Linux 6.12.110.

**Fix and completion evidence.** Publish a short result table with the original
claim, exact theorem, event boundary, substantive premises, counterexample or
blocker, and mirror pin. There is no need for more theorem-count machinery.
Audit a meaningful nonempty accepted witness for each observer-based headline;
erasure alone would also hold for an observer that logs nothing. Credit the
campaign's existing coverage/projection proofs rather than demanding duplicate
ones. Distinguish theorem results, erasure infrastructure and counterexamples
when giving counts. A proved blocker is valuable science; it is not the original
security theorem. C memory safety, constant time, cryptographic security and
physical erasure of secrets remain separate claims.

## 5. The checker observes sets and projections, not complete execution equality

The [correspondence README](../correspondence/README.md) already discloses
within-function ordering and comparison multiplicity limits. The actual
limitations deserve equally prominent treatment in the release:

- `control_flow` retains first decision occurrence for order and later outcome
  membership for repeatable decisions. It cannot establish iteration counts,
  later-iteration order or general cross-function ordering. A witness can be a
  shared source line, not a unique invocation.
- `operand_agreement` requires each model pair to have **some** matching kernel
  record at the source site in that operation. Rows are reusable; surplus
  kernel pairs are not consumed or required to have a model counterpart. A
  local probe returned `([], 3)` for three identical model reports, one matching
  kernel pair and a second, unmatched kernel pair at the same site. Thus the
  latest integration's 1,192,792 matched pairs is a count of successful model
  obligations, not 1,192,792 distinct independent comparisons. Operand swapping
  is deliberately accepted for nonconstant comparisons.
- PC and CMP are separate guest executions with separately replayed inputs.
  `harness/linux.py:720–727` compares returns, read bytes, FDs, digests and signal/
  child outcomes between them. It does not compare the complete WireGuard dump,
  datagrams, replies, statistics and CQEs there. `run_chunk` compares complete
  observations for the PC replay, operands for the CMP replay, and only return
  values between the two model replays. This is two related experiments, not
  all evidence from a single execution.
- `attach_observed` sorts all datagrams and replies. Its reason is uncertainty
  across peers, but global sorting also removes **within-peer** order. Exact
  packet bytes and multiplicity can agree while a delivery sequence differs.
  This matters independently of completing R4: a wrong environment ordering
  could satisfy a theorem about the mirror and evade this observable.

The official [KCOV documentation](https://docs.kernel.org/dev-tools/kcov.html)
describes a fuzzing-oriented, compiler-instrumented observation facility, with
mutually exclusive PC/CMP modes and explicitly annotated remote coverage. It
does not promise a complete semantic trace. Using it here is sensible;
equating its projections with complete control-flow equality is not.

**Fix.** State the projected relation precisely. Prefer cheap strengthening at
important repeated sites: section/call identity, distinct operand-pair coverage
in both directions where attribution permits, and per-peer packet order while
allowing cross-peer interleavings. Do not demand consumption of every compiler
comparison globally. Compare each child's full relevant outputs against its
own replay, with explicit treatment of naturally varying random bytes. Count
distinct matched rows separately from model obligations. Add a duplicate/reorder
case whose intended detection channel is named. If those improvements are
deferred, explicitly exclude differential evidence for order and full iteration
correspondence; do not claim the proof makes those observations unnecessary.

## 6. An accepted mirror can cross a boundary the guest forbids

The campaign report at `615fb7c`, R2, records an accepted synthetic replay that
starts a stepped dump, deletes/recreates the device, and later cleans up the
old dump cursor against a replacement peer at the same raw slot. The old
identity is not resurrected; the new identity is incorrectly released.
This is a concrete **mirror-domain** finding, not a Linux lifetime vulnerability.

The relevant asymmetry is still present at the reviewed main:
`harness/guest.c:2494` rejects `wg_delete_with_dump_pending`, while
`Env.wgDelete` only requires worker idleness. A cursor's Boolean device presence
does not bind it to the original device lifetime. The campaign's accepted
witness was not rerun here; the guard mismatch was inspected directly.

**Fix.** First make the declared boundary consistent: refuse deletion with a
pending dump in the mirror, with a focused accepted/rejected-domain regression.
That is a correspondence-driven repair, not editing the mirror to make a proof
close. If this lifecycle composition is to be supported, give the cursor its
actual device/peer ownership and model the C's retained references instead.
The exclusion itself also needs a reason and eventual disposition; a guard is
the immediate correctness repair, not a claim of complete lifecycle coverage.

This is not criticism of the campaign's unfinished lifetime proof. It is a
finding the campaign has already produced which must be triaged outside that
proof work before treating the runner's accepted domain as the guest's domain.

## 7. The oracle is a configured, patched executable, not unmodified Linux

The identity gate is a strong reproducibility measure. It does not show that
`choice-stream.patch`, its generator, record arming, steering, virtual clocks,
remote section boundaries or the guest preserve the behavior of an ordinary
kernel. Recording itself changes timing and allocation pressure. Steering
failures and clock advances can deliberately choose executions outside normal
operation; the separately labelled failslab extension is good practice.

There is no evidence here of a bad-faith oracle patch. The fair concern is
shared mistakes: the same interpretation can shape the mirror, instrument,
fixture, declared spans and expected output. An identity hash faithfully pins
such a mistake too. Crypto primitives, packet construction/decoding and the
seccomp engine seam add further trusted implementation boundaries.

The actual target includes `CONFIG_SMP=n`, `PREEMPT_NONE`, `HZ=250`,
`CONFIG_BPF_JIT=n`, no user namespaces or netfilter, and a 256 MiB QEMU TCG
guest (`pc-i440fx-8.2`, `qemu64`, one CPU, `-nic none`). In-guest traffic
does not test a physical NIC, DMA, hardware offload, real driver receive paths,
weak-memory races or production performance. Single CPU still has interrupts,
softirqs, sleeps and reference lifetimes; it is not evidence those issues vanish.

**Fix.** Publish a short trusted-boundary account distinguishing record-only
hooks, value steering, virtual-time changes, observation decoding and service
cuts. Review the instrument's source location/effect independently of the
mirror function it supports. Run a small observation-level unsteered smoke
sample against a matched stock build using a deliberately separate observation
driver; do not weaken the approved-oracle identity gate. Timing distributions
and random bytes need not match: compare deterministic observables and stated
behavioral invariants. Such a smoke test is evidence, not instrumentation erasure.
State the hardware/configuration boundary upfront. SMP and physical-hardware
expansion are defensible future work, not a prerequisite for this prototype.

## 8. Flood resistance has a narrower experiment than its name suggests

`control_flow` special-cases `wg_flood`: it requires coverage of
`receive.c:115`, then skips the normal decision checking for that operation.
`Env.flood` models leading valid messages but summarizes the invalid tail and
producer sections, folding the tail's clock records into saved load state.
The earlier constant-decay defect has been repaired; this is not that old
finding. The summary is explicit and fail-noisy for unexpected records.

Still, the real queue threshold is `handshakeQueueLen >= 512`, reported with
`branch`, not `branchCmp`. The receive audit's F9 already identifies the missing
operand evidence. Large above-threshold floods cannot tightly establish the
boundary. The rate limiter refuses IPv6, allocation failure and table exhaustion;
its periodic GC is outside this path. A cookie-gating theorem cannot establish
availability or resource bounds for these omitted mechanisms.

**Fix.** Call the current result “cookie gating under the modeled load state.”
Use ordinary batch cases around 511/512/513 with a valid leading initiation,
or a source record if exact queue depth is otherwise ambiguous, and declare the
threshold operands. Check the summary against a small unsummarized execution
where both apply, including decay and a later valid message. Prioritize IPv6
`/64` rate-limit behavior and allocation-failure cleanup over more same-shaped
IPv4 floods. Treat capacity/GC and adversarial scheduling as explicit future
resource-policy work. Demonstrating cookie rejection alone is useful; calling
it a general DoS-resistance result would be unfair to the evidence.

## 9. Two compilations are not a proof of C semantics

The [compiler experiment](2026-10-13-compiler-experiment.md) is candid that no
`-Os` observations were obtained: startup failed at the function list, shared
exits and a fixture constant. Its tables nevertheless call 969 common witnessed
outcomes and 311 common comparison sites a “C-semantics core,” and its final
simulation recommendation calls those declarations facts about C on which two
compilations agree. Static hook/source-location stability cannot support that
inference. Both builds use GCC 13.3.0; dynamic operands/order remain unmeasured.
The integration summary also says “969 of 1382 decisions” where the experiment's
table counts **outcomes**. Those units must not be interchanged.

**Fix.** Rename the result “witness-location stability across two optimization
levels,” retain the exact denominator, and separate C source reasoning from
compiler evidence. The dynamic second phase is already a named follow-on;
report its eventual results separately. Make the function/exit tables explicitly
build-bound and record image-dependent fixture values per identity. A later
different-compiler comparison would be useful evidence, but requiring it now
as a new release gate would overshoot the prototype's stated target.

Even two successful dynamic builds would test more implementations; they would
not upgrade the correspondence to a simulation theorem. The pinned-build
restriction itself is justified. The semantic conclusion drawn from stability
is the part that needs correction now.

## 10. Mutation evidence: keep power separate from presence

The sentinel scripts deliberately choose one known rejecting example per
channel, on a favorable small corpus subset. That tests that the channel still
works. “13 of 13” is not a sensitivity estimate over plausible mirror errors.
The latest inconclusive rules correctly distinguish absent scheduling opportunity
from survival; earlier order-dependent reruns are disclosed. Do not undo that
improvement by presenting only the final rejection total.

At the inspected mutation snapshot, mutants include decision/condition negation,
operators, constants, returns, operand swaps, skipped records and stops. The
report is unfinished, as expected. In particular, operand-swapped mutants at
nonconstant compares can be observationally equivalent under the declared
checker relation; a survival there need not indicate a missed semantic defect.
A mutation that merely corrupts logging and trips a hidden-record mismatch is
also different evidence from one changing behavior with logging intact.

**Fix.** In the final campaign conclusion give the sampled population and
selection method, then counts for applicable semantic mutants, equivalent
projection mutants, uncompilable mutants, no-verdict/inconclusive cases and
confirmed survivors. Report distinguishing opportunities for schedule-sensitive
cases. Explain survivors one by one without excluding them merely because the
current corpus missed their boundary. Give a few behavior-changing examples
detected by each claimed channel, including one-tick timer changes and repeated
comparison/order changes from this review. Retain the conclusion and reproduction
command, not run dumps. No larger permanent sentinel catalogue is proposed.

## 11. Seccomp and eBPF need a precise public scope

The implementation covers a useful classic-BPF checker/translation and seccomp
filter-chain/cache slice. `kernel/bpf/core.c` is a service boundary, not anchored
C correspondence; `Leanux/Seccomp/Engine.lean` implements the translated subset.
`BpfEngine` supplies a `run` field, not a proof that an arbitrary instance
satisfies the prose ISA contract. The shipped interpreter's tests and the
translation byte records are valuable; they are not a verified eBPF JIT,
general eBPF verifier, or translation-correctness theorem.

Specific restrictions merit attention rather than automatic acceptance:

- Single-thread TSYNC is explicitly a no-op scope choice in the design, not a
  concurrency impossibility. Add that cheap case, while retaining the justified
  exclusion of actual multi-thread synchronization.
- Instruction-pointer reads are excluded because the IP is not recorded.
  Capture it at the source if these filters are claimed; it is an ordinary
  input, not a fundamental modeling obstacle.
- The generator avoids ERRNO values treated by the harness as infrastructure
  failure, including 4, 12 and 23. EINTR/ENOMEM/ENFILE are ordinary policy
  results. Distinguish deliberate seccomp results from guest failure using
  provenance/status, and add targeted child probes. Merely omitting them biases
  action coverage. The same concern applies to the comparison classifier.
- Filter release walkers and exit effects sit outside recorded windows; strict
  mode is tested in an isolated child; USER_NOTIF, tracer-mediated TRACE and
  actual threaded TSYNC need wider mechanisms. Name those limits beside
  “seccomp,” especially when describing filter lifetime behavior.
- The 768-instruction practical recording ceiling versus the 4096-instruction
  input limit is an instrumentation-size restriction. The prefill fixture is a
  reasonable way to test aggregate path budgets, but it does not cover every
  long single-filter translation. Add a sparse long-filter observation/translation
  test or explicitly defer that boundary.

**Fix.** Label the feature “single-task seccomp with classic-BPF translation and
an interpreter service.” Keep the concrete instance and byte-image comparison
visible. If future theorems are parametric in `BpfEngine`, state semantic laws as
premises rather than relying on the class name. Do not advertise sandbox
security: the [Linux seccomp documentation](https://docs.kernel.org/userspace-api/seccomp_filter.html)
itself distinguishes syscall filtering from a complete sandbox. These are
scope clarifications and targeted extensions, not a request to take over the
separate JIT project.

## 12. Finish the cheap correspondence repairs the audits identified

The four audits are valuable precisely because they found mistakes after green
differential runs: MTU errno, cookie rotation, receive queue-full cleanup and
endpoint layout interpretation. Those fixes have landed. This supports the need
for structural review; it does not invalidate the differential method.

Some smaller issues remain at this baseline, independently of the named
handshake-ring follow-on:

- `cookieValidatePacket` still has a plain rate-limit-result `if` at the C's
  cookie.c:147 test (receive audit F2).
- `sendBufferAsReplyToSkb` explicitly says its enclosing function is unlisted;
  allocation failure and family selection lack their own declared decisions
  (F3). “The function is not listed” explains why the checker misses them,
  not why a whole-function correspondence claim should omit them.
- IPv6 rate limiting and its `/64` key are excluded with an old stage label
  (“arm C is IPv4”), and its allocation outcome still uses `envOk` with an
  unsupported failure arm (F12/F13).
- `wgXmit` uses an environment-supplied destination for lookup rather than
  checking it against the packet header (device audit X6). The empty-packet
  guard has now been added; do not repeat X8 as still open. The GSO/list-length
  representation and helper assumptions still need an explicit contract.

**Fix.** Add the missing decisions/functions, the matching allocation record
where appropriate, and a small check that header and supplied destination agree
at the environment boundary. Keep sensible helper abstractions, but say what
inputs/results and state effects each summarizes. For structurally implied
branches such as the ECN tail checks, supply the local implication or an explicit
helper contract; a branch-free compiled body is not by itself a source-level
justification for omitting the C condition. Use a short disposition table for
the audit items: fixed, justified, deferred with reason. Do not let a verdict
paragraph saying “every conditional” override its own omissions table.

## 13. The findings tray should read like a maintainer's bug report

The tray sensibly calls the full-ring losses an observability gap/design nuance,
not a vulnerability. Several formulations still invite an easy public rebuttal.
Draft 02 says “no tracepoint”/“no signal at all” while its own source section
identifies `skb:consume_skb`. That may be inadequate drop attribution, but it is
not absence of tracing. It says 1024 empty keepalive messages are “delivered”;
that must be distinguished from inner payload delivery. It still says the
1025-receive trace is excluded by the old placement bound, although 7a92672
includes it in the passing six-trace tier.

The non-repository reproducer assumes a burst queues everything before worker
drain. The recorded `io_uring` fixture establishes a particular order; a generic
user-space burst does not guarantee it. Similarly, source-level unauthenticated
queue admission supports a resource-contention question, not yet a measured
off-path denial-of-service capability under ordinary worker scheduling. An
attacker holding a captured packet also has a specific capability; state it.

**Fix.** Use “not counted as a device drop; freed through consume_skb rather than
the drop tracepoint,” distinguish keepalive processing from inner delivery, and
update the reproducer's status. Supply a minimal stock-kernel reproducer with
explicit scheduling prerequisites before filing. Separate recorded loss,
source-derived mechanism and attack feasibility. Revise “not defensible” and
“every other discard” in draft 01 into the narrower observed inconsistency in
accounting; avoid universal claims unsupported by an enumeration. Kernel
maintainers can reasonably debate whether to add counters. That debate is not
evidence the mirror discovered a security flaw or that its measurement was false.

## 14. Release coherence and independent reproduction

The README says the first proof is “landed and current”; the live proof register
says it is lagging since `247beec`, at `CounterWindow/Refinement.lean`. Its repair
on the running campaign is expected work, not a failure of that campaign. The
public root must nevertheless name the actual status of the revision a reader
checks out. Otherwise the documented proof command will make the release appear
careless even if all the research conclusions are sound.

`REPRODUCING.md` also describes an old four-module fast tier, names the approved
build “e2” while recent claim records call it “s2,” and omits seccomp suites and
options from its explicit list. The identity, not a directory nickname, is the
authority. “Exactly” the three allowed axioms is inaccurate: the gate accepts
any subset, including none. The dated document index does not yet lead readers
to the census, compiler experiment and four audits on which the broad claims
rely. Many older stage exclusions are stale despite remaining the nearest link
from a census row.

**Fix.** At the chosen release revision, reconcile README, proof register and
setup guide, publish the mirror/kernel/toolchain pins, and run the documented
small first-run and proof commands in a clean worktree with private outputs.
Use the toolchain's kernel replay at the proof claim point as the campaign has
already done; do not substitute theorem counts or a green default build for
axiom checks. This review did not rerun that gate and makes no new claim about
its result on main. Update stale prose in place and link the source audits from
the index. Keep one short result/conclusion with reproduction commands; no
archived logs or extra release bureaucracy is needed.

## Which declared limitations are warranted?

This assessment is deliberately independent of whether a restriction is already
documented. Cost estimates are relative engineering judgments, not commitments
to implement changes in this review.

| Limitation | Assessment | Best response before public claims expand |
| --- | --- | --- |
| No C simulation, byte-level memory semantics or memory-safety result | Warranted research boundary; cannot be repaired by more traces | State it early; retain source-shaped state and service contracts for later simulation. Do not promise that the later proof will be straightforward. |
| One CPU, fixed architecture/configuration and no hardware drivers | Warranted first target; excludes central production behaviors | Publish the exact target and no SMP/offload/performance implication. |
| One WireGuard device | Useful staging restriction, weak as a permanent “single-CPU WireGuard” boundary | Prioritize the already scoped W13 device map/demultiplexing/two-NAPI work; until then say one device. Multiple devices need no SMP. |
| Pending-handshake interactions, multi-peer NAPI, full-budget polling and busy deletion | Ordinary single-CPU behaviors; timing uncertainty is an engineering gap | Record/represent the missing placement and ownership. Use a few composition cases; do not justify absence solely by current fixture shape. |
| FD slice without general blocking/concurrent tasks | Defensible subsystem slice, not general pipe/epoll semantics | State nonblocking/zero-timeout and single-task boundaries; separate future concurrency from available single-task boundary cases. |
| IPv6 rate limiting and periodic GC | Old stage constraints, poorly aligned with a flood-resistance headline | Implement `/64` behavior and select GC/capacity tests or narrow the headline. |
| Cross-layout endpoint bytes rejected | Safe immediate containment, weak long-term protocol boundary | Prefer raw attribute bytes and C interpretation; malformed netlink is a plausible security workload. |
| Single-thread TSYNC and seccomp IP loads | Cheap ordinary cases excluded for convenience | Add the no-op path and record the missing IP. |
| USER_NOTIF, actual thread synchronization and ptrace protocols | Substantial new protocols and ownership; defensible deferral | Explicit feature boundary; do not imply complete seccomp policy support. |
| Reserved ERRNO policy returns and long-filter recording ceiling | Harness limitations, not semantic exclusions | Separate policy results from infrastructure failures; add sparse long-filter tests. |
| Constant-success/unrecorded allocation sites and below-cut failures | Sometimes a valid helper precondition, not full allocation-failure coverage | Name sites/effects, use focused failure steering where meaningful, report which error paths remain excluded. |
| Two-read timer gap at most one tick | Bounded fixture assumption, not a theorem of one-CPU Linux | Capture the first read; report stalls distinctly and keep them outside any unqualified timing claim. |
| Finite waits, no filter-release/exit window | Practical observation boundary with real omissions | State prefix/window semantics; test teardown if lifetime claims depend on it. Pending work is not proof of eventual delivery. |

## What each audience would fairly say—and what would be unfair

| Audience | Strongest fair criticism | Unfair overreach and the evidence-based response |
| --- | --- | --- |
| Linux kernel developers | Too many ordinary paths excluded; record/fixture effects and source correspondence need scrutiny; tray accounting claims need precision | “One CPU makes the work useless.” It isolates substantial real control/data behavior and has already exposed correctable mirror defects. Show exact supported compositions rather than claiming production coverage. |
| WireGuard developers | Replay validation is not delivery or protocol security; post-GRO order and key-reference lifetime differ from loose charters; IPv6/load/lifecycle boundaries matter | “The counterexamples prove WireGuard is broken,” or the opposite, “a false charter proves the exercise worthless.” Preserve the corrected property and classify source-backed nuances without inventing exploits. |
| eBPF/seccomp community | Interpreter-only, classic-filter subset, no general verifier/JIT, missing policy/context/lifecycle cases | “No JIT proof means no seccomp contribution.” Translation images, cache precedence and action behavior are useful independently. Name the exact service seam. |
| seL4/Isabelle/Lean and C-simulation researchers | Relation/premise adequacy, oracle admissibility, event coverage and abstraction contracts are not supplied by axiom checks | “No C proof means no formal result.” The mirror theorems are formal results; their transfer to Linux remains empirical. Do not compare theorem counts to end-to-end verified systems. |
| Security practitioners | What attack property, adversary capabilities, execution window and configuration are actually covered? Could filtering or sorted observations hide the behavior of interest? | “AI authorship itself refutes the result.” Authorship is not a technical counterexample. Reproducible definitions, source comparisons, kernel checking and disclosed counterexamples are the appropriate response. |

These are anticipated arguments, not claims that particular people or
communities have endorsed the project or made these criticisms. Independent
judgment is more valuable than another favorable verdict from the same
implementation assumptions. A later external reviewer should get the tree,
setup, intended claims and open concerns, with freedom to challenge any part.

## Recommended release work, in order

1. **Repair the two concrete evidence defects:** the foreign-function/span
   intersection and timer-input reconstruction. Also triage the known
   dump/delete domain mismatch outside the proof campaign. These changes should
   be separately implemented and validated; this document changes no code.
2. **Write the public claim at the actual observation level:** one configured
   patched executable, selected supported traces, projected branch witnesses,
   operand presence, reconstructed scheduling choices, finite windows and
   separately pinned mirror theorems. Preserve the research ambition without
   presenting it as achieved complete equivalence.
3. **Close a small number of high-value scope holes:** missing audited decisions,
   threshold operands/boundary tests, within-peer ordering evidence, IPv6 rate
   limiting and the cheap seccomp cases. Prioritize ordinary composition over
   larger counts of similar traces. Keep W13 and expensive concurrent protocols
   visibly deferred if not undertaken.
4. **Finish the already running campaigns on their own terms:** publish actual
   theorems/blockers and mutation denominators. Do not add acceptance gates for
   every recommendation or make proof completion a gate for mirror work.
5. **Reconcile the chosen release revision and tray, then reproduce its short
   public commands.** Keep build/unit/differential/identity checks and the
   separate proof gate as the established trust surfaces. The proposed reports
   and boundary reviews are small claim-point checks, not a new audit system.

A defensible short description, after reconciling the findings, would be:

> An executable Lean mirror of selected paths in a pinned, instrumented,
> single-CPU Linux configuration. Differential tests compare observations,
> declared branch witnesses and comparison operands, replaying recorded inputs
> and explicitly reconstructing some scheduling choices. Separate Lean theorems
> establish named properties of the mirror at stated boundaries. Neither the
> C-to-mirror correspondence nor general Linux or WireGuard security is proved.

## Validation of this review and reproduction of the probes

The **model executable build passed (118 jobs)** with
`capped -- scripts/in-bundle lake build leanux-model`. The fast-tier modules
completed in three invocations: `evaluator.test_evaluation` (51),
`harness.test_trace harness.test_wg harness.test_linux` (43, one skipped), and
`evaluator.test_model_replay` (16), each through
`capped -- scripts/in-bundle python3 -B -m unittest`: **110 tests, 109 passed
and one skipped**. The evaluator's printed zero-trace failure report is an
intentional unit-test case, not a failed differential run. No kernel build,
QEMU run, proof gate, full differential check or mutation campaign was run here.
Historical counts and
campaign witness outcomes above are attributed to their committed reports;
they are not represented as fresh results. No substantive local code change
was made to investigate a finding.

Run the following in a worktree at the reviewed pin to reproduce the two
checker probes. They do not execute the model or kernel and write no test file:

```sh
capped -- scripts/in-bundle python3 -B - <<'PY'
from evaluator.test_evaluation import EvaluationChecks
from evaluator import check

run = EvaluationChecks().control_flow_fixture()
cells = dict(zip(run.__code__.co_freevars,
                 (c.cell_contents for c in run.__closure__)))
cells["loc"]["0x999"] = [{"function": "unlisted_function",
                         "source": "/x/.deps/linux/fs/eventfd.c:999"}]
ready = ["eventfd_read.short_buffer=0", "eventfd_read.empty=0",
         "eventfd_ctx_do_read.semaphore=1"]
print(run(ready, [222, 235, 999]))
print(run(ready, [222, 235, 1224]))

comparison = {"rel": "ge", "const_rhs": False, "site": None}
decisions = {"alloc_fd.at_limit": {"site": "fs/file.c:514",
                                   "comparison": comparison}}
loc = {"0x1": [{"function": "alloc_fd",
                "source": "/x/.deps/linux/fs/file.c:514"}]}
model = {"branches": [{"index": 0, "label": "alloc_fd.at_limit=0",
                       "operands": [8, 32]}] * 3}
records = [{"records": [[4, "0x8", "0x20", "0x1"],
                         [4, "0x9", "0x20", "0x1"]]}]
print(check.operand_agreement({"ops": [{"op": "dup"}]}, model,
                              records, loc, decisions))
PY
```

Expected: `[]`, the one foreign-span problem, and `([], 3)`, respectively.
For the timer example, substitute the two delays into `armTimer` at the pin;
both satisfy its gap guard and store 110. This establishes the instrument's
indistinguishability, not the outcome of an unrun full-suite mutant.

To inspect the proof evidence without relying on moving worktrees, use
`git show 615fb7c:docs/2026-10-13-proof-campaign.md` and each result's
`Leanux/Proofs/WG/<Result>/Statements.lean` at that commit. The mutation
method is in `git show 1752896:docs/2026-10-13-mutation-campaign.md`.
External primary documentation linked above was consulted on 2026-10-14;
repository conclusions are about the pinned local source, not a newer online
kernel version. Recommendations are this reviewer's proposals, not adopted
standing rules or user authorization to implement them.
