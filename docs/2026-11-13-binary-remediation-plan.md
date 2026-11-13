# Binary verification remediation plan

Status: proposal for review, not authorization to implement or merge.
Proposed sequencing and technical choices [AGENT 2026-11-13]. The basis is
the [execution-based assessment](2026-11-13-binary-assessment.md), at current
main `9ca4b0655d8a` and the archive revisions it identifies. Its conclusions
are evidence to challenge, not premises a reviewer must accept.

## What we are trying to establish

The intended result relates the compiled WireGuard instructions in a fixed
Linux image to the project's executable operational mirror. There are
three different jobs:

* **Admission:** show that the exact assumptions and asserted invariants
  describe captured Linux executions, at the real image's parameters.
* **Local verification:** prove that an admitted instruction execution has
  the specified behavior, including its effects on memory and services.
* **Composition:** show that real intervening actions preserve or establish
  the next call's assumptions, using one consistent heap, identities and
  source execution throughout.

A frame is the part of state promised to remain unchanged. A service is a
callee or environment action represented by a contract rather than by
executing its instructions. A hand-over is the transition from one call's
result to the next call's entry. Those are substantive obligations, not
bookkeeping. A universal service assumption remains conditional even if
all sampled calls satisfy its executable instance.

The existing sequential function results remain useful at their stated
scope. This plan does not promise a verified whole kernel, cryptographic
security, or a proof of Kraken's ISA fidelity. It also does not count a
successful prefix, a NULL-allocation witness, or an unexplained scope exit
as a successful instance of a path intended to perform useful work.

The first deliverable is a defensible current binary package. The next is
a small, useful composed result. Expansion to a driver lifecycle follows
only after those have passed. No existing mirror behavior is changed to
make a binary proof close.

## Stages at a glance

| Stage | In plain language | Concrete output | What it would establish |
| --- | --- | --- | --- |
| 0. Fix the claim inventory | Say precisely which promises we are testing | Updated existing binary register, with exact statements, pins, unchecked assumptions and chosen workloads | An honest scope and a finite remediation backlog; no new correctness result |
| 1. Repair current validation | Make tests exercise the promises the current proofs actually use | Complete captured admission and return checks for each retained claim, or an explicit unresolved status | Which current claims admit real calls, with remaining universal assumptions named |
| 2. Recover a small archive toolkit | Bring back useful instruments without importing their old conclusions | Selected clean-image generators, capture/checker code and instruction changes, reviewed separately | A trustworthy basis for testing candidate statements on the selected image |
| 3. Repair the receive-window claim | Explain what interrupts may change, and what must stay fixed | An executable C2 statement with a justified frame and lifetime interpretation, followed by a scoped proof | A useful receive-window result in an explicit execution environment |
| 4. Repair service and source interfaces | Ensure the proof describes the real callees and the actual mirror | Executable service instances, explicit universal obligations and the missing mirror bridge where needed | A sound basis for recovering insertion and other service-dependent results |
| 5. Verify a real joined sequence | Carry the same state through actual successive calls | Captured repeated receive visits, then an insertion/lookup sequence, and only then composition proofs | Hand-overs that occur in real executions, rather than compatible-looking isolated assumptions |
| 6. Expand through a driver lifecycle | Add the previously missing configuration, handshake and teardown paths | A tested create/configure/open/handshake/receive/teardown slice with explicit remaining boundaries | Exactly that lifecycle slice; broader driver coverage remains separately reported |

Dependency order: `0 → 1 → 2 → 3 → 5` for the first window sequence;
`2 → 4 → 5` for insertion and source/service recovery; both feed stage 6.
Stage 4's interface investigation can proceed beside stage 3 after the
image is fixed. This is a dependency graph, not a promise that later
stages will be feasible at a particular cost.

## 0. Fix the claim inventory

Use the existing binary section of `docs/proofs.md`, `binary/README.md`
and the printed trust surface. Do not create a second registry or an audit
framework. For each advertised result group, link the exact declarations,
their reachable assumptions and the runtime checker for each assumed or
asserted predicate. Record the mirror commit, image identity, semantics
pin, numeric layout/size parameters, scheduling scope, and whether the
checker uses the original mirror or a supplied-answer model.

Start with all eight groups in the assessment's current-component table:
lookup/peer-get, removal/replacement, callbacks, trie lookup, index
insertion, retained sequences, partial trie mutation, and lookup transport.
Helper lemmas need no duplicated register entries; an assumption cannot
disappear merely because it is hidden behind one. Preserve the distinction
between concrete admission, a formal satisfiability witness, and a universal
service theorem. Mark an untested conjunction as untested.

The existing s5 results keep their image. Proposed new archive recovery
uses the saved clean image `net-clean-2` in an isolated target; stage 2 must
verify that choice before any port. No s5 result transfers just because
the clean-image function has the same name. Rebuilding or changing an
oracle follows the existing behavior/configuration approval rules.

**Exit:** every current advertised group has an owner, a reproducible
admission experiment or a named missing ingredient, and a truthful scope.
Unrunnable predicates are unresolved exceptions under the standing rule,
with their reason stated; finite sampling is not their discharge. New
proof work for an affected statement waits until this is settled.

## 1. Repair current validation

Make one invocation test the conjunction its claim uses: entry, internal
invariants, service instances, frame, source acceptance and return. Use
the actual predicate definitions, or a checker whose equivalence is
established. Keep record sources and allocation identities from the same
boot. Independent mirror replay predicts the source state; reconstructing
that state from the binary heap is a separate representation test and
cannot substitute for it.

Specific work:

* Connect the lookup capture runner to `IndexLookup.callBoundary` and its
  additional headline/transport obligations. Combine the successful
  full-allocation entry check and the return replay on the **same capture**.
  The assessment did not complete that combination.
* Diagnose the full-buffer lookup replay's resource failure before raising
  another cap. Prefer sharing, streaming comparison or avoiding retained
  redundant snapshots. Preserve the original capacity and every byte
  required by the predicate. Any changed memory representation must have
  its semantic correspondence checked; truncating or fabricating a buffer
  is not remediation.
* For removal, replacement and insertion, add the independently replayed
  source-prefix comparison alongside the existing entry reconstruction.
  A difference is a finding against the relation, environment or caller
  coverage, not an instruction to overwrite the expected state.
* Test lookup transport's **joint** representation/separation premises on
  the invocation whose fields are transported. Expose original lookup
  service/permission hypotheses and insertion's random coupling/return
  hypotheses rather than silently treating the checked entry as complete.
* Keep callback tests and partial mutation tests labeled at their actual
  scope. Keep the constructed sequence tests, but record captured caller
  hand-overs as outstanding until stage 5 supplies them.

Use the assessment's existing five workloads and relevant profiles first.
Add the smallest real workload for each missing path, such as rejected
lookup, collision/retry or lifetime change. A constructed NULL-owner or
wrong-kind test is useful but is not evidence of a real caller. If a
claimed path cannot be reached, report that rather than force registers
and call the resulting run natural.

**Exit:** every retained claim has either complete captured admission at
its declared scope or a clearly conditional/unresolved register entry.
Only fully admitted statements may acquire new proofs or composition.
This does not require solving every outstanding group before unrelated
work can proceed. It does prohibit advertising the entire current package
as remediated while those groups remain unresolved.

## 2. Recover a small archive toolkit

Recover from `archive/whole-driver-pilot-2026-11-12` by dependency, not by
merging the whole archive. Separate changes to image/layout generation,
capture/checker code, ISA semantics and proof statements. Reuse existing
tools and tests; avoid a new validation platform.

Confirm the exact ELF and decoded ranges against the live executed bytes,
including runtime-patched and initialization text. Run the clean-image
generators and relevant native/semantic instruction tests. Unsupported
instructions and fault forms must stop explicitly. A pin and a successful
Lean proof do not establish the decoder or ISA implementation's fidelity.

Provide a validation invocation that visibly fails when a required clause
is false, absent, unevaluated or based on missing capture bytes. Retain
diagnostic reporting that can continue after a failure, but never equate
its process exit with successful validation. Count expected invocations,
captured invocations, admitted invocations, failed clauses and scope exits
separately. A legitimate error-return case can pass its specified failure
contract; an exit from the claim cannot pass a requested success path.

Exercise a few targeted negative controls: omitted clause, changed return
byte, wrong identity, missing capture span and unexpected scope exit. Fix
the C1 comment-sensitive runner guard without adding a second token
scanner. No need to enumerate an adversarial matrix for every checker.

**Exit:** selected instruments identify the known C2 and socket-contract
failures as failures, and distinguish them from capture loss or image
mismatch. Recovering these instruments accepts no old whole-driver claim.

## 3. Repair the receive-window claim (C2)

C2 relates the binary receive-window update to the mirror's replay-window
decision. The arithmetic matched the fresh capture; the preserved-count
clause did not. We must decide what execution is represented before
editing that clause.

Run two explicitly separate experiments on the chosen image: sequential
stepping with interrupts deferred, and unforced ordinary scheduling.
Capture the entry and exit window, relevant registers, preempt count,
ownership/lifetime identity and the memory required by the proposed frame.
Measure intervening environment writes where ordinary scheduling requires
them. Missing frame coverage is unknown, not preservation.

The proposed structure is a local sequential instruction result plus an
explicit environment-transition relation for applying it to ordinary
executions. The local result may be recovered on its own when all its
predicates pass sequential captures. It must retain that scope. The
ordinary-execution result requires recorded, justified environment actions
and a checked interference condition; it is not obtained by allowing an
arbitrary changed preempt word or by ignoring changed memory. If the
required environment relation cannot be made executable and tested at
the intended boundary, stop that extension and present the scope/cost
choice before commissioning its proof.

Specify the changed bits/regions and why the rest are preserved from the
code and environment model, before the held-out run. The three observed
count deviations are regression cases, not a complete specification of
all allowed interference. Check duplicate rejection, window advancement,
boundary nonces and two visits in one keypair lifetime. Exercise an actual
retirement/reallocation boundary; a recycled address is a new identity.

**Exit:** the selected statement's complete conjunction passes captured
states; the required cases were actually reached; an independent reviewer
accepts its scope and its connection to the checker. Only then repair or
port the proof. Run the existing binary proof checks and applicable kernel
replay. A natural-scheduling result stays pending if only the sequential
claim has passed. Stage 5 cannot upgrade it by changing labels.

## 4. Repair service and source interfaces

This stage makes explicit what is being verified when instructions call
the allocator, random provider, socket code or other kernel services.

For each service needed by the next path, list observable entry and exit
state, permitted reads/writes, allocation identity changes, failure behavior
and ordering. Derive its permissions from pre-state ownership and the
callee's code; do not fit arenas or write sets to the observed result.
Run the executable instance at the fixed parameters on successful and
failing real calls. An untouched byte outside a partial snapshot is not
evidence for a universal memory frame.

**C1 allocator choice:** first prototype a deliberately scoped transition
interface for actual recorded allocation/free calls, rather than keeping
the existing assertion that the unsupported allocator body executes under
Kraken. This yields a conditional service-boundary result. A claim of
instruction-level allocator verification requires a separate implementation
and test of its needed semantics and a body proof; it is not implied by
the transition prototype. The stage must explicitly classify every service
as executed/proved or assumed under such a contract. Non-executable global
obligations remain exceptions needing resolution under stage 0.

For the pilot socket finding, review ownership of `sk_user_data` and the
callee's obligations together. A write-set edit must explain the ownership
transfer and show that the caller and later callee still satisfy their
conditions. Adding offset `0x268` alone is not a composition argument.
Similarly, open-side service access conditions must make their universal
claims meaningful on every admitted state, not just the observed calls.

**Source-model choice:** prefer calling the original operational mirror.
If the parameterized copy is necessary, supply a bridge for the actual
`Models.ofAnswers`/`Models.fed` interpretation, including returned state,
hidden input consumption, failures and branch order. First execute the
original mirror independently from the same recorded input stream and
check that its predictions justify those answers. Equality only at
`Models.mirror` is insufficient. Then prove the needed bridge after its
predicates have admitted captures. Do not infer its expected answers or
source state from the post-state being tested.

**Exit:** the next path has executable, admitted service instances and
an explicit list of remaining universal assumptions; its source relation
uses the intended mirror. Recover C1 algorithmic lemmas only under that
reviewed statement. A stub allocator returning NULL cannot meet a success
path's exit condition.

## 5. Verify a real joined sequence

The first sequence is two receive-window visits for the same live keypair,
including replay rejection. The second is a real allowed-IPs insertion
followed by lookup, then another insertion or deletion and lookup on the
retained heap. Exercise allocation failure/rollback and peer creation
between calls. These are separate claims, with separate service boundaries.

Capture the actual caller and intervening actions. Carry one allocation
identity map and independently replayed source state throughout. Evaluate
each entry, internal invariant, exit frame and next-entry predicate on
those states. Do not reinstall a convenient caller ABI, regenerate ghost
state from the next snapshot, reset the heap or silently insert a plan
transition. Record genuine caller transitions as part of the environment
and test them at their kernel source.

Before composing two theorem statements, run their predicates together
on the entire chosen sequence. On held-out executions vary peers, prefix
shape, successful/error outcomes and reuse where relevant. A statement's
required success continuation must occur at least once; a run that always
exits immediately cannot establish its usefulness. No percentage of
admitted prefixes substitutes for completion of the declared path.

**Exit:** the whole selected sequence passes without reconstruction of its
expected outcomes, and the exact hand-over obligations have real witnesses.
Only then prove the invariant and composition; use the existing proof
checks and review the resulting claim with all universal assumptions and
environment scope visible. Retain local partial results if this fails;
report the failed join rather than widening premises until it disappears.

## 6. Expand through a driver lifecycle

Choose one useful lifecycle: create device, configure a peer and routing,
open, handshake, receive authenticated data, then remove the peer and tear
down the device. Derive its actual order from the workload and the kernel;
the list is an intended workload, not an imposed dispatch schedule.
Include `wg_set_device`, real successful allocations, peer teardown and
the crypto/environment services needed by the path. The old no-peer or
immediate-failure witness does not cover this workload.

Add one missing entry or service boundary at a time, following stages 3–5:
executable statement, captured admission, independent review, then proof.
Test the same joint invariant at every reachable entry and hand-over, not
only global compatibility of independently inhabited predicates. Preserve
the distinction between actual supplied observations and predicted values.

**Exit:** the declared lifecycle completes within the claim, every required
predicate has been evaluated and passed, and the reviewed composition
states exactly the remaining external services and ISA assumptions.
Publish broader corpus coverage and its scope-exit denominator separately.
This slice does not become a whole-driver result merely by giving its
theorem that name. Expansion beyond it requires another concrete path.

## Execution, build and review discipline

This plan applies the current standing rules; it does not modify them.
Implementation would happen in task worktrees, with small separately
reviewable changes. Saved inputs are read-only, patched dependencies are
private, and no global state changes are part of this work. Main and remote
updates still need explicit signoff for the concrete changes.

For each work unit, name the exact claim, its fixed parameters and required
cases before running. Give an agent an initial two-hour investigation
budget and a stated suite/capture budget; report an unresolved design or
missing capture capability at that limit rather than commissioning more
proofs. Each selected workload gets a discovery execution and a fresh
held-out execution after the candidate statement is fixed. A held-out
failure invalidates that candidate; a redesigned statement needs another
fresh run. This is iteration after a substantive change, not a retry of a
failed model. Timing-dependent failures remain failures. An infrastructure
retry is allowed at most once and is reported separately.

During edits run the touched build and unit tests; run relevant differential
and capture suites when their implementation changes. At proof claim points
run `scripts/binary-proof-gate`, the selected image generators and the
kernel acceptance procedure in `binary/README.md`. On this box the user
must run the sandboxed external acceptance step outside nono; an internal
diagnostic is not that acceptance. At mirror/integration claim points run
the existing full differential/controls/sentinel requirements at their
documented strength. Do not make all archive suites per-edit blockers.
Runtime admission controls commissioning under the existing rule; other
checks keep their existing gate or speedbump status.

All heavy jobs use `capped` here after accounting for other account jobs.
Start with the assessment's successful caps (8–16 GiB for small suites,
32 GiB for the heavy full-buffer admission check); do not repeat the killed
full-buffer instruction replay unchanged. Stop and diagnose cap/time
failures. Do not raise Lean resource limits to conceal a bad decomposition.
Keep raw captures/logs in private temporary output, then remove them.
Commit the conclusion, exact scope and reproduction command, not a dump.

Before each proof or composition phase, an independent reviewer receives
the statement, checker, capture recipe, exact revision and setup. They may
challenge any premise, investigate other code or choose other workloads.
Do not give them a required verdict or previous findings as settled facts.
Disposition every finding individually: fix it, answer it with checkable
evidence, or present the unresolved decision to the user. Material statement
changes go back through captured admission and review; a review of an
earlier revision does not approve the changed claim.

## First implementation batch, if this plan is adopted

1. Update the existing claim register and select the first complete current
   lookup claim, with its missing service/transport obligations explicit.
2. Make its full-buffer admission and return checks work on one unchanged
   capture within a measured resource budget; investigate the source-prefix
   mismatch in one mutator as a separate finding.
3. Recover the smallest clean-image C2 capture/checker subset and make its
   exact count/frame failures visible. Test the two scheduling scopes and
   return with a concrete environment/frame proposal.

That batch produces repaired evidence and a reviewable next statement. It
does not authorize a broad archive merge or begin a whole-driver proof.
