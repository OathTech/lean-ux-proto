# Fresh-eyes review: does this work lead to verified Linux code?

2026-10-20. Independent directional assessment, written on
`task/fresh-eyes-scope`. Recommendations are the reviewer's proposals
[AGENT], not adopted project decisions. The assignment is to assess the
mirror and proof campaigns against the objective of formally verifying real
Linux code [USER 2026-10-20]. Binary experiments are outside this assessment
apart from acknowledging that they are attempts to close an important gap.

**Verdict: retain the assets, change the next milestone.** This is a serious
executable modeling and model-verification project. It has useful properties,
unusually explicit limitations, and evidence that proofs expose modeling
defects. I would not cancel it on those merits. I would stop commissioning
open-ended mirror expansion and further broad proof campaigns until one
bounded result connects actual Linux code, an explicit execution contract,
and a useful property. More mirror theorems do not, by themselves, make that
connection more likely.

The main risk is successful execution of the wrong intermediate objective:
an increasingly comprehensive, carefully verified model whose correspondence
to Linux still depends on testing and human inspection. The documentation
acknowledges that boundary. Acknowledgment is necessary; it is not a plan for
crossing it. The question is now whether to make that boundary the organizing
problem of the next phase.

**What I inspected.** The fixed main baseline is `218d3ffd`; campaign 1's
branch was `8ba82097`, campaign 2's `fe20c87a`, and campaign 3's `7b8994b1`.
The latter is based on the fixed-width mirror `1f766662`, before the namespace
landing. I read the goals, charters, correspondence description and current
register, sampled the mirror and proof definitions behind lifetime safety,
nonce safety, confirmation, conservation and progress, and examined the
scheduler, domain filter and kernel-findings tray. I also read the unmerged
protocol-bridge proposal at `b6bd7854`. This is not an exhaustive proof audit,
a campaign acceptance review, or a binary-track verdict.

Branch-specific references below mean those exact commits, obtainable with
`git show <commit>:<path>`. Links to files present on this review branch refer
to its `218d3ffd` baseline. In-flight changes after these pins are not assessed.
In particular, the namespace carry is unfinished at the inspected campaign-2
head: its report records scoped successes but a **failed aggregate proof
gate**, blocked by shared layers. Campaign 3 reports aggregate validation over
`1f766662` and explicitly lags `218d3ffd`. Main's opening register paragraph
has not yet caught up with the namespace landing. I do not treat any of those
as a current, whole-project proof pass.

**What deserves preservation.** The mirror follows concrete control flow;
hidden-input recording is substantially stronger evidence than matching return
values; unsupported paths stop visibly; proof-side observers have exact erasure
theorems; many results now reach initialized runners and retain failed prefixes;
counterexamples are distinguished from Linux bugs. Campaign 2's queue-refill
and namespace-lifetime findings are concrete returns on the proof investment
([requests](2026-10-14-campaign-2-mirror-requests.md),
[namespace finding](2026-10-20-proof-campaign-2-namespace-pin.md)). None of the
recommendations below requires weakening the kernel checker, pretending a
counterexample is a success, or changing the mirror to make a false property
true.

| Priority | Finding | Next action with the best return |
| --- | --- | --- |
| 1 | The proof campaigns do not own the implementation-to-property connection. | Choose one actual Linux body and one caller boundary; make their composed property the next funded milestone. |
| 1 | The accepted replay domain is not yet an independently specified set of Linux executions. | State admission conditions independently of replay success; audit one omitted interference point. |
| 1 | Lifetime safety of resolved events does not establish absence of invalid dereferences. | State and test the missing fault-exclusion obligation before extending R2. |
| 2 | Event coverage and explicit proof parameters remain separate from a green axiom check. | Close one representative observation boundary and instantiate one terminal theorem's operational premises. |
| 2 | Several security labels stop short of the cryptographic or resource property motivating them. | Choose an explicit threat model and name the bridge obligations, especially key-material uniqueness. |
| 2 | Proof maintenance is becoming a project of its own. | Freeze a research baseline and benchmark a small compositional proof interface before another campaign. |

**1. The missing connection should determine the work order.**

The standing rules still exclude C-to-mirror simulation from the campaigns,
pending a separate user decision. That is a coherent division of labor for an
individual campaign. It is a dangerous indefinite division for the overall
objective: the same boundary can remain out of scope for every successful
piece of work. The binary efforts recognize this problem; I have not assessed
whether they solve it, and their eventual success should not be a premise of
this review's recommendation.

The needed statement is approximately:

> Every execution of the selected Linux component admitted by an independently
> stated entry and interference contract is represented by a mirror execution
> whose proved property transfers to the concrete observations.

For safety, this must cover concrete behaviors in the required direction.
Finding a mirror execution that matches each tested Linux trace is valuable
evidence, but neither covers all admitted executions nor establishes memory
safety of the C. Conversely, proving a property of all model executions is
insufficient when relevant concrete executions have no model execution.

The [simulation-target review](2026-10-12-simulation-target-review.md) already
identifies representation, ownership, service and interference obligations.
The important new circumstance is the size of the investment now resting on
their future discharge. The [working rules](../AGENTS.md) describe a later
simulation as straightforward; that should remain a hypothesis until tested
on an actual component with its real calling conditions.

My preferred experiment is the existing receive-counter result. Start from
Linux's `counter_validate` and
[`counterValidate`](../Leanux/WG/RxData.lean), reuse the window property's
independent mathematical model, and prove the body over the actual bitmap
representation and C arithmetic under a named synchronization contract. Then
justify that contract at one real receive caller, including the keypair's
lifetime. The first part tests the language/representation bridge; the second
tests whether that bridge composes with kernel context. Neither requires
verifying all of WireGuard or building a general C memory model into the
operational mirror.

This is a candidate, not a prejudgment of the proof engine. Another existing
property is preferable if it exercises the same obligations more cheaply.
Do not substitute a rewritten stand-alone implementation and call the Linux
component verified. Pin the actual source and configuration, identify trusted
frontend/compiler steps, state helper contracts, and keep any synchronization
assumptions visible. A function-body theorem conditional on a lock contract is
a legitimate first result; it should not be presented as the second result.

**Recommendation:** authorize a bounded feasibility phase rather than another
property catalogue. Its outputs are the composed theorem or a precise account
of the first unsupported semantic feature and the cost of addressing it. If a
usable proof host does not exist yet, the critical path is proof-host work.
Continuing to expand the model cannot substitute for that work.

**2. Test-domain closure and execution-domain closure are different problems.**

The [correspondence description](../correspondence/README.md) is candid:
generated inputs are filtered through the mirror, instrumentation observes only
part of execution, and some scheduling choices are reconstructed. In
[`evaluator/check.py`](../evaluator/check.py), `domain_filter` runs the model
before Linux, and `select_in_domain` selects accepted candidates and reports
rejection counts. Invariant failures abort; they are not silently filtered.
That is good diagnostic behavior. Reporting the selection bias does not remove
it as a limitation of the evidence.

A concrete example is the namespace-pin fix at `218d3ffd`. It repairs the
teardown guard and deliberately reserves fixture descriptors, excluding the
aliasing input that exposed the defect. The decision is recorded and reasonable
for this fixture. It does **not** establish the behavior of arbitrary descriptor
aliases retaining a namespace. Similarly, the end-of-operation pending-work
guard makes an accepted operation satisfy a completion condition by refusing
other cases; it does not establish that Linux always reaches that condition.
These are scoped repairs, not concealed failures. They illustrate why a future
verification claim must not define its admissible domain as whatever replay
currently accepts.

The scheduling boundary is especially consequential.
[`Env/Batch.lean`](../Leanux/Env/Batch.lean) rejects several peers' NAPI polls
in one softirq, tries suspended activations on copied state to identify a
consistent resumption, and accepts one of specified NAPI placements.
`napiIrqExit` explicitly describes selecting a placement using comparison
evidence. This need not make the test vacuous: it still requires an entire
candidate execution to agree. It does mean that schedule reconstruction is
part of the trusted explanation of agreement, not simply an input stream
independent of the thing being checked.

One CPU and `PREEMPT_NONE` do not remove interrupt/softirq interference. The
project itself has a particularly useful boundary case:
[tray 04](upstream-tray/04-staged-packets-stranded-by-racing-flush.md) describes
a possible interleaving between a process-context staged-send caller and
receive-side confirmation. The report says the fixture does not produce that
interleaving even on one CPU. It is an unconfirmed design question, with no
corpus reproducer; I am not upgrading it to a kernel bug. It nevertheless shows
that the scope restriction is stronger than the hardware configuration.

For a replay laboratory, supporting observed schedules incrementally is
sensible. For a safety proof over Linux, each omitted interference point needs
either exclusion by the concrete entry contract or an argument that moving it
to a represented point preserves the property. Adding more scheduling traces
does not establish that argument.

**Recommendation:** keep deterministic replay as a test adapter, but make the
next component proof use an independently defined environment contract. Start
with one ownership/interference case, not a full SMP model. Identify where
interrupts, BH re-enablement, sleeping allocation, RCU and callbacks can affect
the chosen component. Prove the needed local noninterference or retain an
explicit conditional claim. For testing, spend a small fixed sample on
independently chosen Linux inputs and classify unsupported cases as scope
findings instead of replacing them with accepted candidates. This is a cheap
review-time experiment, not a new acceptance gate or a demand to support every
rejected input.

**3. The lifetime result's failure boundary is weaker than the natural reading
of “lifetime safety.”**

This is a concrete statement-scope issue, not a claim of an unsound Lean proof.
[`LifetimeSafety/Statements.lean`](../Leanux/Proofs/WG/LifetimeSafety/Statements.lean)
exports `runner_initialized_access_safety`: committed reads and writes do not
resolve an identity released earlier. The register accurately uses that
wording. But the motivating implementation concern is also whether code ever
*attempts* to dereference a dead object.

In [`State.lean`](../Leanux/WG/State.lean), a missing peer causes an invariant
Stop. In [`Peers/Access.lean`](../Leanux/Proofs/WG/Peers/Access.lean),
`getPeerPrefix` records a read only when the original getter succeeds. Its
error branch preserves the history unchanged. In
[`Lifetimes/Events.lean`](../Leanux/Proofs/WG/Lifetimes/Events.lean), `Safe`
constrains pairs of emitted release/access events. Thus a failed getter can
coexist with a safe recorded history. Retaining earlier observations through a
Stop does not turn the failed attempt into an access event.

I checked this with the existing compiled campaign-3 dependencies. A local
empty peer store, a history containing one release, and `getPeerPrefix 42`
produce the invariant error `dangling peer 42` while leaving that safe history
unchanged. The probe also proved the general error-branch equation using only
standard Lean axioms. **This is not an initialized Runner counterexample.** It
demonstrates a logical limitation of the stated conclusion; it does not show
that a supported kernel or initialized mirror execution reaches this state.

For real memory safety, two additional distinctions matter. Allocation stamps
prevent confusing logical object generations, but a C pointer is not a checked
lookup carrying that stamp. A proof needs the relation between live allocations,
possibly reused addresses, and outstanding references. Likewise,
[`Keypair.lean`](../Leanux/WG/Keypair.lean) erases the object at its last modeled
reference and labels `call_rcu` as a cut; a C lifetime argument must account
for readers and deferred reclamation at that cut. Abstract identities are a
good representation choice. They move these obligations into the relation;
they do not discharge them.

**Recommendation:** before expanding R2, add a small, explicit goal excluding
the relevant invariant-fault outcomes for a named independently admissible
class of executions. Alternatively observe attempted accesses, including
failure, and prove every such attempt valid. Do not demand that malformed
records or intentionally unsupported inputs succeed. Keep lookup-history
safety, no invalid dereference, reference accounting, and eventual reclamation
as distinct claims. This would produce more useful assurance than another
large collection of successful-access preservation lemmas.

**4. The proof's observations and premises are themselves a specification
boundary.**

The proof-side observer approach has a real strength: exact erasure prevents
instrumentation from changing the executable result. It also has a limitation:
erasure alone does not show that the log records every relevant event. A
wrapper that runs the original function and emits no events would erase
perfectly. A universal property of that empty log would say nothing about
the function's accesses or sends.

This project has done considerably more than erasure: initialized journals,
source factors and local observation equations connect many concrete actions.
Campaign 3's T2 has substantial native-source coverage work. Its final theorem
at `7b8994b1`, `initialized_transmit_source_conservation`, takes a
`NativeAccounting.SourcePoint` premise. Its companion
`transmit_source_children_are_closed` proves independence from the former five
extension parameters. These are useful results. The equation eliminating
parameters is not, on its own, a proof that every semantic event is represented
by the independently defined source relation. The source wiring and that
relation's meaning still need assessment. The registers already distinguish
kernel-proved event properties from reviewed observer coverage for R2–R4 and
campaign 2; that distinction should survive every headline summary.

There is another boundary that axiom checking cannot detect. At the same C3
pin, `HandshakeSecurity.initialized_responder_confirmation_discipline` still
takes `PendingPromotion.H1DriverFrames` and `H1ResponderCurrentEdges` as
arguments. `ResponderH1.lean` explicitly calls the latter required local source
projections, not imported campaign-2 theorems. Its fields constrain session
installation, confirmation and clearing. These premises are disclosed and may
be entirely reasonable; I found no reason here to call them false. Nevertheless,
a theorem `P → Q` can have no nonstandard axioms while `P` remains an undischarged
obligation about the implementation.

**Recommendation:** select one terminal security result and publish its short
end-to-end dependency chain: concrete events covered, initialized invariant,
operational premises with their actual instantiations, and remaining environment
assumptions. For T5, an unconditional application using proved C2 packages is a
better milestone than another conditional preservation theorem. For observers,
test the proposed architecture by intentionally removing one security-relevant
event and seeing exactly which claimed connection fails. Use a one-off
experiment; do not build another general audit framework.

A longer-term possibility is a small shared operational/event interface at
primitive access and effect boundaries, with one adequacy argument reused by
several properties. Evaluate it on one result. A wholesale replacement of the
mirror with a verification language is not justified by this review.

**5. Choose the security claim before filling the security catalogue.**

The campaigns prove valuable implementation discipline. They do not yet state
a threat model that turns the collection into a VPN security argument. That is
not a reason to prove all of cryptography here. It is a reason to identify
which security theorem the implementation facts are intended to support.

The nonce result gives a precise example. At `7b8994b1`,
`HandshakeSecurity/InitializedEncryptionMaterial.lean` defines the uniqueness
token as `(keypair.internalId, packet.nonce)`;
`EncryptionNonceEncoding.lean` uses the same allocation identity with the
serialized nonce. `initialized_nonce_safety` proves those tokens unique and
connects them to actual encryption receipts. This is strong per-allocation
counter discipline. The cryptographic requirement concerns actual
**key material and nonce**. Distinct allocation identities do not, as a matter
of logic, imply distinct key bytes. Relating session derivation, repeated
random draws, resets and compromise to key-material uniqueness is a separate
protocol/probabilistic obligation. I did not construct a reachable key-reuse
attack and am not asserting one.

Similarly, AEAD acceptance is a functional predicate in
[`NoiseCrypto.lean`](../Leanux/WG/NoiseCrypto.lean), not by itself a theorem
about which adversary could have generated a message. Local cookie behavior
and a small reply/input size ratio do not imply a CPU or memory bound under
hostile load. Pending-packet conservation does not imply delivery. These are
reasonable scoped results, but the reasons for prioritizing them often invoke
stronger consequences than the theorems establish.

The proposed protocol bridge, `docs/2026-10-19-plan-protocol-bridge.md`, exists
only on `b6bd7854` at this review's baseline; read it with `git show` rather
than expecting that file on this branch. It recognizes much of this gap.
I support an explicit bridge obligation, but would not launch a large
transcription/re-proof of protocol semantics in parallel with an unresolved
Linux bridge. Published protocol work is already substantial: the
[CryptoVerif authors' result](https://bblanche.gitlabpages.inria.fr/publications/LippBlanchetBhargavanEuroSP19.html)
covers WireGuard's protocol including transport, with secrecy and authentication
properties. A separate
[implementation-verification paper](https://arxiv.org/abs/2212.04171) connects
Tamarin models to separation-logic I/O specifications and verifies a substantial
part of the Go WireGuard key exchange. That is precedent for a compositional
connection, not verification of Linux or evidence that a Lean transcription
would be cheap.

**Recommendation:** pick one threat model and one target claim. Name the
adversary's packet, configuration, clock and compromise powers; identify the
crypto and randomness assumptions; determine which campaign results actually
discharge its premises. Treat per-allocation nonce safety as exactly that
until the key-material bridge is supplied. If the immediate goal is instead
implementation memory safety or routing correctness, say so and defer the
protocol bridge. Both are legitimate contributions to verified Linux.

**6. Proof maintenance is already large enough to influence architecture.**

A source census, including comments and blank lines, gives:

| Revision | Executable `Leanux` files / lines | Proof `Leanux` files / lines |
| --- | ---: | ---: |
| Main `218d3ffd` | 64 / 25,948 | 3,129 / 399,580 |
| Campaign 3 `7b8994b1` | 64 / 25,894 | 6,674 / 716,551 |

These counts exclude `binary/`; the proof count includes `Leanux/Proofs.lean`.
The main-to-C3 branch delta contains 316,966 added proof lines in 3,545 files.
This is a scale indicator, not a measurement of labor, duplication, proof
quality or economic cost. A large proof can be appropriate for a small program.

The more diagnostic evidence is maintenance coupling. Campaign 2's report at
`fe20c87a` identifies fourteen runner-guard copies in seven shared modules after
the namespace change and records the resulting aggregate build failure.
[`docs/proofs.md`](proofs.md) describes extensive observer, frame, source and
runner layers. C3's source-closure history repeatedly adds modules to carry a
property through another part of the same driver. Much of this is doing real
work, but it resembles repeatedly constructing an instrumented semantics for
each property, not merely stating independent invariants over one reusable
semantics.

Two project choices amplify that cost: whole initialized-runner claims pull in
large environment and unrelated-subsystem paths, and the mirror is protected
from proof-motivated restructuring while proofs must follow moving source.
The state split has already improved the situation, so this is not a request
to rediscover that split. The remaining issue is how many proof-side copies
of control flow a small legitimate mirror change must repair.

**Recommendation:** distinguish a useful public property from all historical
intermediate exports, and avoid making preservation of every intermediate
theorem an indefinite compatibility promise. Keep a pinned research baseline
for the implementation-bridge experiment; allow main to evolve with honest lag
reporting. Benchmark one shared observation/effect interface on a representative
property and one real source change. Measure repair effort and review surface,
not theorem count.

I would also propose a narrow revision to the blanket ban on proof-shaped
restructuring: allow an independently reviewed, semantics-preserving factoring
when it keeps C data/control correspondence and demonstrably reduces proof
duplication. This is a **proposal to the user**, not a rule change made here.
It must never allow a behavior change justified only by a desired theorem.
First try the experiment entirely in the proof tree; change standing practice
only if the evidence warrants it. A global effect framework or another gate
would be a poor first response.

**What I would fund next, and what I would defer.**

The effort estimates below are proposed investigation budgets, not estimates
of how long the full verification will take.

| Work | Suggested budget | Payoff / stopping condition |
| --- | --- | --- |
| Define one end-to-end component claim and its independent admission contract. | 1–2 focused days | Very high return. Exposes whether the missing item is a theorem, an environmental assumption, or unavailable semantics. Stop expanding scope once the claim is concrete. |
| Test actual Linux-to-property feasibility on the chosen body and one caller boundary. | First two-week investigation, then explicit reassessment | Highest strategic return. Produce a checked component result or a sharply located blocker. Do not silently replace the target with an easier rewritten program. |
| Resolve one statement gap: invalid-access exclusion or unconditional T5 premises. | A few focused days to scope and attempt it | High return. Establish what stronger claim costs; if blocked, report that rather than multiplying weaker exports. |
| Pilot a shared observer/contract interface and carry one source change. | At most one week initially | Potentially high return, uncertain implementation cost. Continue only if it reduces both proof duplication and review burden. |
| Probe one omitted UP interference case and a small independently selected input sample. | A few days | High information value about the domain; no promise of finding a Linux bug. Report rather than broaden into an SMP implementation campaign. |
| Add unrelated subsystem mirrors, a fourth broad property campaign, or a new protocol-proof framework. | Defer | Low near-term return against the missing implementation connection. Resume only for a named dependency of the selected claim. |

This does not mean throwing away completed campaigns or suspending necessary
repairs to preserve them. It means giving the next substantial investment a
different success criterion. A small conditional theorem about actual Linux
with an explicit, checked path toward discharging its conditions would advance
the stated goal more directly than another exhaustive layer over the same
unproved boundary.

**Pivots and cancellation.** Three outcomes would all be intellectually honest:

- Continue as a Linux-verification project with a much narrower component
  target and implementation correspondence on the critical path. This is my
  preferred direction.
- If that connection is not presently tractable, retain the mirror as an
  executable specification and differential bug-finding laboratory. Evaluate
  it by independent defect discovery, coverage of useful configurations and
  maintainability. Keep proofs that materially help those outcomes; do not
  describe this as having verified the Linux implementation.
- Stop the project as a route to formal Linux verification if successive
  bounded attempts cannot produce a credible implementation bridge and there
  is no separately valued testing/specification use. Preserve a reproducible
  research snapshot and the conclusions. Sunk proof volume is not a reason
  to continue an unproductive direction.

I do not recommend immediate cancellation: the mirror defects found by the
campaigns and the detailed operational models are evidence of value. Nor do
I recommend declaring Linux verification complete once the current campaigns
land. The next decision should turn on whether the missing connection is
becoming cheaper and more concrete.

**Evidence and reproduction limits.** This review makes source-level and
logical-scope findings, not a new Linux vulnerability claim. No QEMU run, new
oracle build, full differential suite or full proof gate was performed for
this review. Historical pass/failure counts above are attributed to their
pinned reports, not rerun results. The small lifetime probe was elaborated
against the clean detached `review-c3-copy` build at `7b8994b1`; its relevant
`State`, `Peers/Access` and `Lifetimes/Events` sources match `218d3ffd`.
The temporary probe is not retained as another proof result.

To reproduce its essential check in a temporary
`Leanux/Proofs/FreshEyesProbe.lean` after building the proof dependencies:

```lean
import Leanux.Proofs.WG.Peers.Access
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Peers
open Leanux.Proofs.WG.Lifetimes

example (pid : PeerId) (w : WGWorld) (a : Ambient)
    (h : List PeerEvent) (e : Stop)
    (failed : ((getPeer pid).run w).run a = .error e) :
    runStatePrefix (getPeerPrefix pid) w a h = (.error e, h) := by
  rw [getPeerPrefix_run, failed]

example : AccessEvent.Safe ([.release 42 7] : List PeerEvent) := by
  simp [AccessEvent.Safe]

#eval match runStatePrefix (getPeerPrefix 42)
    ({ dev := some { ifindex := 3, ifname := "wg0" } } : WGWorld)
    ({ env := fun _ _ => true, timing := ⟨0, 0⟩ } : Ambient)
    ([.release 42 7] : List PeerEvent) with
  | (.error (.invariant message), events) =>
    (message, events == ([.release 42 7] : List PeerEvent))
  | _ => panic! "expected the missing-peer invariant failure"
```

Run it through `capped -- scripts/in-bundle lake env lean
Leanux/Proofs/FreshEyesProbe.lean`, then remove that temporary file.
The observed output is the dangling-peer invariant message and `true` for
unchanged history. The two named lemmas in the original probe passed axiom
inspection with only standard axioms; the exact snippet above also elaborated
successfully. There is no accepted initialized execution or Linux capture in
this experiment.

The size census is reproducible from `git ls-tree -r --name-only <revision>
Leanux`, retaining `.lean` files and counting newline characters in each
`git show <revision>:<path>` blob. Classify `Leanux/Proofs/` and
`Leanux/Proofs.lean` as proof code, all other retained files as executable.
The branch delta is `git diff --shortstat 218d3ffd...7b8994b1 -- Leanux/Proofs`.
