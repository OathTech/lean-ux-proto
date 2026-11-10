# The binary track: reassessment with the current agents

2026-11-10. Independent strategic and technical assessment, written on
`task/binary-reassessment` for the owner. Commissioned after the track had
been idle since 22 October, with the question of what the more capable
agents now available change and whether there is a way forward at reasonable
cost [USER 2026-11-10, paraphrased]. Everything recommended here is a
proposal [AGENT]; nothing is an adopted decision. The branch holds this
document and its index row only. The trial proofs it reports are not
committed; where they are and how to rerun them is in
[Reproduction](#reproduction).

## Conclusion

**Continue, on a different basis. The work did not stall on proof cost, and
proof cost is now small enough to stop steering by it.**

1. *The stall was a decision taken on a metric, not a wall.* In October the
   agents were proving at a recorded 18 to 25 anchored instructions per
   elapsed hour and committing checked Lean at about two thousand lines an
   hour. The allowed-IPs insertion is 506 instructions. Its calibration
   counted completed functions at four hours and at eight and a half; at the
   recorded rate that count could not have been anything but zero. What
   followed was two re-proof experiments on 21 October (typed heap view,
   machine-state views), nineteen idle days, and the external-tooling probe
   of 9 and 10 November. All three measured proof size on code that was
   already proved and found no saving, because proof size was not located
   where they looked.
2. *With the current agents the open pieces close in minutes.* Five timed
   trials by worker agents on the landed package, each with a budget set in
   advance:
   - an unproved 22-instruction heap-storing segment: 7 minutes;
   - the reconstruction, mirror link and structural check for the
     insertion's open "covering" case: 13 minutes;
   - a target the track had never touched, the replay-window code inlined in
     the receive path (67 instructions), from the ELF to a tested statement,
     a checked theorem up to its test-and-set instruction and a link to the
     mirror function: 50 minutes;
   - the first complete entry-to-return path of the stalled insertion, with
     an explicit allocator contract and its three failure exits: 49 minutes;
   - the insertion's hardest path, the intermediate node, where two fresh
     objects are live at once and an existing subtree is re-parented: its
     reconstruction, mirror link and structural check for both sub-cases,
     and the machine code from the connection stores to the return, in 55
     minutes of a 75-minute budget. The 45 instructions that initialize the
     internal node, and the composition from the function's entry, were not
     reached.

   I recompiled every result and read every final statement. They are
   trials: none has had an independent review, and each has limits listed in
   section 3.
3. *What limits the track is what the owner has to read and what the claim
   means.* The printed trust surface went from 750 lines to 4,713 while the
   proved share of the anchored WireGuard instructions reached 4%. The
   theorems are about Kraken's sequential stepping of literal instruction
   terms: no interrupt, no second CPU, no account of runtime text patching;
   and the image is the KCOV-instrumented oracle build, in which one
   instruction in seven is a coverage call. WireGuard's text calls about 139
   distinct kernel functions outside itself; a result over all of it would
   rest on that many machine-level contracts. None of this changes with a
   better prover.
4. *So the thing to manage is review attention, not agent hours.* I
   recommend two bounded results, statement first, each with a surface the
   owner can read in one sitting: complete the allowed-IPs insertion (the
   October charter's checkpoint A) to one reviewed headline; and take the
   receive replay window from the compiled code to the landed anti-replay
   theorem, which is a result of the kind the 20 October success criterion
   asked for and which nothing since has attempted. Stop the proof-size and
   tooling experiments. Do not resume breadth (adequacy of the whole mirror)
   until those two show what a completed function costs in printed surface.

"Stop" is a defensible answer on one ground only: that a claim about a
sequential model of an instrumented build is not worth the owner's reading
time at any price. The evidence does not force that, and the price has
fallen far enough that I would not stop before the two results above exist.

The decision points are in
[Recommendation](#recommendation-and-decision-points).

## 1. What the binary track established

My reading of the statements in `binary/` at main `d741a764` (its Lean
modules are unchanged since the landing at `e8b16952`), not of the reports.

**Size.** 944 Lean modules, 105,059 lines, about 4,000 theorems; 15 modules
are generated image terms. 88 modules raise `maxHeartbeats` or
`maxRecDepth`, all but four of them for the whole file. That is a finding
under the box rule that a raise is scoped to one declaration with its
reason; none of the trials below needed a raise.

**Complete function theorems** (machine execution from the function's entry
to its `ret`, against an accepted run of the mirror function):

| Compiled function | Instructions | Theorem |
| --- | ---: | --- |
| `wg_index_hashtable_lookup` with `wg_peer_get_maybe_zero` | 62 + 76 | `LookupRelation.lookup_simulation` (milestone 1), `Pair.IndexLookup.lookup_checked` |
| `wg_index_hashtable_remove`, `_replace`, `_insert` | 25, 41, 109 | `Pair.Remove.remove_checked`, `Pair.Replace.replace_checked`, `Pair.Insert.insert_checked` |
| Arbitrary finite sequences of those four over one retained heap | | `Pair.Sequence.sequence_checked`, `Pair.InsertSequence.sequence_checked` |
| allowed-IPs `lookup` with `common_bits` | 103 + 73 | `Pair.Trie.lookup_checked`, `Pair.Allowedips.lookup_checked` |
| KCOV callbacks (`trace_pc`, `cmp4`, `const_cmp4`, `const_cmp1`) and `__local_bh_enable_ip` | | `Callback.*_contract`, proved from the image |

That is 489 of the 12,340 anchored WireGuard instructions counted by the
scoping census ([scoping report](2026-10-15-binary-tv-scoping.md), per-function
table): 4.0%. The allowed-IPs insertion (`add.isra.0`, 506 instructions) has
component theorems only, each from a named internal cut
([closing record](2026-10-20-binary-allowedips.md)).

**The shape of a headline.** For every `fetch` that extends the literal image
terms, every machine state and mirror world satisfying a precondition, and
every accepted run of the mirror function from that world, the machine
eventually reaches a state satisfying a postcondition: returned to the
caller, memory related to the mirror's final state, frame outside a stated
footprint. The paired results state the precondition as an executable check
returning `ok` (`Pre := callBoundary ... = .ok ()`) and the relation as an
executable decoder: `Corresponds names o m d` is
`reconstruct names o m = .ok (target d)`, where `names` maps mirror
identities to addresses. This is a reasonable design; it is what lets the
same definitions be run on captured kernel states before they are proved.

**What the headlines assume**, in decreasing order of how much rests on them:

- *The semantics is sequential.* `Binary.instructionStep` steps Kraken's
  interpreter. There is no interrupt, preemption or other CPU in it.
  `SerializedEnvironment onlineCPUs externalActions` is two equations
  (`onlineCPUs = 1`, `externalActions = []`) over variables that occur
  nowhere in the step relation: it records the intent and constrains
  nothing. The honest reading of every theorem is "under Kraken's
  sequential execution of this code".
- *The instructions are the literal terms.* `AnchoredDecoderAgreement fetch`
  and its siblings say `fetch` returns the committed decoded instructions.
  That these are what the CPU executes rests on objdump, on a byte
  comparison with the saved ELF run as a test, and on the kernel not having
  patched that text at boot or run time (alternatives, static keys). The
  scoping report raised the last point; I found no record that it was
  settled for the proved ranges.
- *Kraken with nine local patches* is the meaning of each instruction. Six
  of the patches add semantics (memory cmpxchg, BSR, PUSHF and the interrupt
  flag, STOS, MOVS and memory XADD, register BT); each is tested, none is
  proved against anything.
- *The precondition is satisfiable and realistic.* Theorem witnesses exist
  for the hit paths of the first lookup and for the paired functions'
  concrete states; captured kernel states were replayed as tests. General
  reachability from a kernel entry is unproved (landing obligation F7).
- *External services.* The random provider behind index insertion is a
  hypothesis (about 1,267 instructions unproved); allocator, free and RCU
  have no contract yet; the first lookup's headline still takes the callback
  contracts as hypotheses although a later sibling proves them.

**Transport.** The objective had two halves: adequacy, and transport of the
mirror's proved properties to the binary. The second half is
`lookup_transport` (any predicate of an accepted mirror lookup run) and
`lookup_snapshot_transport` (the replay-state frame through lookup, with
representation and separation as extra premises). No property from the three
proof campaigns has been carried to machine code for any function that
changes state.

**Open at landing** and still open: the list in
[the landing assessment](2026-10-19-binary-landing-assessment.md#outstanding-review-obligations-at-landing)
(F1 NULL-owner witness, F2 callback hypotheses in the original headline, F6
transport premises, F7 entry realism, F9 scaling), and for the insertion:
entry establishment, allocator contracts, the covering and intermediate
cases, failure and rollback, composition, the link to a complete run of
`Leanux.WG.add`, external acceptance of the last export.

**What it found.** Two mirror defects (the index lookup's dead-peer store;
the allowed-IPs sequence counter held as an unbounded number where the C
has a `u64`), both fixed on the mirror lane. No kernel finding.

## 2. Why it stalled

| Candidate cause | Finding | Evidence |
| --- | --- | --- |
| Instruction stepping | Not a bottleneck, then or now | October recorded region execution as routine. Trial T1: no failed cycle on memory frames or mapping, 7 minutes for 22 instructions. The [Ascent probe](2026-11-10-ascent-probe.md) found the same by two methods. |
| Heap representation and framing | A real but modest cost; restructuring it bought nothing | The typed heap view re-proved the placement loop at the same type with 12% more attributed lines; the machine-state view took the entry proof's handwritten dependencies from 925 to 1,339 lines (`docs/2026-10-21-binary-heap-view.md`, `docs/2026-10-21-machine-state-views.md`, both on the unlanded `task/binary-heap-view`). |
| Reconstruction after mutation: allocation identity, fresh-record decoding, structural invariants | Intrinsic to relating a pointer structure to an identity-keyed store, and the largest per-case volume; but it is per mutation shape, not per instruction, and a further shape is cheap | October's child-attachment case: four commits between 08:08 and 09:10 UTC on 20 October, 3,617 added lines (`ff877b1a` to `2f1b3bf0`), machine regions included. Trials T2 and T5 did the next two shapes by reusing those lemmas. About 60% of T2's lines were the structural check. |
| The form of the structural invariant | Partly an artefact | `heap` is an executable nested loop with accumulators. Each mutation shape re-proves its layers, because the landed lemmas are stated at the shape of the case that needed them (T2 worker's report; I checked the duplicated lemma families exist). A state "nodes mapped by `f`, one node appended" with lemmas parametric in `f` would remove about half. |
| Statement design: one tested boundary assertion and one printed statement per internal cut | An artefact of the method, and the main driver of review cost | Printed surface (`binary/TrustSurface.expected.txt`): 750 lines at milestone 1 (`686bba49`), 2,576 at the first landing, 4,713 after the insertion increment, which completed no function. |
| The target image | An artefact of the choice of target | The image is the mirror's KCOV-instrumented oracle. In WireGuard's text 2,090 of about 14,200 instructions are transfers to coverage callbacks (my count, below). Most of `TrustBase.lean` is KCOV layout, readiness and separation. |
| Entry and environment realism | Intrinsic; untouched; unaffected by prover capability | Section 1. WireGuard's text has 588 call sites to about 139 distinct kernel functions outside itself (my count). |
| The calibration metric | An artefact, and the proximate cause | The charter counted completed functions at four hours. The recorded rates on the index family were 18.5 and about 25 anchored instructions per elapsed hour ([index subsystem](2026-10-18-paired-index-subsystem.md), [index insertion](2026-10-18-paired-index-insertion.md)); 506 instructions at that rate is twenty hours or more. At eight and a half hours the increment had component theorems for placement, exact reassignment, the empty-root tail, initialization, child attachment and the returns. |
| Direction after the stall | An artefact | The success criterion adopted on 20 October was one bounded result joining actual Linux code, an explicit contract and a useful property; the decision named the typed heap view's lookup calibration as that experiment ([decisions](decisions.md), 2026-10-20). What ran was a re-proof of proved code under a new memory interface (the lookup re-proof itself was deferred), then a second such re-proof, then a proposal for a third, then the external-tooling probe. Each measured proof size or authoring effort at the level of instruction segments; none could have produced a result of the criterion's kind. |
| Capability of the agents | Not the cause | The October agents built the whole framework, found two mirror defects with it and wrote dense, correct Lean quickly. The trials below are faster by a small factor on like-for-like steps, not by orders of magnitude. |

My attribution, then: the costs intrinsic to the problem are the
reconstruction of linked structures after mutation (bounded, per data
structure) and the environment (unbounded, and the real limit of the claim).
Everything else that made the track look stuck was a consequence of how the
work was measured, stated and pointed.

## 3. What has changed: five trials

All five ran on 2026-11-10 on the landed package (`binary/`, Lean v4.35.0,
the landed Kraken pin `43df9468`), each by a fresh worker agent (the model
this assessment runs on, Claude Fable 5.2) barred from reading earlier
attempts, under a time budget fixed before it started, keeping a log of
every failed check cycle. T5 alone was allowed to read T1, T2 and T4.
Times are box wall-clock from the worker's start; the harness's own
durations agree with them. The harness reported about 0.12, 0.22, 0.45,
0.48 and 0.54 million tokens for the five workers, 1.8 million in all. I
recompiled every module afterwards and read every final statement.

| | Target | Budget | Used | Result | Lean written (non-blank lines) | Failed check cycles |
| --- | --- | ---: | ---: | --- | ---: | ---: |
| T1 | 22 unproved instructions of the insertion (`Add.entry+0x338` to `+0x38c` or `+0x6c0`): four stores into three trie nodes, three loads after the first stores, one branch | 45 min | 7 min | Closed | 196 | 11 |
| T2 | The insertion's open "covering" case: reconstruction after its four connection stores, the link to the mirror's two `chooseAndConnectNode` calls, preservation of the structural check `heap` | 100 min | 13 min | Closed, all three | 994 | 10 |
| T3 | A target the track never touched: `counter_validate` (the replay window) as inlined in `wg_packet_rx_poll`, 67 instructions with a loop and eleven callback sites: image terms, statement, executed tests, proof, link to the mirror | 110 min | 50 min | Closed up to the test-and-set instruction, callbacks as hypotheses | 1,768, and 205 generated | 38 |
| T4 | The first complete path of the insertion: empty root, from `Add.entry` to `ret`, with an allocator contract and the link to `Leanux.WG.add` | 95 min | 49 min | Closed, with the -ENOMEM and both -EINVAL exits as well | 2,027 | 28 |
| T5 | The insertion's intermediate-node path (second allocation; an existing subtree re-parented under a fresh internal node): data result, structural check, machine side, composition from the entry | 75 min | 55 min | Partly closed: data result, mirror link and structural check for both sub-cases; machine code from `+0x338` to the return for both. Not reached: the 45 instructions initializing the internal node, composition from the entry, rollback | 3,119 | 22 |

**T1, stepping.** The statement was fixed before the worker started. It is
the one the Ascent probe froze for its stage 3 (`binary-ascent/stage3/Target.lean`
on the local branch `task/ascent-probe`, not on main); I copied it into the
trial directory, where it compiles on the landed package with one import
removed, and reran its executed tests there: 3,600 constructed states
satisfy it, five wrong variants and three overlapping layouts are rejected.
The worker proved it by the landed method (one lemma per generated region
under `simp`, composed with `region_eventually`) in 6 minutes 45 seconds.
None of its failed cycles concerned memory frames, aliasing or mapping; four
were deliberate looks at a goal; the rest were normal-form friction (operand
order, literal spellings, the branch condition). It handled a symbolic
shift count by splitting into its eight values and deciding the residue,
which would not scale to wider operands. The probe's direct arm took 5
minutes 53 seconds on its own toolchain; the figure reproduces on the
landed one.

**T2, reconstruction after mutation.** This is the class of work the closing
record names as the continuing expense. The worker wrote the statement and
the reasons its hypotheses hold before proving, then closed the
reconstruction lemma at 3 minutes, the mirror link at 5, the structural
check at 12. Part 1 needed two new lemmas; everything else was a second
pass through the landed child case, whose connection lemmas are generic
enough to apply twice. About 630 of the lines are the structural check,
re-derived layer by layer because the landed lemmas are stated at the shape
of the child case. Limits: the four stores are taken as given memory (the
instructions performing them were not executed); the ordering and prefix
hypotheses of the mirror link and the structural check are argued in
comments, not derived from the placement loop; no state witnessing them
together was built.

**T3, a new target end to end.** Image terms for the segment came from an
85-line script in the package's style in two and a half minutes (objdump's
bytes checked against the ELF, branch encodings against targets). The
statement (a machine-width pure function with two reject outcomes, because
the image has two reject exits where the C has one; a memory relation for
the counter and the 128-word bitmap; the exit state and the write frame)
was written and executed on 46 runs with ten wrong variants rejected before
any proof. The theorem `T3.counter_window` closed at 35 minutes, the clear
loop by induction. The link to `Leanux.WG.counterValidate` closed at 45
minutes as a theorem. Limits: the proof stops at the `bts` (the pinned
Kraken has no `bts` in any form, register or memory; the brief had said
only the memory form was missing); the eleven callback sites are discharged
by a hypothesis with an abstract invariant, which the worker showed
satisfiable by stub callbacks but not by the kernel's, since the landed
package proves the PC, 1- and 4-byte callbacks from the image and not the
8-byte ones this code calls; the entry state is not derived from
`wg_packet_rx_poll`; the mirror's recorded decisions are not related to
anything; the pure function is the worker's own, proved equal to the mirror,
not the proof tree's `CounterWindow.step`, which the trial could not import.

**T4, composition from the entry, and a contract.** October's record for
this path was its tail as a component (`Root.initialization_checked`) and a
count of zero complete functions. The worker reached the allocator call at
14 minutes, defined the contract and passed through it at 16, established
the landed tail's executable boundary check from the entry assertion at 19
(this needed a nine-line converse of a landed lemma), composed to `ret` at
23, and linked to the actual `Leanux.WG.add` at 30. It then tightened the
contract and closed the three failure exits. The two large landed
components applied unchanged. Limits: the entry assertion was not executed
on a constructed state, only argued satisfiable; the allocator contract is
new, unproved trust surface with two parameters that have no content (the
allocator's precondition and its own write set), and its success and
failure clauses are paired with the mirror's hidden allocation outcome by
hypothesis; the result is `Eventually (instructionStep fetch)` only, without
the history and permission conclusions some landed headlines carry; the
wrappers and the sequence counter are not included. The worker also found
that the proof tree already contains the source-side fact it needed
(`Leanux/Proofs/WG/AllowedIps/MutationMirror.lean`) and re-proved it,
because the binary package may not import the proof tree.

**T5, two fresh objects at once.** The question was whether the landed
machinery, built for one pending leaf, survives a second allocation. The
landed `Pending` structure fitted unchanged. What did not fit was
`reconstruct_allocated`, which cannot be applied twice: between the two
allocations there is no reconstruction to apply it to, because a leaf whose
parent word is still zero does not decode, so the relation is undefined at
every state between an allocation and its publication. The worker wrote a
two-allocation assembly and re-stated the connection lemmas generically in
the names and in which node is child or parent (253 lines), after which
the data result closed at 9 minutes, its mirror link at 15, the structural
check at 24. It then executed the 16 instructions of the third connection
and the 7 of the root publication, joined them to T1's theorem and the
landed callback and return components, and reached the caller's return
address with `Corresponds` and `heap` for both sub-cases at 53 minutes.
Limits: the initialization of the internal node (`+0x292` to `+0x338`,
about 45 instructions with a width-dependent key copy) is a hypothesis
(`InternalInit`), not a proof; the mirror's hidden allocation step is not
run; the ordering, prefix and side conditions of the structural check, and
the three links between the bits the machine selects and the mirror's
`choose`, are hypotheses argued in the statement file and not derived from
the walk; composition from the entry and the -ENOMEM rollback were not
started. My brief for this trial misdescribed T1's segment as the last two
connections; it is the first two of three. The worker found the third,
after a callback that neither the brief nor T1 mentions, and proved it.

**A caveat on the trial harness.** The trial modules were compiled one file
at a time against the built package, not as part of it. One worker found a
`simp` set the package uses that fails in that setting, and module names
that clash with the package's. Moving any of these files into `binary/`
would need a pass for both.

**Comparison with October.** The like-for-like points are few. The child
case of the insertion (machine regions, reconstruction, mirror link,
structural check) was four commits within about an hour and 3,617 added
lines; T2 did the data, mirror and structural parts of the next case in 13
minutes and about 1,000 lines on top of them. The index removal and
replacement were measured at 18.5 anchored instructions per elapsed hour
including tests, captures and witnesses; T3 did 67 instructions with its
statement, tests and mirror link in 50 minutes, without captures. A fair
summary is a factor of three to five on like steps, from workers starting
with no context: a large change in price, not a change of kind. October's
agents would have finished the insertion too, given the hours.

### What the trials do and do not show

Shown:

- The pieces October recorded as its continuing expense or left open
  (reconstruction after mutation, the structural check, a second
  allocation, composition from the entry, an allocator contract) are each
  a matter of minutes to an hour for a fresh worker once the framework
  exists. The framework is October's achievement and the trials lean on it
  throughout.
- A target the track never touched can be taken from the ELF to a tested
  statement without new infrastructure.
- Several workers can share one built tree and work concurrently; warm
  checks take one to three seconds.

Not shown:

- That any of these results would survive review to landing standard. I
  read the statements and found them sensible; I did not audit the proofs'
  helper lemmas, and no independent reviewer has seen them.
- That the hypotheses the workers introduced are satisfiable together, or
  derivable on the real path. T2, T4 and T5 each rest on hypotheses that
  are argued and not derived; the detail above lists them. A completed
  insertion has to discharge every one.
- Anything about entry realism, concurrency, or the decoder link. The
  trials inherit every assumption of section 1.
- A like-for-like speed ratio. October's timings are commit intervals of a
  coordinated run that also wrote tests, captures and reports.
- Cost on a genuinely new data structure with mutation (skb queues, timers,
  netlink messages). T3's state is one counter and an array.

## 4. Ways forward

Costs are in worker-agent time on this box, wall-clock, and owner attention.
The agent figures come from the trials and are uncertain by a factor of
three either way; the owner figures are my estimates and are the ones that
matter.

### A. Resume function by function towards the whole mirror

- *Next result:* checkpoint A of the October charter, then B, then the next
  subsystem.
- *Claim:* as today, per function.
- *Cost:* agent time is no longer the obstacle. T3 took 67 instructions
  from nothing to a theorem with its statement, tests and mirror link in 50
  minutes; at that rate the remaining 11,800 anchored instructions are one
  to two hundred worker-hours where the code is like what has been done,
  more where a new data structure needs its relation. The cost is the
  surface: at the present 4,713 printed lines for 4%, the whole would print
  something like a hundred thousand lines of statements and definitions,
  plus about 139 service contracts, each a place where an assumption can be
  wrong and nobody proves it right.
- *Fails if:* nobody can read what is claimed. It would.
- *Earliest test:* none needed; the surface numbers already answer it.
- *Verdict:* not as before. Breadth is conceivable only after the statement
  form changes (E).

### B. Restructure the proofs around a typed-heap or reconstruction-level interface

- *Next result:* existing theorems re-proved through a new interface.
- *Cost:* days of agent time per attempt, on the record of three attempts.
- *Evidence:* heap view, 12% more lines; machine-state view, 45% more;
  external weakest-precondition layer, no authoring saving on a fresh
  segment and named engine gaps (calls, repeated call sites, fragments that
  exit by a jump). T1 shows the cost these aimed at is small already.
- *Verdict:* stop. The one restructuring the trials support is local and
  cheap: make the expected-state and structural-check lemmas parametric in
  the node update (section 2), when the insertion is completed. The
  unlanded local-contracts proposal should be dropped; the heap-view branch
  is a finished negative result and can be recorded and removed.

### C. Fewer, deeper results

**C1. Complete the allowed-IPs insertion.**
- *Next result:* one theorem per wrapper (`wg_allowedips_insert_v4`, `_v6`)
  over every path of `add`, then the retained-heap sequence with lookup.
- *Claim and assumptions:* section 1's, plus an allocator contract and, for
  rollback, a free contract.
- *Cost:* measured so far: the empty-root path with its three failure exits,
  49 worker-minutes (T4); the covering case's data side, 13 (T2); the
  intermediate case's data side and its machine code from the connection
  stores to the return, 55 (T5). Still to do: the entry-to-loop-header
  assertion; composition of the exact and child paths from the entry; the
  machine regions of the covering and intermediate connections that no
  trial executed; rollback, with a free contract; the two wrappers; one
  theorem over all paths; the sequence with lookup. I estimate 10 to 20
  worker-hours, a day of wall-clock for four workers, then an independent
  review and its repairs: two to three days elapsed. (T4's worker, not
  knowing T2's or T5's results, estimated 12 to 25 hours for the remaining
  paths; T5's worker estimated 3 to 5 hours for the rest of its own.) The
  largest uncertainty is not a proof but a derivation: T2 and T5 assume the
  ordering and prefix facts their structural checks need, and those have to
  come out of the placement loop's postcondition and `common_bits`. Owner:
  one sitting for the statement packet, one for the review's findings, one
  run of the external gate.
- *Fails if:* the composed entry assertion or the allocator contract cannot
  be stated in a form the owner accepts; or the paths' side conditions
  cannot be derived from what the landed loop theorem exports, in which
  case that theorem has to be strengthened first.
- *Earliest test:* write the statement packet first (the theorem, the entry
  assertion, the contract; no proof) and have the owner read it. Half a day.

**C2. The replay window, from machine code to the anti-replay theorem.**
- *Next result:* the compiled `counter_validate` in `wg_packet_rx_poll`
  computes the proof tree's pure window step
  (`Leanux.Proofs.WG.CounterWindow.step`) on the keypair's memory; with the
  landed `AntiReplay.pure_uniqueness`, no counter is accepted twice by a
  sequence of executions of that code between which the window's bytes are
  not otherwise written.
- *Claim and assumptions:* section 1's. This segment runs with bottom halves
  disabled and touches only the keypair, the stack and the coverage buffer,
  so the sequential assumption is closer to true here than anywhere else in
  the driver: what is assumed is that a hard interrupt does not write those
  bytes.
- *Cost:* T3 took 50 worker-minutes to the test-and-set with the callbacks
  assumed. Still to do: the `bts` semantics and the last two instructions (an
  hour or two with the patch's tests); the two 8-byte comparison callbacks
  proved from the image and an invariant that instantiates T3's hypothesis
  (T3's worker estimates half a day to a day; I would plan on the day);
  restating against `CounterWindow.step` and the corollary over a sequence
  of calls (hours). Two days elapsed with review. Owner: the patch decision
  and one sitting for the statement.
- *Needs from the owner:* a tenth Kraken patch adding `bts`, which the
  pinned semantics lacks entirely (a trust-surface change); a home for a
  theorem that imports both the binary package and `Leanux.Proofs`, which
  the landing rules currently keep apart.
- *Fails if:* the callbacks' invariant cannot be instantiated (T3 states
  them as hypotheses; the landed package proves the 1-, 4-byte and PC
  callbacks from the image but not the 8-byte comparison ones).
- *Earliest test:* T3 was that test. It got to a checked theorem at the
  test-and-set in 35 minutes and to the mirror function in 45.

### D. Change what is trusted

- *A build without KCOV as the proof target.* Removes a seventh of the
  instructions and most of the callback machinery, and makes the target
  nearer to a kernel someone runs. It breaks the identity between the
  proved image and the tested oracle, invalidates the landed image terms,
  and is a kernel-configuration change needing its own case. Not now;
  decide it before any return to breadth.
- *The C instead of the binary.* The owner's RefinedC port
  (`~/projects/cerberus-caesium`) is a C-level proof host in Lean. It would
  trade the decoder and ISA assumptions for a C semantics and the compiler,
  and give typed memory and visible loops. I did not assess whether it
  accepts kernel C. The cheap test is `counter_validate` alone through it;
  the owner is better placed than I am to say whether that is an afternoon
  or a month.
- *Trust more of the environment explicitly.* Unavoidable beyond leaf
  functions. If breadth is ever resumed, the contracts should be one
  reviewed file, each tested against captures, with a count kept.

### E. Use the mirror, and the statements, differently

- *Prove against the proof tree's pure models where they exist*, then
  compose with the landed model-to-mirror refinement, instead of against
  the monadic mirror run with its decision records. C2 does this.
- *One statement schema.* A single reviewed definition of "this compiled
  function refines this mirror function under relation R and contracts C",
  instantiated per function, so the owner reads the schema once and then
  only R and C per data structure. Internal cuts stop being printed
  surface: they are means, which the charter already said they were.
- *A surface budget.* A stated number of printed lines per function family,
  checked at each claim point like the axiom list. I suggest 300.

### F. Stop

- *What it keeps:* the landed package as a frozen experiment with its
  limits stated, which it already is.
- *What it gives up:* the only part of the project that touches the code
  Linux actually runs, at the moment its marginal cost fell.
- *When it is right:* if the owner does not want to spend reading time on
  claims of section 1's kind. It is a judgement about value, not cost.

### Parallelism

The work absorbs more agents than the owner can supervise. Four workers ran
at once here in one built tree without contention. The limits are elsewhere:
one headline at a time per owner review slot; every Kraken patch and every
contract is an owner decision; the external `lake check` gate is run by the
owner outside the sandbox on an export that was 1.75 GB at the last landing.
A workable shape is one statement owner, three to five provers on the paths
or regions of one function, one independent reviewer who sees the code and
not the provers' conclusions, and one headline in flight.

## Recommendation and decision points

Do C1 and C2, under E's discipline, and nothing else on this track until
both are landed or have failed.

Decisions for the owner:

1. Whether a claim of section 1's kind (sequential model, literal image,
   instrumented build, explicit contracts) is worth reading time at all. If
   not, stop here (F).
2. The order of C1 and C2. I would run them together; if one, C2 first: it
   is smaller, it carries a property people care about, and it is a result
   of the kind the adopted criterion asks for.
3. The `bts` patch to the pinned Kraken, with its tests.
4. Where a theorem lives that joins the binary package to the proof tree.
5. The allocator and free contracts, read before any proof uses them.
6. The surface budget and the statement schema (E), as standing practice for
   this track. This would be a change to how the binary gate is used, not a
   new gate.
7. The unlanded branches: record `task/binary-heap-view` as a closed
   negative result and remove its worktree; drop the local-contracts
   proposal; `task/ascent-probe` is already decided.
8. Breadth, the KCOV-free target and the C route: defer all three until C1
   and C2 report their printed surface per function.

What I would do first, in order:

1. Write the two statement packets, no proofs: for C1 the wrapper theorem,
   the entry assertion and the allocator contract; for C2 the window
   theorem through the test-and-set and its corollary. Run each on
   constructed and captured states with wrong variants rejected, as the
   track already does. Give them to an independent reviewer, then to the
   owner. About half a day of agent time; one sitting for the owner.
2. On sign-off of the statements, prove them, with the trial files in
   `.tmp/trials/` as a starting point if the owner wants them kept.
3. Independent review of each result against the code, the owner's external
   gate, landing.
4. Report printed surface and agent time per completed function, and decide
   point 8 on those numbers.

## What I verified, inferred and did not check

**Verified by running or reading the thing itself:**

- The landed package checks from main in a fresh worktree: bootstrap of the
  pinned Kraken to the locked commit, then `scripts/binary-proof-gate`,
  which passed (1,119 build jobs, the printed surface equal to
  `TrustSurface.expected.txt`, the source scan clean). The build outputs
  were copied from the heap-view worktree and replayed by Lake against the
  sources' hashes, not compiled afresh.
- Nine landed headlines depend only on `propext`, `Classical.choice`,
  `Quot.sound` (printed from the built modules).
- The headline shapes, `SerializedEnvironment`, the decoder agreements, the
  callback contracts and the allowed-IPs relation, by reading
  `TrustBase.lean`, `PairAllowedipsState.lean`, `LookupAdequacy.lean` and
  the printed surface.
- The module, line and theorem counts; the surface line counts at three
  commits; the commit times and sizes of the October increments
  (`git log --stat -- binary`).
- The counts of instructions, coverage transfers and external callees in
  WireGuard's text, from the saved s5 ELF.
- All five trials: I recompiled each final module with the package's
  toolchain, checked the printed axioms, searched for `sorry`, new axioms,
  native decision and resource raises, and read the final statements.
- That regions `Add.r338`, `Add.r35a`, `Add.r373` were used by no landed
  proof before T1.

**Inferred:**

- The 4% coverage figure joins my list of complete theorems to the scoping
  census, which was taken on the earlier image; the landing record says the
  anchored bodies kept their sizes.
- The attribution in section 2 is my judgement from the record and the
  trials. In particular "the metric was the proximate cause" is a reading
  of the charter, the closing record and the recorded rates together.
- The cost estimates for C1 and C2 extrapolate from five trials, each a
  single run by a single worker.
- The projection of the printed surface to the whole mirror is linear
  extrapolation and could be far off in either direction.

**Not checked:**

- The external `lake check` gate (it must be run by the owner outside the
  sandbox); the last allowed-IPs export's acceptance was pending at landing
  and I found no later record.
- Whether boot-time or run-time text patching can touch the proved ranges.
- Kraken's semantics or the nine patches against any other model of x86-64.
- The package's executed test suites, the captures and the QEMU-backed
  checks: none was rerun.
- The helper lemmas inside the trial proofs, beyond compilation and axioms;
  joint satisfiability of the hypotheses the trial workers introduced.
- The RefinedC port's ability to take kernel C.
- The proof campaigns over the mirror, beyond locating the window model and
  the anti-replay statements that C2 would use.

## Reproduction

The trial files are in the ignored directory
`.worktrees/binary-reassessment/.tmp/trials/` of the main checkout on
`reynolds-oath`: `COMMON.md` (the rules every worker had), and per trial
`BRIEF.md`, `LOG.md`, `Statement.md` where one was written, and the Lean
modules. They are not committed and go when the worktree is removed; if any
is worth keeping, that is the owner's call.

The worktree also holds about 2 GB of build outputs (`.lake`,
`binary/.lake`, `.deps/kraken`) that the trial files need; they go with the
worktree.

To rebuild the setting from a clone, in a worktree of main:

```sh
binary_python=$(command -v python3)
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
cap scripts/in-bundle "$binary_python" -B binary/run.py --bootstrap-only
cap scripts/in-bundle lake -d binary build
```

To compile a trial module `M.lean` in a directory `D` outside the package
(dependencies of the same directory first):

```sh
LP=$(cd binary && ../scripts/in-bundle lake env printenv LEAN_PATH)
(cd D && mkdir -p build && \
  cap ../path/to/scripts/in-bundle env LEAN_PATH="$LP:$PWD/build" lean -o build/M.olean M.lean)
```

Trial order of compilation:

- `t1/`: `Target`, `Setup`, `TargetTest` (the executed tests, about a
  minute), `Direct`, `DirectCheck`.
- `t2/`: `CoverReconstruct`, `CoverSource`, `CoverTrieHeap`,
  `CoverIncoming`, `CoverHeap`.
- `t3/`: `RxCounterImage`, `RxCounterLayout`, `RxStatement`, `RxTest`,
  `RxArith`, `RxRegions`, `RxMemory`, `RxProof`, `RxMirror`, `RxMirrorRun`,
  `RxWitness`; `gen.py` regenerates the first two from the saved ELF.
- `t4/`: `T4Prologue`, `T4Stack`, `T4Regions`, `T4Live`, `T4Entry`,
  `T4Alloc`, `T4Boundary`, `T4Tail`, `T4Return`, `T4Fresh`, `T4Reach`,
  `T4Machine`, `T4Source`, `T4Main`, `T4Fail`, `T4MainFail`.
- `t5/`: its copies of T2's first four modules and of T1's `Target`,
  `Setup`, `Direct`; then `T5Generic`, `T5Reconstruct`, `T5Bridge`,
  `T5Machine`, `T5Path`, `T5Run`, `T5Source`, `T5TrieHeap`, `T5Heap`,
  `T5HeapMemory`, `T5Transfer`, `T5Main`, `T5Return`, `T5MachineRoot`,
  `T5Root`, `T5RootSource`, `T5PathRoot`, `T5RootHeap`, `T5RootHeapMemory`,
  `T5RootReturn`, `T5Axioms`.

`.tmp/trials/bin/check <dir> <Module>` is the helper the workers and I used
for the command above.

The counts of section 2:

```sh
# surface lines at three commits
for c in 686bba49 4c85a802 dcafc971; do git show $c:binary/TrustSurface.expected.txt | wc -l; done
# October increments
git log --format='%h %ad %s' --date=format:'%m-%d %H:%M' --reverse -- binary
git show --stat --format= ff877b1a 4fdb882a 509103fc 2f1b3bf0 -- binary
```

The instruction, coverage-transfer and callee counts come from disassembling
the address range of WireGuard's text symbols in the saved s5 `vmlinux`
(`objdump -d --no-show-raw-insn`, between `handshake_init` and the end of
`wg_get_device_dump`), counting instruction lines, `call`/`jmp` targets
named `__sanitizer_cov*`, and other direct targets outside the range. The
range is approximate at its lower end (two WireGuard helpers fall just
below it and were counted as external); the figures are 14,194 instructions,
2,090 coverage transfers, 588 external call sites, 139 distinct callees.
