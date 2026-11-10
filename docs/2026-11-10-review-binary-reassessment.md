# Independent review: the binary track's reassessment

2026-11-10. Reviewed: `docs/2026-11-10-binary-track-reassessment.md` at
`02e48bae` (main at `46e879f2`), with the five trials it reports, read from
the local branch `task/binary-trials` (`12ad7cd6`, identical to the scratch
copies in `.worktrees/binary-reassessment/.tmp/trials/`). Written on
`task/review-reassessment` in its own worktree
(`.worktrees/review-reassessment`), with its own copy of the build outputs,
replayed by Lake against main's sources. Inputs read: the document; every
trial's `BRIEF.md`, `LOG.md`, `Statement.md` and final statements;
`binary/TrustBase.lean`, `binary/TrustSurface.expected.txt`,
`binary/surface.py`, the relation and frame definitions of the paired index
and allowed-IPs results; the October closing record, charter, landing review
and decisions; the heap-view branch's two reports; the s5 `vmlinux`; the
oracle's choice-stream patch. The review's judgements are mine [AGENT].

During the review the coordinator relayed the owner's definition of trust
surface, in two kinds: *assumed* (the semantic base, the reading of the
image, a headline's premises and contracts, any of which may be false or
unsatisfiable) and *claimed* (the headline statement with every definition it
mentions, transitively, which may be weaker than it looks or vacuous);
kernel-checked material a headline does not mention is not trust surface.
I have this from the coordinator's relay, in paraphrase, not from the owner
directly. Section 3 measures the landed package under that definition.

## Verdict

**The trial results are real and the document's factual base is mostly
sound. Its two central inferences are not established by its evidence, and
one of its cost estimates misses a known kind of obstacle.**

What can be relied on:

- Every trial recompiles from its sources against the landed package with
  only `propext`, `Classical.choice` and `Quot.sound`, no escape, no
  resource raise; the timings agree with the files' modification times; the
  executed tests of T1 and T3 reproduce.
- The counts I could check are right, most of them exactly (section 1).
- The document's own lists of limits are candid. Most of what follows is in
  them in some form. My disagreement is with what the conclusion makes of
  them.

What cannot:

- *"What limits the track is what the owner has to read"* (conclusion 3) is
  measured on the wrong object. Nearly half of the 4,713 printed lines are
  statements and definitions of internal-cut component theorems, which a
  finished headline does not mention, and the file omits the bodies of the
  relations. Under the owner's definition the landed
  finished headlines carry about 2,400 hand-written source lines in all,
  440 to 900 new per function family, and the insertion increment added
  eleven lines of contracts. The projection to "a hundred thousand lines"
  and the proposed budget of 300 have no basis in that measure (H1).
- *"The open pieces close in minutes"* (conclusion 2) holds for the parts
  that repeat a landed pattern. In each of T2, T4 and T5 the part that
  connects the piece to the real path is a hypothesis, and none of those
  hypothesis sets has a witness (M1, M2). T4's allocator contract cannot be
  met by the image's allocator while the oracle is recording allocations
  (H2).
- The estimates for C1 (10 to 20 worker-hours, two to three days) and the
  claim of a three- to five-fold speed-up extrapolate in a unit the October
  records twice warn against, from comparisons that are not like for like
  (M3, M4).

None of this argues against the recommendation's first step. Writing the
two statement packets before any proof is the cheapest way to test exactly
the things this review could not settle, and I would keep it. I would not
take from the document that proof cost has stopped mattering, or that the
owner's reading is the binding constraint.

## 1. Checks run

All in the review worktree, heavy jobs through `capped`.

| Check | Result |
| --- | --- |
| `capped -m 24G -- scripts/in-bundle lake -d binary build`, outputs copied from `.worktrees/binary-reassessment` | 1,119 jobs replayed, exit 0: the copied outputs match main's `binary/` sources by hash. Not compiled afresh |
| All 65 trial modules compiled in the document's order, one `lean -o` each under `capped -m 12G`, into a fresh `build/` per trial | every exit 0, no error, no warning; 199 `#print axioms` lines, all within the three standard axioms (171, 21 with two, 7 with `propext` alone) |
| Source scan of the trial files for `sorry`, `admit`, `axiom`, `native_decide`, `+native`, `unsafe`, `implemented_by`, `extern`, `set_option`, `opaque`, new syntax or attributes | none, except three `decide +kernel` (T1 `Direct.lean:81` and its copy, T5 `T5Machine.lean:55`), two tactic macros in `t3/RxRegions.lean`, and `#eval` tests. `decide +kernel` adds no axiom and is not on the gate's list |
| T1 `TargetTest`: 67 s | 3,600 cases hold; five wrong variants rejected (on 1,152 to 3,600 cases); three overlaps rejected; as reported |
| T3 `RxTest`: 20 s | 46 runs pass; ten mutants fail on 2 to 34 runs; as reported. The callbacks in these runs are stubs (`RxTest.lean:38-48`) |
| `verify/Axioms.lean` | nine landed headlines, standard axioms |
| Modification times of the trial files against the logs | consistent: T1 7 min, T2 13, T3 50, T4 49, T5 55; T1 to T4 overlapped |
| T1's `Direct.lean` against the Ascent probe's direct arm (`task/ascent-probe:binary-ascent/stage3/Direct.lean`) | 36 of about 200 distinct lines in common: not a copy. The trial worktree did not contain the probe's closing report until 02:39 UTC, after T1 ended |
| `git show <c>:binary/TrustSurface.expected.txt \| wc -l` at `686bba49`, `4c85a802`, `dcafc971` | 750, 2,576, 4,713 |
| `objdump -d --no-show-raw-insn` of `handshake_init` to the end of `wg_get_device_dump` in the s5 `vmlinux` | 14,194 instructions, 2,090 coverage transfers, 588 external transfers, 139 distinct callees: exactly as reported |
| Scoping census (`docs/2026-10-15-binary-tv-scoping.md:119,203,249-255`) | 62, 76, 25, 41, 109, 103, 73 instructions; 489 of 12,340 is 4.0% |
| `binary/*.lean` | 944 modules, 105,059 lines, about 3,950 theorems; unchanged since `e8b16952` |
| October rates and increments | 18.5 (`2026-10-18-paired-index-subsystem.md:848`), about 25 (`2026-10-18-paired-index-insertion.md:834`); four commits 08:17 to 09:10 on 20 October, 3,617 added lines; heap view +12%, machine-state view 925 to 1,339 lines: as reported |
| `SerializedEnvironment` (`TrustBase.lean:100-102`) and `instructionStep` (`Execution.lean:25-32`) | two equations over variables that do not occur in the step relation: the document's statement that it constrains nothing is correct |
| Dependency closure of the 71 gate headlines, by a Lean metaprogram (section 3) | the numbers of H1 |

## 2. Findings

Severity: **H** changes what the owner should conclude from the document;
**M** qualifies a claim or estimate; **L** is a slip or a note.

### H1. The surface numbers do not measure what the owner reads, in either direction

The document's third conclusion and its section 2 rest on "750 lines to
4,713 while the proved share reached 4%", and route A projects "something
like a hundred thousand lines".

`binary/TrustSurface.expected.txt` is three things (`binary/surface.py:170-191`):

| Part | 686bba49 | 4c85a802 | dcafc971 (now) |
| --- | ---: | ---: | ---: |
| Printed headline statements | 230 (10) | 745 (48) | 1,587 (71) |
| Printed definitions | 80 | 1,085 | 2,369 |
| `TrustBase.lean`, verbatim | 438 | 744 | 755 |

Of the present 1,587 statement lines, 820 are the 23 internal-cut component
theorems of the insertion (and `findNode`, `common_bits`, the random
service's return), 469 are 21 complete functions and sequences, 199 six
transport results, 89 sixteen witnesses, 10 the five proved callbacks. The
growth from 2,576 to 4,713 is 842 lines of component statements, 1,284 lines
of the definitions they mention, and 11 lines of `TrustBase.lean`. No
finished headline was added, so under the owner's definition that increment
added nothing to the surface of any result; it printed means.

The file is also not closed. Of 641 project names its statements and
definitions refer to, 281 are not printed. Among them are the bodies that
say what the relations mean: `Binary.Pair.reconstruct`, `Binary.Pair.target`
and `Names.validate` (`PairMemory.lean:29-144`),
`Binary.Pair.Allowedips.decodeNode`, `decodePeer`, `validate`, `assertAt`,
`Binary.Pair.Trie.heap`, `IndexLookup.Result`, `Sequence.Interface`,
`LookupRelation.Physical`. A reader of all 4,713 lines sees
`Corresponds n o m d := reconstruct n o m = .ok (target d)` and not what
`reconstruct` reads. So the file overstates the reading by its component
material and understates it by its missing closure.

Measured under the definition (section 3), the finished landed headlines
mention about 2,430 hand-written source lines, of which about 2,170 are
reachable from premises (assumed) and 270 only from conclusions; 830 lines
of generated image terms; 62 layout constants; and the mirror and Kraken.
Per family, in landing order: 903, 638, 447 and 443 new hand-written lines
for 138, 66, 109 and 176 instructions. The one finished path among the
trials, `T4.add_empty_root`, mentions 650 hand-written lines, of which 113
are new to the trial and the rest is the allowed-IPs relation the landed
lookup already mentions. `T3.counter_window` mentions about 145.

Consequences: the 4% against 4,713 comparison, the linear projection and
the suggested budget of 300 printed lines per family (every landed family
exceeds it in source lines) should not be used. What a finished function
costs to read is a few hundred lines once its data structure's relation
exists, most of it the entry check and the relation, not contracts. That is
real, but it is not obviously the binding constraint, and the document's
option E (one statement schema, cuts not printed) is supported more
strongly by these numbers than by its own.

### H2. T4's allocator contract excludes the image's allocator in the oracle's recording mode

`T4.AllocatorContract` is stated at `0xffffffff81196d20`
(`t4/T4Alloc.lean:15-24`). In the s5 image that is
`kmem_cache_alloc_noprof`, and it contains the oracle's own allocation
hooks:

```
$ objdump -d --no-show-raw-insn --start-address=0xffffffff81196d20 --stop-address=0xffffffff81196f40 vmlinux
ffffffff81196d5b: mov 0xe294df(%rip),%eax   # <kcov_alloc_armed>
... call <__kcov_alloc_pre> ... call <___slab_alloc> ... call <__memset> ... call <__kcov_alloc_post> (twice)
```

`__kcov_alloc_pre` and `__kcov_alloc_post`
(`kernel/patches/choice-stream.patch:1042-1091`) append the allocation
record to the task's KCOV area (`kcov_choice_write`, lines 308-314, writes
`t->kcov_area`) and, when a schedule steers the site, force the failure.
That record is where the mirror's hidden allocation outcome comes from, and
the October experiment armed these sites
(`docs/2026-10-20-binary-allowedips.md:182-184`).

T4's entry assertion requires the allocator's footprint to miss the
coverage state: `awApart : ∀ a, aw a → ¬Window s0 a ∧ ¬c.bytes a`
(`t4/T4Boundary.lean:93`), where `c.bytes` includes the KCOV storage
whenever the coverage mode is recording (`binary/CommonBitsCoverage.lean:34-35`),
and the theorem concludes `c.At` at the return. So with coverage recording
and the site armed, no footprint of the real allocator satisfies the
hypotheses: the theorem holds only for the configuration in which the
allocation is not recorded. `t4/Statement.md` says both that the
allocator's "own KCOV callbacks ... [are] inside `writes` by assumption" and
that `writes` misses the coverage state; those cannot both hold.

This is the same situation as the random provider behind index insertion,
which the landed package handles with `RandomReturnContract`,
`RandomInputCoupling` and ten `RandomProvider.*` definitions, leaves about
1,267 instructions behind a hypothesis, in an increment that took 4 h 22 min
and 10,066 lines in October. The document's C1
estimate has no line for it, and its account of T4's limits ("two
parameters that have no content") does not mention it. The free path
(`kmem_cache_free`, for rollback) was not examined by anyone. T4 remains a
checked theorem; "the first complete entry-to-return path ... with an
explicit allocator contract" needs the qualifier that the contract is not
yet one the instrumented image can meet in the mode the mirror's inputs
come from.

### M1. In each trial the difficulty the October record named sits in a hypothesis, and the briefs carried part of the design

- **T2.** The brief gives the statement almost whole: the two memory terms
  `m1`, `m2`, the expected state in words, the landed lemma to imitate
  (`t2/BRIEF.md`, "Target"). The four stores are a memory term, not executed
  instructions. The "mirror link" is to two `chooseAndConnectNode` calls
  run on a hand-built device `coverPending` (`t2/CoverSource.lean:10-14,29-41`),
  not to `Leanux.WG.add`, whose covering branch also consumes
  `addNewnodeCoversDown` and `addNewnodeAtRoot` (`Leanux/WG/AllowedIps.lean:155-159`).
  Only the non-NULL-parent sub-case is treated; the table's "Closed, all
  three" does not say so, and the root sub-case
  (`rcu_assign_pointer(*trie, newnode)`) is open. `heap_installedCover`
  takes eight path facts as hypotheses (`t2/CoverHeap.lean:271-287`).
- **T3.** The brief supplies the segment's addresses, the roles of `r13`
  and `rbx`, the field offsets and the shape of the statement
  (`t3/BRIEF.md`, "Target"); "from the ELF to a tested statement" in 50
  minutes starts after that reverse engineering. The theorem stops before
  the `bts`, so the bit that decides acceptance is never computed. The
  eleven callback sites are a hypothesis satisfied in the trial only by
  `ret` stubs. The tests run the generated terms under Kraken with stubbed
  callbacks: they test the statement against the semantics, not against
  the kernel.
- **T4.** Nothing executes or witnesses the entry assertion; see H2.
- **T5.** The capstone `machine_intermediate_return` has 48
  hypotheses (`t5/T5Return.lean:13-66`). Among them: `InternalInit` (the
  missing 45 instructions), the three links between the machine's selected
  bits and the mirror's `choose`, `sides : b1 ≠ selected byte shift`, and
  the same ordering and prefix facts as T2. The device in the conclusion is
  the formula `intermediateInstalled`, linked by a separate lemma to
  connection steps run from a hand-built device after the allocation; the
  mirror's `allocNode` is not run. The worker ended at 52 min 57 s of 75,
  having chosen the NULL-parent variants over the initialization segment
  (`t5/LOG.md`, 03:18, 03:33, 03:36, 03:41:47). "Not reached" in the
  document's conclusion reads as out of time; it was declined, and it is
  the part of that path unlike anything the trials did.
- No trial has a state satisfying its hypotheses together, except T3's with
  stub callbacks and a zero bitmap (`t3/RxWitness.lean`). I did not find a
  contradiction in any hypothesis set, and did not build a witness.

The document lists nearly all of this under each trial. Its conclusion 2
and "Shown" list do not carry it: the accurate summary is that second
instances of landed patterns are cheap, which October's four commits in an
hour on the child case already suggested.

### M2. The derivation C1 depends on is source-side work the binary package is barred from importing

The document calls the ordering and prefix facts "the largest uncertainty"
and says they "have to come out of the placement loop's postcondition and
`common_bits`". The landed loop theorem exports the exit address, `rbx` as
the address of the mirror's `nodePlacement` result, the exact flag,
`Corresponds` and `heap` (`TrustSurface.expected.txt:718-756`). It exports
nothing about prefixes or depths, and should not: those are properties of
`Leanux.WG.nodePlacement` and `commonBits` over a well-formed trie. The
proof tree has theorems of that kind
(`Leanux/Proofs/WG/AllowedIps/PlacementMirror.lean`, `GraftMirror.lean`,
`DeepGraft.lean`, `InsertionDispatch.lean`), and `binary/` may not import
them (landing review B1, repaired by `0e5f44c0`). T4's worker already
re-proved one such fact for that reason. The document raises the import
question as a need of C2 only (decision 4). C1 needs it decided first, or
needs the source-side facts restated in `binary/`; neither is in its
estimate, and neither resembles what a trial did.

### M3. The speed-up and the account of the stall are weaker than stated

- "A factor of three to five on like steps" rests on two comparisons. The
  child case (machine regions included, lemmas written for the first time)
  against T2 (no machine regions, by reuse of those lemmas) is not like for
  like. Index removal and replacement at 18.5 instructions an hour (with
  captures, witnesses, composition and export) against T3 at 80 (callbacks
  assumed, no return, no captures, scalar state) is not either. In lines of
  checked Lean per hour the trials ran at 2,100 to 4,600 against October's
  2,180 (18,529 lines in eight and a half hours): one to two times. The
  document says a like-for-like ratio is not shown; its summary sentence
  and conclusion 2 state one anyway.
- The October records say not to multiply an instruction rate by a census
  (`2026-10-18-paired-index-subsystem.md:853-855`,
  `2026-10-20-charter-binary-allowedips.md:220-221`). The document does so
  three times: 506 instructions at the recorded rate, 11,800 remaining
  instructions at T3's rate, and implicitly for C2.
- "The charter counted completed functions at four hours" is not what the
  charter says. Its four-hour checkpoint "reports progress and remaining
  costs and does not silently end the authorized work" (lines 247-250). The
  count of zero is the closing record's; the stop was the user's decision
  recorded there, with the stated motive that allocation identity,
  fresh-node decoding, mutation frames and structural invariants were the
  continuing expense (`2026-10-20-binary-allowedips.md:11-14,56-64`). That
  is a judgement about proof cost per function, on 18,529 lines for no
  finished function, and T5's own findings (the relation is undefined
  between an allocation and its publication; the connection lemmas had to
  be restated generically) confirm the expense was real. "Not a wall" is
  supported. "Did not stall on proof cost" is the author's reading, marked
  as such in the document's "Inferred" list and stated without that mark in
  the conclusion.
- The account of what followed (two re-proofs on 21 October, no result of
  the adopted criterion's kind) agrees with the branch history and
  `docs/decisions.md` (2026-10-20). The heap-view report had set a
  strategic reassessment for about 3 November; none is recorded before this
  one.

### M4. What the C1 and C2 estimates leave out

- Landing. The October increment's review produced a blocking finding and
  repairs over two days (`2026-10-20-review-binary-allowedips-landing.md`;
  commits `0e5f44c0` to `2113ee69`). The trial files do not build inside
  the package (the document says so). The gate's headline list and expected
  surface change. The external check needs the owner and an export that was
  1.75 GB.
- Tests of the new entry assertions on constructed and captured states,
  which the document's first step promises and T4's worker reports as a
  harness change it did not make.
- For C1: H2 and M2; the root sub-case of the covering path; the
  two-allocation run of the mirror's `add` including `hiddenAlloc`, which
  no landed lemma runs; the free contract and its hooks; the wrappers and
  the sequence counter.
- For C2: the two 8-byte callbacks proved from the image and an invariant
  that survives eleven calls, where the landed `KcovPlan` depends on the
  stack pointer, the arguments and the preempt count; the entry state,
  which is in the middle of `wg_packet_rx_poll` and comes from nowhere; a
  semantics patch, which is new assumed surface. The corollary will be over
  re-prepared entry states, as the landed sequences are, so it says the
  compiled segment computes the window step and sets the bit, not that the
  driver drops a replayed packet. That is still a result of the adopted
  criterion's kind; it should be described at that size.
- The workers' own estimates the document quotes (12 to 25 hours, 3 to 5
  hours, half a day to a day) are not in the trial files; they were in
  reports to the author and cannot be checked.

Agent time within a factor of three, as the document says of itself, is
plausible. "Two to three days elapsed" and "one sitting" per stage for the
owner are not derived from anything.

### L1. Slips of fact

- "I found no record that it was settled": the adequacy report records an
  independent review's measurement of no alternatives entry in the anchored
  ranges, no jump table, empty `smp_locks`, no RET-thunk rewriting and no GS
  use (`2026-10-15-binary-adequacy.md:2946-2950`, repeated in the
  `TrustBase.lean` comment the surface file prints). Static keys are not
  named there, and I found no re-measurement for the ranges proved later;
  those parts of the concern stand.
- "All but four of them for the whole file": 86 of the 88 modules have a
  file-wide raise (two of those also a scoped one); two are scoped only.
  Whether the rule's grandfathering reaches `binary/` is the owner's call:
  `AGENTS.md` words it for the proof tree.
- Six patches add instruction semantics; patch 2 also extends the parser to
  an addressing form and is part of the reading of the image.
- The document's table row for T2 (see M1) and the charter (see M3).

### L2. Notes on the trial process

- Isolation from earlier attempts was by instruction in `COMMON.md`, not
  enforced, and no transcript is kept. I found no sign of a breach (check
  in section 1).
- Three workers compiled `sorry`-terminated scratch copies to inspect goals
  (`t2/LOG.md` FAIL 2, `t3/LOG.md` 02:35, `t5/LOG.md` cycles 14, 15, 18,
  21); none is in a kept file. T4's worker wrote one scratch file to `/tmp`
  and removed it.
- The trial worktree was fast-forwarded to main at 02:39 UTC while T3 and
  T4 ran; the change was documentation only (`git diff --stat d45c9ddb
  d741a764 -- binary Leanux scripts` is empty).
- `binary-trials/bin/check` hard-codes the worktree path under `/home`. It
  is on a local branch and would need changing before any use elsewhere.

## 3. The landed surface under the owner's definition

Method. For each of the 71 headlines the gate prints, a Lean metaprogram
opens the statement, takes the constants of its proposition-typed binders
as premise roots and those of its conclusion as conclusion roots, and
closes each set through every definition, structure and inductive type
(types, values and constructors), not through theorems. *Assumed* is the
premise closure; *claimed beyond assumed* is what only the conclusion
reaches. Sizes are source lines of the declarations (declaration ranges,
merged per file), by origin: hand-written `binary/` modules,
`TrustBase.lean`, generated image terms, generated layout constants, the
mirror, Kraken. A relation that occurs in both the precondition and the
postcondition counts as assumed. Internal-cut components are left out of
the totals.

| Headline (`Binary.` omitted) | Assumed: `binary/` + `TrustBase` | Claimed beyond assumed | Image terms |
| --- | ---: | ---: | ---: |
| `LookupRelation.lookup_simulation` | 257 + 314 | 269 + 4 | 243 |
| `LookupRelation.lookup_transport` | 338 + 314 | 205 + 4 | 243 |
| `LookupRelation.lookup_snapshot_transport` | 371 + 314 | 215 + 4 | 243 |
| `Pair.IndexLookup.lookup_checked` | 399 + 157 | 42 + 18 | 241 |
| `Pair.Remove.remove_checked` | 312 + 144 | 44 + 18 | 279 |
| `Pair.Replace.replace_checked` | 325 + 143 | 46 + 18 | 296 |
| `Pair.Sequence.sequence_checked` | 438 + 207 | 81 + 22 | 334 |
| `Pair.Insert.insert_checked` | 502 + 256 | 71 + 4 | 398 |
| `Pair.Insert.insert_from_image` | 502 + 159 | 71 + 4 | 293 |
| `Pair.InsertSequence.sequence_checked` | 684 + 320 | 81 + 8 | 491 |
| `Pair.InsertSequence.sequence_from_image` | 684 + 215 | 81 + 8 | 587 |
| `Pair.Sequence.First.sequence_checked` | 413 + 90 | 113 + 33 | 430 |
| `Pair.Trie.lookup_checked` | 322 + 163 | 27 + 29 | 480 |
| `Pair.Allowedips.lookup_checked` | 473 + 163 | 27 + 29 | 480 |
| *Trial* `T4.add_empty_root` | 353 + 161, and 95 new | 23, and 18 new | 1,589 |
| *Trial* `T3.counter_window` | about 145 in all, 108 new | | 143 |

The other twelve finished headlines (the `_simulation` and `first_return`
siblings and three frame results) fall within the same ranges. Every
headline also mentions 950 lines of Kraken declarations and 2,000 to 5,300
lines of the mirror, most of it the state types.

| Union | Assumed | Claimed beyond assumed |
| --- | ---: | ---: |
| 26 finished headlines, `binary/` + `TrustBase` | 1,668 + 499 | 261 + 12 |
| the same, image terms and layout constants | 828 + 62 | 0 |
| Added by the 23 component theorems and mentioned by no finished headline | 661 hand-written, 1,109 image | |

| Family, in landing order | New hand-written lines | of which assumed | New image lines | Instructions |
| --- | ---: | ---: | ---: | ---: |
| First lookup and its transports | 903 | 871 | 243 | 138 |
| Paired index lookup, removal, replacement, sequences | 638 | 495 | 189 | 66 |
| Paired index insertion and mixed sequences | 447 | 388 | 157 | 109 |
| Allowed-IPs lookup | 443 | 413 | 239 | 176 |

Not in any of these counts, and all of it assumed: the nine Kraken patches
(1,914 patch lines) and the rest of Kraken; `objdump` and the generators
behind the image terms; the facts `TrustBase.lean` records in comments and
not as premises (stable text, no GS use).

What the premises are. A finished headline assumes one decoder agreement
per image it steps through; the callback contracts, which the
`first_return` and `from_image` siblings discharge for the index family and
which stay hypotheses, in a second form, for the allowed-IPs lookup; the
serialization and permission premises; for insertion the random provider's
return contract and input coupling; a precondition that is an executable
check returning `ok`; and an accepted run of the mirror function. The check
is where most of the assumed lines are, and it contains the relation.

The owner's objection, tested. A wrong relation cannot hide behind a
simulation proof only to the extent something consumes it:

- *Index family: held.* The relation is a total decoder of the table, the
  entries and the reference counts against a fixed projection of the
  mirror's device that cannot drop an object (`PairMemory.lean:117-144`).
  Lookup's conclusion fixes `rax` and the output slot to the addresses of
  the mirror's answer (`PairLookupAdequacy.lean:11-15`); the sequence
  theorems feed each mutator's relation to later lookups whose answers are
  those register values (`PairSequenceFrame.lean:59-63`); the frame's write
  set is the table, the 32-byte entries and the 4-byte counts, not whole
  objects (`PairIndexStorage.lean:7-10`). A relation too weak to determine
  a later lookup would fail those proofs.
- *Allowed-IPs lookup: held* in the same way, through the returned pointer.
- *Allowed-IPs insertion: not yet.* No landed theorem feeds an insertion's
  relation to a lookup. The relation is the lookup's, which is some
  assurance, and it is run on captured states as tests.
- *What a proof never polices.* A relation or precondition that is too
  strong: every simulation proof checks against an unsatisfiable `Pre`. The
  witnesses police that, for the constructed states they cover, and the
  captured-state replays, which are tests. General reachability from a
  kernel entry is open (landing obligation F7), and so is a common `fetch`
  for the several decoder agreements a sequence theorem takes together.

Where a landed headline says less than it appears to, as far as I looked:
`SerializedEnvironment` (nothing); the removal's answer in a sequence
(`True`, there being no return value); the sequences' calls, which are
joined by a re-prepared entry state and claim no caller instruction; the
allowed-IPs lookups on a dying peer, where the mirror refuses and the
theorem is silent; `Return.add_checked` and `Return.wrapper_checked`, which
are epilogues and not function results. Each is stated somewhere in the
package's own documents. I found no relation weak enough to make a finished
headline misleading.

What the definition leaves for a reader to judge beyond the two kinds: the
evidence that the assumed part is true of the kernel, which is not text in
either kind but runs (the byte comparison of the image terms with the ELF,
the instruction tests of the patches, the captured-state replays), with
which of them were run for which commit; and the domain of the accepted-run
premise, which is inside the mirror and decides where each theorem is
silent.

## 4. Verified, inferred, not checked

**Verified by running or reading the thing itself:** everything in section
1; the statements quoted in H2, M1 and M2; the measurements of H1 and
section 3.

**Inferred:** that the allocation sites of `add()` are armed in the
oracle's ordinary runs (from the closing record's mention of allocator-site
arming and the mirror's `allocNode190`, `205`, `234` records; I did not run
the oracle). That the internal node's initialization would take hours (from
its instruction mix as the worker's log describes it, and the size of the
landed leaf initialization). The classification of headlines into finished
and component, by name; `findNode_checked` and `RandomService.return_recorded`
are counted as components.

**Not checked:** joint satisfiability of any trial's hypotheses; the helper
lemmas inside the trial proofs beyond compilation and axioms; whether T3's
two reject exits and its `validate` agree with the C beyond the trial's own
mirror link; the token counts; the workers' unrecorded estimates; a fresh
compilation of `binary/` (outputs were replayed); the external `lake check`;
the package's executed suites and captures; Kraken against any other model;
`kmem_cache_free`; static keys in the proved ranges; the proof tree's
placement theorems beyond their existence; the RefinedC route.

## 5. Reproduction

In a worktree of main with the built package (the reassessment's
"Reproduction" section), and the trial sources from `task/binary-trials`
copied to `.tmp/trials`:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
LP=$(cd binary && ../scripts/in-bundle lake env printenv LEAN_PATH)
# one trial module, dependencies of the same directory first
(cd .tmp/trials/t4 && mkdir -p build && \
  cap ../../../scripts/in-bundle env LEAN_PATH="$LP:$PWD/build" lean -o build/T4Main.olean T4Main.lean)
```

The surface measurement: a Lean file that imports `binary/surface.py`'s
`IMPORTS`, and for each name in its `HEADLINES` runs

```lean
let (p, c) ← forallTelescope ci.type fun xs body => do
  let mut p : Array Name := #[]
  for x in xs do
    let t ← inferType x
    if ← isProp t then p := p ++ t.getUsedConstants
  pure (p, body.getUsedConstants)
```

then, for every constant reachable from those roots through
`ConstantInfo` (type and value of definitions, type and constructors of
inductive types, nothing of theorems), prints its module
(`env.getModuleIdxFor?`) and `findDeclarationRanges?`. Run it with
`cap ../scripts/in-bundle lake env lean <file>` in `binary/`; the closures
per headline and the line sums are then a few lines of Python over that
graph. The split of the printed file is by the first `def`/`structure`
line and the `TRUST DECLARATIONS` line of `TrustSurface.expected.txt`.

The allocator: the `objdump` command in H2 on the s5 `vmlinux`
(`binary/kernel-identity-s5.txt`), and
`grep -n '__kcov_alloc_pre' -A36 kernel/patches/choice-stream.patch`.
