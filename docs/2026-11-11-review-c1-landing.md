# Independent review: landing result C1, the compiled allowed-IPs insertion

Reviewed: branch `task/binary-c1` at `6d712422` (the whole branch is main
`bc287764..6d712422`: 105 commits, 7 of them merges, 207 files, +40,121
lines), in my own worktree `.worktrees/review-c1-landing` on
`task/review-c1-landing`. Inputs read: the closing report and the final
statement on the branch, the decisions of 2026-11-10 and the track's rules
of 2026-10-14, the statement packet and its review with the sections on
revisions 3 and 4 (`task/review-c1-statement` at `27707e7d`), the four
statement files in full with the package definitions they mention,
`C1Signed`, `C1Joined`, `C1Assembly`, `C1Invariant`, the interface
propositions, `C1Referenced`, the witness (`C1Witness`, `C1WitnessStub`,
`C1WitnessScene`, the stub of `C1ServiceStub`), the mirror's `insert`, `add`,
`lookup`, `peerGetMaybeZero`, `peerPut` and `hiddenAlloc`, the kernel source
lines the statement cites, the capture appendix and its checker, the merge
of main, the surface registration, `binary/README.md` and the register row.
Judgements are mine [AGENT, reviewer].

## Verdict

**Land with named changes.** The result is what it says it is. The closed
theorem `Binary.Statements.C1.Proof.signed` has the type
`Binary.Statements.C1.Signed`; the Lean shown to the owner in the final
statement is the text of the four statement files, which have not changed
since the commit the statement's reviewer confirmed; I rebuilt all 184 C1
modules from source and the closure is accepted on the three standard
axioms by the build, by the gate, and by the replay checker run as a
diagnostic. I found no way in which the theorem means less than its type,
and nothing in the statement that is vacuous or weaker than the documents
say. The limits are stated where a reader meets them first, with one
omission (S2).

The named changes are all to documents and records, none to the Lean:

- **S1, before or with the merge**: the record of the owner's signature.
  The branch's documents say the owner signed revision 2 and cite an entry
  that the log itself attributes to the coordinator; the same wording was
  withdrawn for C2. One entry at the landing should say what the owner
  signed and when.
- **S2 to S5, at the owner's choice**: one limit missing from the lists a
  reader meets first; the ELF check of the insertion's own instruction
  terms missing from the documented checks; one stale sentence in
  `binary/README.md`; two small reproduction slips.
- The owner's kernel replay outside the sandbox, as the closing report
  asks.

## Checks run

All in my worktree, heavy jobs through `capped` (48G or less), each
wrapped whole. Build outputs (`.lake`, `binary/.lake`, `.deps`) were copied
from the reviewed worktree; what was recompiled here is said below.

| Check | What I did | Result |
| --- | --- | --- |
| Kraken pin | `git -C .deps/kraken rev-parse HEAD` in the copy; the gate's own pin check | `96d484872c2c438a4d02f47e6390507f587a095c`, equal to `TrustBase.krakenCommit`; clean tree. Copied, not reconstructed from upstream (the C2 landing review did that for the same pin) |
| Build of the C1 modules | Deleted every build output of `C1*` and `StatementC1*` (1,472 files), then `capped -m 48G -- scripts/in-bundle lake -d binary build` | 1321 jobs, exit 0. Compiled here: 184 modules (the 180 proof modules and the 4 statement modules), about 220 CPU-seconds in all, the largest `C1BelowCoverMachine` at 28 s. Replayed from the copy: the rest of the package and Kraken. `signed` on `propext`, `Classical.choice`, `Quot.sound`. No warning from a C1 file |
| Binary gate | `scripts/binary-proof-gate` | PASS: pin, 1321 jobs, 75 terminal statements on the standard three, surface diff PASS, no forbidden token |
| Bridge gate | `scripts/c2-bridge-gate` | PASS: five theorems on the standard three, the two statements equal to the expected text; lag report `b32bb164`, `1b7a3b70`, `218d3ffd`, as the closing report has it |
| The type of the result | a scratch file: `example : Headline ∧ Witness ∧ InsertThenLookup ∧ FailedInsertInvisible := signed` with every name fully qualified; `#check @signed` | elaborates; `signed : Signed`. `TrustSurface.expected.txt` line 1592 pins `Binary.Statements.C1.Proof.signed : Binary.Statements.C1.Signed` and line 4646 prints `Signed` |
| Shown text against the files | every Lean block of the final statement split into declarations and searched in the four statement files, whitespace-normalised | 57 of 59 found verbatim. The two others: a fragment shown with an ellipsis, and `AllocatorContract`, shown without its one inner doc comment (equal once comments are removed). Of the files' declarations only `Related` and `HeadlineExplicit` are not shown, and they are not part of `Signed` |
| Statement files since the reviewed revision | `git diff 2110573b HEAD -- binary/StatementC1*.lean` | empty: the files are those of revision 4 as the statement's reviewer confirmed it; no proof commit touched them |
| Image terms against the ELF | `generate.py --check`, `generate_allowedips.py --check`, `generate_allowedips_mutation.py --check`, `generate_c1_callbacks.py --check` on `.artifacts/kernel-net-choice-s5` | all "checked": `Image`, `ServiceImage`, `AllowedipsImage` (lookup 103 instructions, `common_bits` 73), `AllowedipsMutationImage` (the two wrappers and `add.isra.0`), the callback listing, and the layouts |
| Addresses in the statement | `nm` and `objdump -d` of the saved image, read beside `StatementC1Contracts.lean` | `allocEntry`, `freeEntry` and `cacheWord` are `kmem_cache_alloc_noprof`, `kmem_cache_free` and `node_cache`; `add.isra.0` calls the allocator exactly three times, each with `mov $0xdc0,%esi` and the cache loaded from `node_cache`, returning to `…0d04`, `…0e52`, `…0ff2` (the statement's `allocSites`), and the release once, returning to `…1252` (`freeSite`). Its other call targets are `__sanitizer_cov_trace_pc`, `_cmp1`, `_const_cmp1` and `common_bits` |
| Statement tests and the three regression files | `binary/allowedips_mutation.py`, then `binary/Statements/C1/run-tests.sh` | PASS, exit 0, about 17 minutes; 58 lines, identical to the kept output of revision 4's run. The three regression files elaborate on the standard axioms; 23 searches hold (the baseline over 108 insertions and 486 lookups, 23 distinct mirror decisions in each), the five refused variants are refused, the two closed-world runs hold with 21 reference steps, `ServiceActive` holds of the test service and fails of the quiet one |
| Capture checks | `Check.lean` on the five kept captures (inputs copied from the reviewed worktree's `.tmp/c1`), under this build | exit 0 on each; 40, 6, 9, 9 and 9 lines, byte-identical to the kept outputs |
| Surface measurement | `binary/Statements/C1/measure-surface.py` (after creating `.tmp/c1`: S5) | the closure counts of the closing report: `Signed` 1013 (58, 378, 188, 389), `Headline` 993, `Premises` 542 |
| Kernel replay, diagnostic | from `binary/`, the two lines of `binary/README.md` for C1: `lake env leanexport C1Signed`, then `lake check --from-export` with `PATH` and `COMPARATOR_BWRAP` set as written there | export exit 0, 30,374,720 lines, 1,783,858,960 bytes, the report's figures exactly; "Lean default kernel accepts the solution", axioms `propext`, `Quot.sound`, `Classical.choice`, no sandbox-disabled banner; about five minutes. Inside nono, so a diagnostic. Export deleted |
| The alternative headline | a scratch theorem `HeadlineExplicit := explicit_of_for headlineFor referencedHolds` | elaborates on the standard three: the form with the relation in the conclusion is closed as well, in one line (N6) |
| Mutants, each built and reverted | (A) in `allocSites`, the record sites of the return addresses `…0d04` and `…0e52` exchanged (78 and 79); (B) in the callback listing, `movzbl %sil,%edx` changed to `movzbl %dil,%edx` | (A) build fails in `C1TrunkNode.lean:392` (`decide` finds `((Add.entry + 324), 78) ∈ allocSites` false), `C1BelowAlloc.lean:279` and `C1Source.lean:1685`. (B) build fails at `C1ServiceCallbackCmp1.lean:83`. The proofs depend on the pairing of return sites with the mirror's record sites and on the listed terms |
| Mirror and proof tree untouched | `git diff bc287764 6d712422 -- Leanux` | empty. Against main the branch modifies seven files only: `binary/README.md`, `binary/TrustSurface.expected.txt`, `binary/lakefile.toml`, `binary/surface.py`, `docs/README.md`, `docs/decisions.md`, `docs/proofs.md`; everything else is added |
| After the proof | `git diff 842e9339 HEAD --stat` | documents only, as the closing report says |

Not run: a guest (no trace was recorded or captured again by me); the
mirror build and the unit tier (no mirror file changed); the whole proof
gate (the proof tree is main's); a clean build of the landed package and of
Kraken (replayed from the copy); the replay outside the sandbox, which is
the owner's. Taken from the report and not checked: the elapsed times of
the packages, the whole-RAM comparisons of the capture (the dumps are
deleted as they are compared), the re-recording of one trace.

## What I conclude about the proofs, and how

The packages were written fast and by many hands, and their intermediate
lemmas were read by nobody in full. I did not read them in full either,
and for the claim it is not needed. `signed` takes no hypothesis and its
axioms are the standard three, so every device between the statement and
the instructions (the invariant, the step model and `StepFacts`, the cut
with `CutExtra`, the interface propositions, the service rules, the
copies of mirror text) is inside one kernel-checked term. If one of them
were trivially true, or had a hypothesis nothing meets, the theorem that
uses it would still have to produce `Signed` at its stated type, and could
not. An interface proposition weaker than its name is a defect of the
description, not of the result. What can be wrong while everything checks
is the statement, the reading of the image, and the semantic base, and
that is where I looked.

- **Nothing outside the statement files can change what the statement
  means.** The four files import landed modules only
  (`PairAllowedipsMutation`, `AllowedipsRootRecord`,
  `PairAllowedipsLookupAdequacy`, `LiteralDecode`); no landed Lean file is
  modified on the branch; the proof modules are imported by the statement
  files nowhere, so no instance or notation of theirs is in scope where the
  statement is elaborated. `Signed` in `theorem signed : Signed` resolves to
  `Binary.Statements.C1.Signed` (the gate prints it qualified); there is no
  second definition of any statement name.
- **The statement, read with its definitions.** In my words. *Assumed*, for
  a decoder `fetch`, a layout `L` and an abstract allocator state `A`: that
  `fetch` returns the committed terms of the two wrappers, `add.isra.0`,
  `lookup`, `common_bits`, `wg_peer_get_maybe_zero` (and, through the same
  premise, `wg_index_hashtable_lookup`: N3); that the coverage and
  BH-enable callbacks meet their landed contracts; and that whatever is at
  the two service addresses, called as `add` calls it from a state with
  valid coverage data, mapped stack and the stated separations, returns
  with the callee-saved registers kept, writes only its scratch, the arena
  outside live nodes and the coverage buffer, and answers as the mirror's
  next pending record says, with a fresh, aligned, zeroed 72-byte object in
  the arena on success. *Claimed*: a relation between the mirror's world
  and memory exists that holds at every physically empty table where the
  allocator is idle with the mirror's records pending; depends on heap
  bytes only; survives one reference on a registered peer taken or dropped
  with the matching mirror operation; and is carried by every call of
  either wrapper and of `lookup` that meets the caller's executable
  conditions and that the mirror accepts, the machine provably reaching the
  return address on every path and for every undefined value (`Eventually`
  is Kraken's least fixed point and `Effects.All` is false on a fault, an
  unimplemented instruction and a missing decode), with the mirror's answer
  in `eax` or the mirror's peer's address in `rax`, the sequence word
  advanced, and memory unchanged outside the stated write sets. Because the
  relation is hidden, what a reader can use is the observable part: results
  along a sequence that starts at an empty table. The two exclusions are
  that reading for one step, stated without the relation.
- **The existential over the invariant is not a way out.** `Initial` forces
  the relation to hold of real states (the witness exhibits one such state
  for one `fetch`, layout and allocator), `InsertStep` and `LookupStep`
  conclude observables, and the proof's `Inv` is `Related` by definition
  (`C1Invariant.lean:37`), the landed executable relation.
- **Mirror acceptance is not a narrow hypothesis.** From a state the
  relation holds of, `Leanux.WG.insert` is refused, as far as I can read it, only when a
  needed record is missing, of the wrong site or malformed, or at the depth
  bound, which a key of at most 128 bits cannot reach. (I read this off the
  mirror's text; I did not prove it.) Read against `allowedips.c:181-250`
  and `:281-301` in the pinned source, the mirror's `add` and `insert`
  follow the C branch for branch, and the lines the statement cites for the
  reference clause (`netlink.c:386`, `:421`, `:486`, `peerlookup.c:68`) say
  what it says they say.
- **`Source.lookup` is the mirror's.** `Binary.Source.lookup` is
  `liftWG (WG.lookup …)` (`SourceAdapter.lean:55`), not the logged copy of
  the same name in `AllowedipsSource.lean`.
- **The return sites are checked by the proof, not only by reading.** The
  contract's `alloc` clause asks for `(ra, record.site) ∈ allocSites`. The
  proof has to supply that at each call with the actual return address and
  the record the mirror is about to consume, so a wrong pairing of a return
  site with a mirror record site would have left the theorem unprovable.
- **Copies of mirror text.** `hiddenAllocCopy` is tied to the mirror by
  `hiddenAlloc_copy : ∃ P, ∀ s, AmbientM.hiddenAlloc s = hiddenAllocCopy P s`,
  proved by `rfl` (`C1Source.lean:422`); the witness's `addFree` by a proved
  equation with the mirror's `add` (`C1WitnessMirror.lean:108`). Either way they are inside the closed term.
- **`decide +kernel`.** In packages 3 and 4 and the witness only (84 lines
  in 17 files), each a closed decidable fact evaluated by the kernel; no
  `Lean.ofReduceBool` in the axioms of anything.
- **Rendering or object.** The tests and the capture's contract clauses are
  renderings, as the documents say. They no longer carry the claim: the
  theorem quantifies over the propositions themselves. Where the evidence
  bears on something no proof covers (that real calls meet the caller's
  conditions), the capture evaluates the statement's own `emptyTable`,
  `insertReady` and `lookupReady`, which are executable, on captured states.
- **The instruction terms.** The proofs reach the image only through the
  decoder-agreement premises, whose terms the generators compare with the
  ELF; all four checks pass here. On the 20 captured calls Kraken, executing
  those terms from the captured entry state, visits the guest's instruction
  addresses and ends in the captured return state under both seeds; I
  reran that check under this build.
- **The merge of main and the tenth Kraken patch.** The merge (`4cc606de`)
  resolved two conflicts by union (the lakefile's roots, `docs/decisions.md`)
  and takes main's version of everything C2 landed; against main the branch
  changes no C2 file, no Kraken patch, no gate script and not AGENTS.md.
  Patch ten adds one `Operation` constructor (`bts`) with its parser,
  printer and semantics; none of the images C1 executes contains a `bts`,
  so the semantics of every instruction on C1's paths is what it was under
  nine patches. The bridge gate passes on the merged tree.

## Findings

### Should fix before or with the landing

**S1. The record of the signature.** The closing report (lines 7 and 204)
and the final statement (line 4) say as fact that the owner signed revision
2, the first citing `docs/decisions.md` with a [USER] tag. The entry they
rest on is the commissioning entry of 2026-11-10, which says that the
remaining choices were left to the coordinator's recommendation and are
[AGENT, coordinator]; "C1 is signed as `Signed` of revision 2" is one of
those bullets. The same group's line for C2 was later withdrawn as
premature by the C2 landing entry, and now reads "to be signed"; C1's still
reads "is signed". The two entries the branch adds are tagged [USER] and
speak of "C1's signed statement" while recording that it is being revised.
The closing report's open item 3 notices the wording and leaves it to the
coordinator. Whether the owner signed revision 2 only the owner knows; the
log as it stands does not attribute that act to him, and two documents
about to land say it does. Fix, at the landing: one [USER] entry recording
what the owner signed (revision 4: the four statement files as of
`fa4277bb`, unchanged at the head) and the merge approval, as was done for
C2; the commissioning bullet and the two revision entries worded as the C2
line was; the first paragraph of the closing report and of the final
statement, and the register row's "whose signature is given at the
landing", brought into line. The docstring "WHAT IS SIGNED" on `Signed`
becomes true at that point and needs no edit. Severity: medium, as a
matter of provenance; it does not touch the result. This is the C2 landing
review's S3 again.

### At the owner's choice

**S2. One closed-world condition is missing from the lists a reader meets
first.** `Initial` asks that the mirror world be armed at the three sites
and that its whole pending record list consist of allocation records for
those sites (`StatementC1Headline.lean:159-162`), and `Related` carries the
same conjunct, so it holds along every sequence. The packet said so twice
(its section 3: the mirror's pending records are allocation records for the
three sites and nothing else, from the start). The closing report's section
3, the register row and the README row do not; the closing report's
section 2 mentions only that the sites are armed. The consequence is worth
one sentence: the headline is silent about the mirror world of a
differential run in which any other hidden record is pending at the empty
table or later, and about an unarmed mirror; the worlds of the tests, the
witness and the capture's checker are constructed ones with allocation
records only. Severity: low; a line in the closing report's item 1 and in
the register row.

**S3. The ELF check of the insertion's own terms is in no documented list.**
`binary/generate_allowedips_mutation.py --check` compares the committed
terms of `wg_allowedips_insert_v4`, `_v6` and `add.isra.0` with the saved
image. `binary/README.md`'s block of image checks (lines 228-234) lists six
generators and the new callback listing, not this one; the closing report's
validation table and reproduction block name the callback check only. It
passes (`AllowedipsMutationImage.lean: checked`, with its two layout
files). "Decoder agreement is tested, not proved" is the result's stated
limit; the test for the three functions the result is about should be
among the commands a reader is given. Severity: low; one line in each
list.

**S4. A stale sentence.** `binary/README.md:254-256` still ends "full
insertion remains open", in the paragraph on the earlier mutation
experiment, under a table whose C1 row says insertion is closed. Severity:
low.

**S5. Two reproduction slips.** (a) `binary/Statements/C1/measure-surface.py`
writes `.tmp/c1/Surface.lean` without creating the directory and fails with
`FileNotFoundError` in a worktree where the capture has not run; with the
directory present it reproduces the report's counts. (b) The closing
report's replay block begins `cd /home/dev/projects/lean-ux-proto/.worktrees/binary-c1`:
a box path, and a worktree that is to be removed once the branch lands;
`binary/README.md` has the same commands without it. Severity: low.

### Notes (no change asked)

**N1. What the witness covers.** It does its job. `Premises` is met by a
decoder that holds the image's own WireGuard functions and callbacks and a
stub at the two service addresses; `Executed` is derived from the
headline's steps at that decoder, from a concrete empty table, with the
mirror's four runs evaluated; `ServiceActive` is the stub's own run. So
the readings it is there to exclude are excluded: premises nothing meets,
an allocator never idle, caller conditions no state meets, a mirror that
accepts nothing, a contract only a silent service could meet. The closing
report's list of artificial aspects is fair and I found each in the code
(the state byte at `0xa00001` with `Idle` asking that its neighbours be
unmapped; `ret` at `freeEntry`; `over` resetting everything but the heap
between calls; `serviceEntry` a state of its own; the return address
`0xffffffff82000000`). Three things to add to it:
- The four calls are IPv4 and take three of the nine insertion paths (empty
  root, intermediate node, rollback) and a lookup hit. "Each kind of call"
  in the `Witness` docstring means those. For the exact match, the child
  attachment, the covering node, the two other allocation failures, the
  over-long prefix and the IPv6 wrapper, that the hypotheses can be met
  rests on the tests (interpreted) and on the capture, where the
  statement's own `insertReady` holds at real entries of both wrappers.
- The weakness conceded in revision 3 (a service active only at states no
  insertion reaches) is a weakness of what is stated, not of this stub: its
  first three instructions (`push %rdi; call __sanitizer_cov_trace_pc; pop
  %rdi`) run on every call, the six inside `Executed` included.
- That revision 3's contract can be met by a service whose state has
  ordinary mapped neighbours is argued (`StateWord.lean`) and tested (the
  test service), not shown by a checked witness. The closing report's open
  item 4 says as much.

**N2. The docstring of `Signed` says more than its clauses in one
paragraph.** "About how the compiled code uses that service it establishes
that …" (calls only with the named cache and flags, relies on nothing else
about an object, releases exactly the node it allocated, once). None of
these is a clause. Each is a consequence by argument: the theorem holds
for every service that meets the contract, so the compiled code cannot
depend on what the contract leaves open. The argument is sound as far as I
can see, and the register row does not repeat the paragraph.

**N3. One more function's terms are assumed than the six named.**
`Premises.peer` is `AnchoredDecoderAgreement`, which fixes `Image.fetch`:
`wg_peer_get_maybe_zero` and also `wg_index_hashtable_lookup`
(`0xffffffff813a0670`), milestone 1's function. It is a true fact about the
image (`generate.py --check`) and unused by the proof's paths; "six
functions" in the documents is the set the claim is about, not the whole of
what the decoder premise says.

**N4. What the printed surface does not print.** The 808 added lines print
every definition of the statement files and the callback listing. Not
printed, and not shown in the final statement either, are the landed
package definitions the statement draws in (about 210 lines by the
measurement). A reader needs these to read `ServiceReady`, `Separated`,
`frameReady` and the write sets: `CommonBitsCoverage.Context` with `At`,
`CoverageAt`, `Needed`, `writes`, `bytes`, `metadataBytes`
(`CommonBitsCoverage.lean:9-36`); `Trie.coverageCheck`, `coverageDataCheck`
and the span lists (`PairLoopCheck.lean`, `PairCallCheck.lean:12-50`);
`spansApart` (`PairSpan.lean:10`) and `disjointRanges`
(`PairMemory.lean:27`); `InRange` and `EqualOutside` (`Memory.lean:34-39`);
`instructionStep` (`Execution.lean:25`); `readNat`, `Trie.address`,
`AllowedipsEntry.TotalWrites`; and Kraken's `Eventually`. I read each; none
says anything other than its name, and each is as it is on main. `Returned`,
`EntryFrame` and the decoder-agreement and callback-contract definitions
are printed already. The closing report's open item 5 states the omission.

**N5. The captures' Kraken stamp.** Four of the five kept captures carry
the nine-patch commit in their metadata. A capture is registers and memory
of a guest running natively; Kraken enters only when `Check.lean` executes
the terms from the captured entry state. That check, rerun here under the
ten-patch build, gives byte-identical output on all five, and patch ten
touches no instruction on these paths. What the capture shows is as the
appendix says: at 20 real calls the caller's conditions hold, the compiled
functions under Kraken reproduce the guest, and the answers are the
mirror's; for the image's allocator the evaluable clauses hold for an arena
drawn after the fact around every byte it changed. What it does not show:
`Idle`, `frame`, anything about gaps in which other kernel activity changes
those bytes, anything concurrent.

**N6. `HeadlineExplicit` is closed too.** `explicit_of_for headlineFor
referencedHolds` proves it in one line on the standard axioms. The branch
neither registers nor claims it, which matches the decision to keep the
relation out of the claim; the owner may want to know that the stronger
form is there if a later result wants it.

**N7. "Every later lookup" in the exclusions is the next lookup.**
`InsertThenLookup` and `FailedInsertInvisible` conclude about every lookup
entered from a state that agrees with the insertion's final state on the
heap (`LookupAfter`). A lookup that finds a peer raises its reference
count, a heap word, so a second lookup is not such a state: the exclusions
speak of whichever lookup comes next, from any caller frame, not of all
lookups from then on. (Sequences are the headline's business, through the
hidden relation.) The docstrings and the closing report say "every later
lookup"; the Lean is clear, the prose is slightly wider than it.

**N8. Speed.** The 184 modules compile in under two minutes of wall time
on this host because they are glue over the landed component theorems (the
closing report's "what the proof is built from" in the README row). Nothing
in that is suspicious; I mention it because the build's brevity surprised
me before I looked.

## Compliance

- Mirror and proof tree: untouched (`git diff bc287764 6d712422 -- Leanux`
  is empty). No gate script, AGENTS.md or kernel file changed against main.
- Provenance: every one of the 105 commit messages carries an [AGENT] or
  [USER] tag; the two [USER] decision entries are paraphrase. S1 is the one
  place where an act is attributed more firmly than the log supports.
- Quoted text: I found no quotation of the owner in the branch's documents
  or commit messages.
- Resource raises and suppressions: none in `C1*.lean`, `StatementC1*.lean`
  or `binary/Statements/C1/` (the one `set_option` is `format.width` in the
  measurement script's generated file).
- No new gate; the tests, the capture tooling and the regression files are
  by-hand claim-point checks, as documented.

## To the signer

What you are asked to sign is `Signed` in `binary/StatementC1Vacuity.lean`
with the three files it rests on, as printed in sections 2 and appendix A
of the final statement. I checked that print against the files
declaration by declaration, and the files against the revision your
statement reviewer confirmed: they are the same text.

In one paragraph: for any code at the two allocator addresses that behaves
as the contract says, the compiled `wg_allowedips_insert_v4`, `_v6`, `add`,
`lookup`, `common_bits` and `wg_peer_get_maybe_zero` of the s5 image, run
one call at a time on one CPU from an empty table, always return, return
what the mirror's `insert` and `lookup` return, and write nothing outside
their stack window, the coverage buffer and the allowed-IPs heap. The
theorem is closed and kernel-checked, and I could not make it mean less
than that.

What to hold in mind while signing, most of it already in the closing
report's section 3:

1. It is a statement about six functions against a contract, not about the
   kernel's allocator, and the image's allocator cannot meet the contract
   under this semantic base. The capture is the evidence that the contract
   describes what the real allocator does at these calls; it is evidence,
   not a premise discharged.
2. It is closed-world, on both sides. On the machine: only these calls,
   changes outside the heap, and a reference on an existing peer taken or
   dropped. On the mirror: only the matching operations, and a record list
   holding nothing but allocation records for the three armed sites (S2).
   A `wg set` that creates its peers is covered for its first peer only.
3. The caller's conditions are assumptions about every real call. They are
   executable and hold at the 20 captured calls; nothing proves them of the
   kernel's callers.
4. The witness is a stub, IPv4 only, three paths and a lookup (N1). It
   rules out the vacuous readings; it is not a model of anything.
5. The definitions that give `c.At`, `c.Needed`, `c.writes`, `c.bytes`,
   `spansApart`, `EqualOutside` and `instructionStep` their meaning are not
   in the text put to you nor in the printed surface (N4). They are short
   and I found nothing odd in them; if you read one, read
   `binary/CommonBitsCoverage.lean:9-36`.
6. One paragraph of the docstring on `Signed` describes consequences that
   are argued, not stated (N2).

My advice: sign revision 4 as it stands, and have the signature recorded
in `docs/decisions.md` as yours at the landing (S1). The remaining gate is
your kernel replay outside the sandbox, from a tree built from the merged
source; `binary/README.md` has the commands without the worktree path.
