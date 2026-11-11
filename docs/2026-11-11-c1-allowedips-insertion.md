# C1, the compiled allowed-IPs insertion: closing report

2026-11-11, branch `task/binary-c1`. Result C1 of the binary track is
closed: `Binary.Statements.C1.Proof.signed : Signed`, with no hypothesis,
on the standard three axioms. The statement is revision 4 of the
[final statement](2026-11-10-c1-final-statement.md) as put to the owner.
**No revision of the statement has been signed by the owner; revision 4
is signed at the landing.** The [independent landing review](2026-11-11-review-c1-landing.md)
says to land with named changes to documents and records; section 9 has
their dispositions. Every judgement here is the integrator's [AGENT] unless it
says otherwise.

## 1. What is proved

`binary/C1Signed.lean`:

```lean
theorem signed : Signed := signed_of_referenced_and_witness referencedHolds witnessHolds
```

The statement, verbatim from `binary/StatementC1Vacuity.lean` and
`binary/StatementC1Headline.lean`:

```lean
def Signed : Prop :=
  Headline ∧ Witness ∧ InsertThenLookup ∧ FailedInsertInvisible

def Headline : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    ∃ Inv : World → Mem 64 → Prop,
      Initial L A Inv ∧ Framed L Inv ∧ Referenced L Inv ∧
      InsertStep fetch L A Inv ∧ LookupStep fetch L Inv
```

In words. For every decoder, layout and allocator state that meet the
premises there is a relation between the mirror's world and machine memory
that (`Initial`) holds at a physically empty table with the allocator idle;
(`Framed`) does not depend on memory outside the heap; (`Referenced`)
survives one reference on a registered peer being taken (with the mirror's
`peerGetMaybeZero` returning the peer) or dropped from a count above one
(with the mirror's `peerPut`); (`InsertStep`) is carried by every call of
`wg_allowedips_insert_v4/_v6` that meets the caller's conditions and that
the mirror's `Leanux.WG.insert` accepts, the machine returning to the
caller with the mirror's answer in `eax`, the table's sequence word
advanced, and memory changed only in the stack window, the coverage buffer
and the heap; and (`LookupStep`) is carried by every such call of `lookup`,
which returns the address of the mirror's peer or NULL. The insertion's
nine paths are all inside: over-long prefix, empty root with and without
memory, exact match, child attachment, node allocation refused, covering
node, intermediate node, and the second allocation refused with its
rollback and release.

`Witness`: one decoder, layout and allocator meet every premise with the
image's own callbacks, run four calls from an empty table (`Executed`), and
have a service that uses its stack and writes the coverage buffer
(`ServiceActive`). `InsertThenLookup`: at an empty table whose allocator
will succeed, an insertion returns 0 and every later lookup of the key
returns that peer's address. `FailedInsertInvisible`: where the allocator
will refuse, the insertion returns `-ENOMEM` and every later lookup returns
NULL. The full text of every clause is in the final statement (section 2
and appendix A) and in `binary/TrustSurface.expected.txt`.

Closure of the statement (constants outside Lean's own libraries, by
declaring module; `binary/Statements/C1/measure-surface.py`):

| Statement | Total | C1 statement files | Binary package | Kraken | Mirror |
| --- | --- | --- | --- | --- | --- |
| `Signed` | 1013 | 58 | 378 | 188 | 389 |
| `Headline` | 993 | 44 | 372 | 188 | 389 |
| `Premises` | 542 | 20 | 331 | 187 | 4 |

Printed in the trust surface for C1: 808 lines (1 headline line, 454
assumed, 353 claimed, of which 75 are the generated callback listing).

## 2. What is assumed

`Premises fetch L A` (`StatementC1Headline.lean`), nine fields:

| Field | What it assumes |
| --- | --- |
| `insertion`, `lookup`, `peer` | The decoder returns the committed decoded terms of the six WireGuard functions (the two wrappers, `add`, `lookup`, `common_bits`, the peer helper). Decoder agreement with the ELF is tested, not proved |
| `tracePc`, `callbacks`, `cmp1`, `constCmp4`, `bhEnable` | The landed contracts of the coverage callbacks and of BH-enable. In the witness these are the image's own code, proved from its terms |
| `allocator` | `AllocatorContract fetch L A`, below: the code at the two service addresses, whatever it is |

The contract in full (`StatementC1Contracts.lean`), with the definitions it
is stated in:

```lean
structure Separated (L : Layout) (A : Allocator) (c : CommonBitsCoverage.Context) (s : MachineState) : Prop
-- (four conjuncts: the service's stack apart from the arena and from the coverage bytes, the
--  coverage bytes apart from the arena, the buffer apart from the coverage metadata and the
--  preemption count)

def AllocResult (L : Layout) (A : Allocator) (live : List Nat) (record : HiddenRecord)
    (stream : List HiddenRecord) (t : MachineState) : Prop :=
  let a := t.data.regs.rax.toNat
  (record.bytes.head? = some 0 → a = 0 ∧ A.Idle t.data.dmem live stream) ∧
  (record.bytes.head? = some 1 →
    a ≠ 0 ∧ a % 8 = 0 ∧ a + nodeSize < 2^64 ∧
    (∃ span ∈ L.arena, span.1 ≤ a ∧ a+nodeSize ≤ span.1+span.2) ∧
    (∀ other ∈ live, disjointRanges a nodeSize other nodeSize = true) ∧
    readNat t a nodeSize = .ok 0 ∧ A.Idle t.data.dmem (live ++ [a]) stream)

structure AllocatorContract (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) : Prop where
  frame : ∀ m m' live stream, A.Idle m live stream →
    (∀ a, L.Arena a → ¬Kept live a → m.get? a = m'.get? a) → A.Idle m' live stream
  alloc : ∀ (c : CommonBitsCoverage.Context) (s : MachineState) (ra : UInt64) live record stream,
    s.pc = allocEntry → EntryFrame s ra → ServiceReady L A c s →
    s.data.regs.rdi.toNat = L.cache → s.data.regs.get (.low .rsi .W32) = 0xdc0#32 →
    (ra.toNat, record.site) ∈ allocSites → A.Idle s.data.dmem live (record :: stream) →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧ EqualOutside (ServiceWrites L A c s live) s.data.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ AllocResult L A live record stream t) s
  free : ∀ (c : CommonBitsCoverage.Context) (s : MachineState) (ra : UInt64) live stream,
    s.pc = freeEntry → EntryFrame s ra → ServiceReady L A c s → ra.toNat = freeSite →
    s.data.regs.rdi.toNat = L.cache → s.data.regs.rsi.toNat ∈ live →
    A.Idle s.data.dmem live stream →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧
      EqualOutside (ServiceWrites L A c s (live.erase s.data.regs.rsi.toNat)) s.data.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ A.Idle t.data.dmem (live.erase s.data.regs.rsi.toNat) stream) s
```

`ServiceReady` is the coverage state valid, a positive capacity when the
buffer is needed, the direction flag clear, `A.depth` mapped bytes of stack
scratch, and `Separated`. The outcome of an allocation is tied to the
record the mirror consumes: the contract's `Idle` carries the pending
records, which is foreknowledge of the allocator's answers.

Beside the premises, each step assumes the caller's conditions, which are
executable checks on the entry state: `insertReady` (the wrapper's entry,
the table, the address bytes, a non-NULL registered peer, the `node_cache`
word, the stack window apart from every peer object, and `frameReady`: ABI
return word, mapped stack, valid coverage state, capacity, direction flag,
and the separations of heap, stack, buffer, metadata and preemption count)
and `lookupReady`. `Initial` assumes `emptyTable`, the mirror's three
allocation sites armed, and a pending record list of allocation records
for those sites only. The semantic base is Kraken at the ten-patch pin
`96d48487` and the trust declarations of `binary/TrustBase.lean`.

## 3. What is not claimed, and what is accepted knowingly

From the final statement (its sections 7 and 8) and the statement review:

1. **Closed-world from an empty table.** The invariant is hidden, so the
   conclusion holds only along sequences of insertions, lookups, changes
   outside the heap, and a registered peer's reference taken or dropped by
   one as `Referenced` says. Peer creation or removal between insertions is
   outside: a `wg set` or `wg setconf` that creates its peers and gives
   them allowed addresses in one message is covered for its first peer
   only. A later result on removal or the dump replaces this one; it cannot
   extend it. The world is closed on the mirror's side too: `Initial` and
   the relation the proof exhibits require the mirror to be armed at the
   three allocation sites and its whole pending record list to consist of
   allocation records for those sites (`StatementC1Headline.lean:159-162`).
   So the headline is silent about a mirror world with any other hidden
   record pending, at the empty table or later, as in a differential run,
   and about an unarmed mirror. The tests, the witness and the capture's
   checker use constructed worlds with allocation records only.
2. **Nothing is claimed of the kernel's allocator.** The result is about
   the six WireGuard functions against any code at the two service
   addresses that meets the contract. The image's allocator is not shown to
   meet it, and under this semantic base it cannot (the final statement's
   appendix C: its instructions and its writes outside the arena).
3. **Parent pointers, the peers' node lists and the internal nodes' list
   heads are not claimed.** Nothing with an observable conclusion reads
   them.
4. **A single-CPU, coverage-instrumented image and a sequential model**:
   one CPU stepping these instructions alone, on the saved s5 build with
   KCOV callbacks. Nothing carries to an SMP build.
5. **Decoder agreement is tested, not proved**; at the two service
   addresses the guest does not run the ELF's bytes at three sites.
6. **The caller's conditions are not proved of any real call.** The capture
   shows them at 20 calls. The over-long-prefix exit is not reachable from
   the real caller; the NULL-peer exit is outside.
7. **Where the mirror refuses, the claim is silent**: a trie deeper than
   its bound, a lookup that would retry on a dying peer, a peer with a
   pending worker, a short record list, reference-count saturation.
8. **The mirror's definition of an accepted run is inside the claim**: 389
   declarations of the closure, not in the printed line counts.
9. **The witness is IPv4 only and takes three of the nine insertion paths**
   (empty root, intermediate node, rollback) and a lookup hit. That an
   allocator with ordinary mapped state can meet the contract is argued
   (`StateWord.lean`) and tested (the test service), not shown by a checked
   witness (landing review, N1).
10. **One paragraph of `Signed`'s docstring describes consequences by
    argument, not clauses**: "About how the compiled code uses that service
    it establishes that …". The proposed rewording is put to the owner
    with the signature, below; the statement file is not changed (N2).
11. **The landed definitions the statement draws in are not in the text
    put to the owner nor in the printed surface**: `Context` with `At`,
    `CoverageAt`, `Needed`, `writes`, `bytes`, `metadataBytes`
    (`binary/CommonBitsCoverage.lean:9-36`); `Trie.coverageCheck`,
    `coverageDataCheck` and the span lists (`PairLoopCheck.lean`,
    `PairCallCheck.lean:12-50`); `spansApart` (`PairSpan.lean:10`) and
    `disjointRanges` (`PairMemory.lean:27`); `InRange` and `EqualOutside`
    (`Memory.lean:34-39`); `instructionStep` (`Execution.lean:25`);
    `readNat`, `Trie.address`, `AllowedipsEntry.TotalWrites`; Kraken's
    `Eventually`. The reviewer read each and found nothing but what its
    name says (N4).
12. **"Every later lookup" in the two exclusions means the next lookup**,
    from any state that agrees with the insertion's final state on the
    heap (`LookupAfter`): a lookup that finds a peer raises its count, a
    heap word, so a second lookup is not such a state. Sequences are the
    headline's business (N7).

For item 10, the change proposed for the owner's decision at the signature,
to the docstring of `Signed` in `binary/StatementC1Vacuity.lean`. It is not
applied; a docstring change alters no Lean term, and the trust surface
prints no docstring.

```diff
 contract; the image's allocator is not shown to, and under this semantic
-base cannot be**. About how the compiled code uses that service it
-establishes that the code calls it only with the cache and the flags the
+base cannot be**. About how the compiled code uses that service the
+following are not clauses of the statement but consequences by argument
+(the theorem holds for every service that meets the contract, so the
+compiled code cannot depend on what the contract leaves open): the code
+calls it only with the cache and the flags the
 contract names and from states the contract covers; relies on nothing about
```

The witness's artificial aspects, as its prover reports them. The witness
shows that the premises are not vacuous; it is not a model of a kernel.

- The service at `allocEntry` is a stub: package 4's twelve-instruction
  body with `push %rdi; call __sanitizer_cov_trace_pc; pop %rdi` in front.
  It keeps its one mutable byte between two unmapped bytes, a leftover of
  the contract before revision 3 that an ordinary design would not need;
  removing it was not attempted.
- The code at `freeEntry` is a bare `ret`: nothing is reused.
- The buffer write happens only in PC mode with room in the buffer.
- Between the four calls of `Executed`, each next entry state takes its
  heap bytes from the previous final memory and every other byte from one
  base memory: the stack and the coverage buffer are reset between calls.
- The `ServiceActive` state is not one an insertion is shown to reach
  (the statement allows this since revision 3).
- The calls return to an address outside every listing.
- The mirror's four runs go through a text copy of the mirror's `add` with
  a loop-free allocation, proved equal to the mirror's `add`; a change to
  `Leanux.WG.add` therefore breaks the build. Memory reads are moved to
  list functions before `decide +kernel`, which adds no axiom.

## 4. The statement's history

1. Statement packet ([packet](2026-11-10-statement-packet-c1-insertion.md)),
   no proofs, with executed tests.
2. The [statement review](2026-11-10-review-statement-packet-c1.md) found
   three defects before any proof: a conforming service could overwrite
   nodes it had handed out, so the headline was unprovable (H1: resolved by
   `Kept` in `ServiceWrites` and `frame`); the contract promised a return
   from states where no stack-using code can return (H2: `ServiceReady`);
   the witness did not pin the callbacks to the image's code (F1:
   `CallbacksFromImage`). At commissioning the choices were left to the
   coordinator's recommendation, with the final text to be put to the
   owner before any proof is accepted [AGENT, coordinator, 2026-11-10,
   `docs/decisions.md`]; revision 2, with F1 repaired, was the text the
   proof started from. It was not signed.
3. The proof found four more. Top of memory: `AllocResult` admitted an
   object ending at 2^64, which the landed interpretation refuses (the
   bound added, revision 3). The contract excluded every allocator with
   ordinary internal state, through a coverage context aliased to it
   (`ServiceReady.separated`, revision 3). The witness was unprovable as
   shaped, because the headline's steps conclude about final states only
   (restated as `Executed` and `ServiceActive`, revision 3). A stack window
   inside a peer object met the caller's conditions and broke the landed
   node-initialization boundary (`c1.stack-peers` in `insertReady`,
   revision 4).
4. Two changes came from the owner's decision and the review of revision 3:
   the closed world admits the caller's reference on an existing peer
   (`Referenced`, revision 3), and the take is paired with
   `peerGetMaybeZero`, the operation `set_peer` performs (revision 4).
   Each decision is in `docs/decisions.md` [USER 2026-11-10].
5. Revision 4 is the text put to the owner; the three findings that are
   checkable by elaboration stay as regression files
   (`binary/Statements/C1/proof/TopOfMemory.lean`, `StateWord.lean`,
   `StackOffPeers.lean`).

## 5. The proof's shape and size

One accepted insertion is described once on the source side as a pure step
model (`C1Step`) with an invariant (`C1Invariant`); the compiled code is
nine paths, meeting at two service rules derived once from the contract
and at one machine cut inside `add` (`add+0x156`, in its strengthened form
`TrunkToNodePlus`, `C1Cut`). `C1Assembly` and `C1Joined` join the parts;
`C1Joined` pins each interface proposition to its theorem with a type
ascription.

| Part | Modules | Lines | Elapsed agent time | Helpers |
| --- | --- | --- | --- | --- |
| Statement (`StatementC1*.lean`) | 4 | 645 | | |
| Invariant, step model, interfaces, cut, assembly, join, result (`C1Invariant`, `C1Step`, `C1Interfaces`, `C1Cut`, `C1Assembly`, `C1Joined`, `C1Signed`) | 7 | 963 | | |
| Package 1, the source side (`C1Source`) | 1 | 3,612 | about 31 minutes | |
| Package 2, the trunk and the paths above the placement (`C1Trunk*`) | 43 | 8,476 | about 68 minutes, then 37 | forked helpers |
| Package 3, the paths below the cut (`C1Below*`) | 107 | 17,223 | about 62 minutes | forked helpers |
| Package 4, the service rules and callbacks (`C1Service*`) | 15 | 1,962 | about 49 minutes | |
| The reference clause (`C1Referenced`) | 1 | 223 | about 6 minutes | |
| The witness (`C1Witness*`) | 6 | 1,613 | about 32 minutes | forked helpers |

180 proof modules, 34,072 lines; with the statement, 184 and 34,717.

**Where a landing reviewer should look.** Packages 2 and 3 and the witness
relied on forked helpers whose intermediate lemma statements their provers
only spot-read. In the witness, `C1WitnessContract.lean` and
`C1WitnessMemory.lean` were helper-written and read by their prover at the
headline statements only. What the kernel checked is that the stated
theorems follow; whether an intermediate lemma says something odd on the
way is not otherwise reviewed. The integration made eight mechanical
repairs for revisions 3 and 4 (positional and argument changes), moved the
two packages' copies of the strengthened cut to `C1Cut`, removed three
interface propositions that nobody proved (the three paths from the bare
cut), and renamed one clashing helper; the commits say which.

No file of the result carries a resource raise or a linter suppression.

## 6. Validation

On the integrated head; the Lean content is that of commit `842e9339`, and
the commits after it change documents only. `scripts/in-bundle` resets
`PATH`, so every heavy command was wrapped whole in `capped`.

| Check | Command | Result |
| --- | --- | --- |
| Clean full build of the binary package | `binary/.lake/build` and the private Kraken's `.lake/build` removed, then `capped -m 80G -- scripts/in-bundle lake -d binary build` | 1321 jobs, completed, no warning; every module of the package and of Kraken compiled from source (1191 "Built" lines, none replayed). The mirror's own build directory was not removed; it was never seeded |
| `signed` | `#print axioms signed` in that build | `propext`, `Classical.choice`, `Quot.sound` |
| Forbidden constructs | text scan of `binary/C1*.lean`, `StatementC1*.lean` and `binary/Statements/C1/**.lean` for `sorry`, `axiom`, `admit`, `native_decide`, `decide +native`, `ofReduceBool`, `trustCompiler`, `skipKernelTC`, `unsafe`, `implemented_by`, `extern`, `set_option`, `maxHeartbeats`, `maxRecDepth`, `nolint`, `linter.` | none (three hits are the English word "admit" in comments). `decide +kernel` is used (in packages 3 and 4 and in the witness) and adds no axiom |
| Binary gate | `capped -m 48G -- scripts/in-bundle /usr/bin/python3 scripts/binary-proof-gate` | PASS: pin `96d48487` clean, build 1321 jobs, 75 terminal statements on the standard axioms (74 before, `signed` new), surface diff PASS, no forbidden token |
| Bridge gate | `capped -m 24G -- scripts/in-bundle /usr/bin/python3 scripts/c2-bridge-gate` | PASS: `C2Bridge` built (130 jobs), 5 theorems on the standard three axioms, the two statements equal to the expected text; lag report: four modules at `b32bb164`, mirror at `1b7a3b70`, register names `218d3ffd` |
| Mirror build | `capped -m 24G -- scripts/in-bundle lake build` | 66 jobs, completed |
| Unit tier | the `unittest` line of AGENTS.md, wrapped in `capped` | 149 tests, OK (1 skipped) |
| Statement tests and the three regression files | `capped -m 24G -- binary/Statements/C1/run-tests.sh` | PASS, exit 0, about 25 minutes; output identical to revision 4's run. `TopOfMemory`, `StateWord` and `StackOffPeers` elaborate, their theorems on the standard axioms. 23 searches hold (the baseline over 108 insertions and 486 lookups, the others over 36 and 168 each, 23 distinct mirror decisions), the two closed-world runs hold with 21 reference steps between calls, `ServiceActive` holds of the test service and fails of the quiet one, and each refused variant is refused |
| The insertion's own terms against the ELF, by hand | `capped -m 8G -- scripts/in-bundle /usr/bin/python3 -B binary/generate_allowedips_mutation.py --check` | "AllowedipsMutationImage.lean: checked", with its two layout files: the committed terms of `wg_allowedips_insert_v4`, `_v6` and `add.isra.0` |
| Callback listing against the ELF, by hand | `capped -m 8G -- scripts/in-bundle /usr/bin/python3 -B binary/generate_c1_callbacks.py --check` | "StatementC1CallbackImage.lean: checked" |
| Capture checks on the five kept captures | `Check.lean` and `summarise.py` on the raw captures in `.tmp/c1` | 73 lines of `Check.lean` output over five traces (40, 6, 9, 9, 9), byte-identical to revision 4's run; the summary identical, 60 kinds of check all ok, no problem listed |
| One trace re-recorded and re-captured under the ten-patch pin | `capped -m 24G -- binary/Statements/C1/capture/run-capture.sh alloc:a2_allowedips_split_nomem`, with the earlier recording and capture set aside | exit 0, fresh guest boot, capture stamped Kraken `96d48487`; 2 insertions, 3 allocations (one slow path, one forced NULL), 1 release; 58 kinds of check all ok, `PROBLEMS []`. Against the nine-patch capture of the same trace the nine lines of `Check.lean` output differ in one field only, the count of bytes changed inside two service calls (704 against 709, 269 against 270), which varies between boots |
| Kernel replay export | `capped -m 48G -- ../scripts/in-bundle lake env leanexport C1Signed` | exit 0; 30,374,720 lines, 1,783,858,960 bytes |
| Kernel replay inside nono, the checker's own sandbox on | from `binary/`: `capped -m 48G -- ../scripts/in-bundle sh -c 'PATH="$PATH:/usr/bin" COMPARATOR_BWRAP=/usr/bin/bwrap exec lake check --from-export ../.tmp/c1-check.ndjson'` | exit 0 in about four and a half minutes: "Lean default kernel accepts the solution", axioms `propext`, `Quot.sound`, `Classical.choice`, no sandbox-disabled banner. A diagnostic: the gate is the owner's run outside nono. An earlier run with `--inadvisably-no-sandbox` gave the same verdict in about 5 minutes |

The capture's recordings were made under the nine-patch Kraken
(`43df9468`). No guest was booted for the recheck of the five kept
captures. One trace was then recorded and captured again from a fresh
guest boot under the ten-patch pin, as the last row says.

The tests, the capture tooling and the three regression files are not
built by a gate: like C2's statement tests, they are by-hand claim-point
checks, documented here and in the final statement's appendix B.

The kernel replay proper is the owner's, outside the sandbox. From the
root of a checkout of the source being checked whose `.deps/kraken` is the
bootstrapped ten-patch checkout (`binary/run.py --bootstrap-only`; the main
checkout's `.deps/kraken` is the unpatched upstream clone and the build
fails there):

```sh
capped -m 48G -- scripts/in-bundle lake -d binary build        # from the source being checked, immediately before the export
cd binary
capped -m 48G -- ../scripts/in-bundle lake env leanexport C1Signed > ../.tmp/c1-check.ndjson   # exit 0 required
capped -m 48G -- ../scripts/in-bundle sh -c 'PATH="$PATH:/usr/bin" COMPARATOR_BWRAP=/usr/bin/bwrap exec lake check --from-export ../.tmp/c1-check.ndjson'
```

Both settings in the last line are needed, and the single quotes matter
(`PATH` must expand inside the bundle): `lake check` looks for its sandbox
helper with `which`, which is in `/usr/bin` and not on `in-bundle`'s
`PATH`; and the `bwrap` that `in-bundle` stages must not be the one used
where unprivileged user namespaces are restricted by path, so
`COMPARATOR_BWRAP` names the system one (`/usr/bin/bwrap` on the devboxes;
where it lives is a box matter). "Lean default kernel rejected the
solution" directly after a `bwrap` error line is the sandbox failing to
start, not a kernel verdict. And "the kernel accepts the solution" says
nothing about what `signed` states: the gate's surface comparison is what
checks that. `binary/README.md` has the same block for C2's roots.

## 7. Open items

1. The owner's signature on revision 4 and the merge approval; the
   coordinator records them in `docs/decisions.md` when they are given.
2. The external kernel replay of the export (the block above).
3. `StatementC1Vacuity.lean`'s docstring on `Signed` begins "WHAT IS
   SIGNED": the statement files are left exactly as put to the owner, and
   the docstring becomes true at the signature.
4. The witness's stub keeps a shape revision 3 made unnecessary (section 3).
5. The trust surface prints the definitions of the C1 statement files; the
   package definitions they draw in that were not already printed
   (`spansApart`, the coverage checks, `EqualOutside` and others, about 210
   lines) are not printed, following what was done for C2.
6. Only one of the five captures was re-recorded under the ten-patch pin.
7. Removal, the dump and the walk-by-peer are not started; by item 1 of
   section 3 a result on them replaces this one.

## 8. How to reproduce

From the worktree root, with the package bootstrapped (`binary/README.md`),
the saved s5 image for the image tests and the capture, and a host Python
with pyelftools:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
cap scripts/in-bundle lake -d binary build
cap scripts/in-bundle /usr/bin/python3 scripts/binary-proof-gate
cap scripts/in-bundle /usr/bin/python3 scripts/c2-bridge-gate
cap scripts/in-bundle /usr/bin/python3 -B binary/generate_allowedips_mutation.py --check   # the terms of the two wrappers and add
cap scripts/in-bundle /usr/bin/python3 -B binary/generate_c1_callbacks.py --check
cap scripts/in-bundle /usr/bin/python3 -B binary/allowedips_mutation.py      # writes the tests' input
cap binary/Statements/C1/run-tests.sh                                        # the three regression files, then the tests; about 25 minutes
cap binary/Statements/C1/capture/run-capture.sh                              # boots guests; about 10 minutes
cap scripts/in-bundle /usr/bin/python3 -B binary/Statements/C1/measure-surface.py
```

## 9. Dispositions of the landing review's findings

The [independent landing review](2026-11-11-review-c1-landing.md)
(`6a70659d` on `task/review-c1-landing`, of this branch at `6d712422`):
land with named changes, all to documents and records, none to the Lean.
One commit per finding; no Lean file and no gate changed.

| Finding | Disposition | Commit |
| --- | --- | --- |
| S1. The record of the signature | Fixed, as corrected by the coordinator, whose wording the error was: no revision of the statement has been signed by the owner. The closing report, the final statement and its index row say so; in `docs/decisions.md` the commissioning bullet reads "is to be signed" and the two revision entries say "C1's statement". The entry recording the owner's signature and merge approval is not added here: the coordinator adds it when they are given (open item 1) | `736d0c5a` |
| S2. The closed-world condition on the mirror's side | Fixed: stated in section 3 item 1 and section 2, in the register row and in the README row | `b23c8419` |
| S3. The ELF check of the insertion's own terms | Fixed: `generate_allowedips_mutation.py --check` is in the README's image checks and in this report's validation table and reproduction block; run once, three files checked | `e295a33f` |
| S4. A stale sentence in the README | Fixed | `d06ae8af` |
| S5. Two reproduction slips | Fixed: `measure-surface.py` creates `.tmp/c1`; the replay block is relative to the checkout's root and says which checkout | `39fa3c77` |
| N1. What the witness covers | Stated in section 3, item 9 | `5a5ba2ee` |
| N2. The docstring of `Signed` | Stated in section 3, item 10, with a proposed rewording as a diff for the owner's decision at the signature; the statement file is unchanged | `5a5ba2ee` |
| N3. `Premises.peer` also fixes `wg_index_hashtable_lookup`'s terms | No change asked. Answered here: "six functions" in the documents is the set the claim is about; the decoder premise says more, a true fact of the image checked by `generate.py --check` and unused by the proof's paths | |
| N4. What the printed surface does not print | Stated in section 3, item 11, with the reviewer's file references; open item 5 stands | `5a5ba2ee` |
| N5. The captures' Kraken stamp | No change asked. Section 6 says which captures were recorded under which pin and that one was re-recorded | |
| N6. `HeadlineExplicit` is closed too | No change asked. Not registered and not claimed, by the decision to keep the relation out of the claim; `explicit_of_for headlineFor referencedHolds` proves it if a later result wants it | |
| N7. "Every later lookup" is the next lookup | Stated in section 3, item 12 | `5a5ba2ee` |
| N8. Speed | No change asked | |

After these changes the binary gate was run once on the final head, wrapped
in `capped`: PASS (build 1321 jobs, 75 terminal statements on the standard axioms, surface diff PASS, no forbidden token).
