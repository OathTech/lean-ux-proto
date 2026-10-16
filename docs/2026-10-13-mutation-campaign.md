# The mutation campaign: the check's reach measured, 2026-10-13

The first audit under the user's direction of 2026-10-13 (fidelity, audits
and the census's gaps while the proof campaign runs): mechanical mutants of
the mirror, each one edit at one line, run against the differential check on
the s2 oracle. A mutant the check rejects shows which channel catches that
kind of mistake; a mutant that survives is a finding on the check's reach:
an arm no trace exercises, an operand nobody declared, a comparison the
checker never makes, or an edit that is genuinely equivalent. The sixteen
sentinels of `scripts/wg-mutants.py`, `pipes-mutants.py` and
`seccomp-mutants.py` stay the claim-point speedbump; this campaign measures
the whole mirror once and says which survivors should become sentinels or
traces.

Provenance: [USER 2026-10-13] fidelity improvements, audits and the census's
gaps are the mirror work while the proof campaign runs; the campaign's shape
(the classes, the sampling, the subsets) is [AGENT, fork of the coordinator].

## 1. The tool

`scripts/mutate.py` (run through `scripts/in-bundle`):

- `--list [--cap N] [--class C ...] [--file F ...]`: the deterministic
  enumeration of the committed tree, one line per mutant (a stable id, the
  file and line, the class, a note). The id is a hash of the file, line,
  class and original line, so it names the same edit on the same tree.
- `--show ID`: the edit as a two-line diff. `--apply ID --into WORKTREE`:
  apply it.
- `--run [...] --workers K --results FILE [--confirm-survivors]`: for each
  mutant, in a detached scratch worktree at `HEAD` (one per worker, the
  build copied once, `git checkout -- .` between mutants, the tree verified
  clean before and after), apply, build and check on the file's corpus
  subset, record the verdict. A survivor on a subset is rerun on the whole
  area suite before it counts when `--confirm-survivors` is given.
- `--summary` and `--report FILE`: the tables below from the results file.

Verdicts follow the sentinel scripts: `rejected` only when every failing
trace ends in a mirror-side outcome (`semantic_mismatch`,
`control_flow_mismatch`, `hidden_mismatch`, `mirror_invariant`,
`unsupported_path`) and nothing else; `survived` only on a clean pass;
`uncompilable` when the model build fails; anything else `no_verdict`, the
infrastructure's, never a rejection.

### The classes

| Class | The edit | What rejects it, if the check reaches it |
| --- | --- | --- |
| decision-negated | the outcome of a recorded decision (`branch`, `branchCmp`) negated: the arms swapped | control flow: the recorded outcome differs from the witness, or the other arm's path |
| condition-negated | a plain `if` with no decision negated | downstream: an observation, a later decision, a record out of order |
| comparison-operator | `≥`↔`>`, `≤`↔`<`, `==`↔`!=` at one comparison | the outcome at the boundary value, if a trace sits on it; the operands if declared |
| constant-off-by-one | a `def` constant or a literal in a condition, plus one | an operand comparison on a declared compare; otherwise only a trace at the boundary |
| early-return-removed | `then return ...` becomes `then pure ()`: the arm falls through | control flow or an observation after the fall-through |
| operand-swapped | a `branchCmp`'s two recorded operands exchanged, outcome kept | the operand comparison alone, and only where the two values differ |
| record-skipped | a hidden-input consumption replaced by a constant (`hidden`, `hiddenAlloc`) | hidden mismatch: the record is left unconsumed, or a later site reads the wrong record |
| stop-passthrough | `then unsupported "..."` or `then invariant "..."` becomes `then pure ()` | whatever the stopped path does next, if a trace reaches the stop |

Doc comments and line comments are skipped; `if let` and `if h :` are not
negated; a `branchCmpExcluded` is negated but its operands are not swapped
(the contract fixes them).

### The subsets

A mutant runs on the corpus that reaches its file (`SUBSETS` in the tool):
the WireGuard files on the `wireguard` suite's id prefixes of the stages
that exercise them (the sentinel scripts' subsets, widened), the FS files on
`pipes` and `handwritten`, the epoll files on `epoll`, `Leanux/Seccomp` on
`seccomp`, `Kernel/Signal.lean` on `pipes` and `seccomp`, the kernel
definitions, the environment model and the runner on `handwritten` plus the
`b1_`/`d3_` WireGuard stages. A subset choice can only make a rejection
harder, never easier, so a survivor is confirmed on its whole area suite.

## 2. The enumeration

The committed tree at main 2c7a076 yields 4,319 mutants:

| Class | Mutants |
| --- | ---: |
| decision-negated | 1,133 |
| constant-off-by-one | 934 |
| comparison-operator | 840 |
| condition-negated | 588 |
| early-return-removed | 430 |
| operand-swapped | 250 |
| stop-passthrough | 108 |
| record-skipped | 36 |

The largest files: `FS/Eventpoll.lean` 389, `FS/Pipe.lean` 356,
`Seccomp/Engine.lean` 198, `Seccomp/Filter.lean` 196, `Runner.lean` 182,
`WG/RxData.lean` 168, `Env.lean` 168. A run is a suite run, so the campaign
samples: `--cap N` keeps at most N mutants per file and class, evenly spaced
by line (cap 1: 296; cap 2: 551; cap 3: 769).

## 3. How the results are counted (power apart from presence)

A survival is not a missed defect unless the mutant changes behaviour the
check is supposed to see. The pre-release review (section 10) asks for the
population and the selection method first, then the counts in five
categories, and the survivors one by one. The categories:

- **Applicable semantic mutants:** the mutant changes what the mirror does
  on some input (a decision's path, a value an observation or a later
  decision depends on, a record's consumption), so a trace that reaches it
  can reject it. A survival here is a presence question: did the corpus
  reach the edit with a distinguishing input.
- **Equivalent projection mutants:** the mutant changes only what the
  mirror reports, not what it does, and the report is equal on every input
  the relation sees. The clear case is an operand swap at a comparison
  whose two operands are equal whenever the compare runs (`x == 1` with
  `x` always 1, `flags & MASK != 0` with the mask bits never set): the
  recorded pair is the same pair. Such a survival is not a missed defect
  and does not call for a trace; it is listed so the count is honest.
- **Uncompilable or invalid:** the model does not build, the mutated
  runner no longer prints parseable output (`invalid_output` on every
  trace), or the decision table is broken (a duplicate label). Not
  semantic mutants; counted apart.
- **No verdict or inconclusive:** an infrastructure outcome (a timeout, a
  busy slot, an environment failure), or a mutant whose rejection needs a
  scheduling opportunity the run did not contain. The second kind is
  distinguished from a survival the way the sentinel D2-M12 now is: the
  count of traces in the run that could have distinguished the mutant is
  given, and zero means inconclusive, not survived.
- **Confirmed survivors:** applicable semantic mutants that pass the
  subset and then the whole area suite. Each is explained; none is excluded
  because the corpus merely missed its boundary, since that is exactly the
  finding.

Two kinds of mutation are kept apart throughout: one that only corrupts
what the mirror logs (the recorded outcome of a decision the mirror does
not branch on, the operands of a comparison, a hidden record consumed as a
different value) and trips a hidden-record or operand mismatch with the
behaviour intact; and one that changes behaviour with the logging intact
(a negated condition, a removed early return, a constant off by one in a
path the mirror takes). The first measures the instruments; the second
measures the comparison. By class:

| Class | Changes behaviour | Changes the log |
| --- | --- | --- |
| decision-negated | yes (the other arm runs) | yes (the recorded outcome) |
| condition-negated | yes | no |
| comparison-operator | yes at the boundary value | yes where the compare is declared with operands (the outcome) |
| constant-off-by-one | yes at the boundary | yes where the constant is an operand |
| early-return-removed | yes | no |
| operand-swapped | no | yes (the recorded operands) |
| record-skipped | yes where the record's value steers a path (an allocation failure, a clock) | yes (the record is left unconsumed) |
| stop-passthrough | yes, on the stopped path only | no |
| order-swapped | no (both arms are tested either way) | yes (the decision order) |

## 4. The population and the selection

The population is the enumeration above: 4,319 single-line mutants of the
mirror at main 2c7a076 (the mirror files are byte-identical through
7ea0289, where the campaign ran), plus 34 two-line `order-swapped`
mutants added after the first pass. The sample is `--cap 1`: for every
(file, class) pair with at least one mutant, the one at the middle of the
file's list by line, deterministic, 308 mutants in all (296 of the eight
single-line classes and 12 order swaps). The cap is a budget choice, one
suite run per mutant at four to six minutes; it samples every file and
every class once, and it is blind to the second and later sites of a class
in a file. Each sampled mutant ran on its file's corpus subset
(section 1); a survivor on a subset ran again on its whole area suite, and
then, after the baseline census named the suites that take each
survivor's distinguishing outcome, on those suites too (section 6.8).

## 5. The counts

| File | Class | Generated | Uncompilable | Invalid | Rejected | Survived | No verdict |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Env.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `Env/Batch.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env/Batch.lean` | condition-negated | 1 | 0 | 0 | 0 | 1 | 0 |
| `Env/Batch.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env/Batch.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env/Batch.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `Env/IpStack.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `Env/IpStack.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env/IpStack.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env/IpStack.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `Env/IpStack.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `Env/Stack.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `Env/Stack.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Env/Stack.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `Env/Stack.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/AnonInodes.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/AnonInodes.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/AnonInodes.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Close.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Close.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Close.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Close.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Close.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventfd.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventfd.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventfd.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventfd.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventfd.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventfd.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventfd.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventfd.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/EventfdOps.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/EventfdOps.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/EventfdOps.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/EventfdOps.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/EventfdOps.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/EventfdOps.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/EventfdOps.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Eventpoll.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventpoll.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventpoll.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventpoll.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventpoll.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Eventpoll.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventpoll.lean` | order-swapped | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Eventpoll.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Eventpoll.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Fcntl.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Fcntl.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Fcntl.lean` | decision-negated | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Fcntl.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Fcntl.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Fcntl.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/File.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/File.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/File.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/File.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/File.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/File.lean` | operand-swapped | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/File.lean` | order-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/File.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/File.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/FileTable.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/FileTable.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/FileTable.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/FileTable.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/FileTable.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/FileTable.lean` | operand-swapped | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/FileTable.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/FileTable.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Fput.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Fput.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Fput.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Fput.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Inode.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Inode.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Inode.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Inode.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Inode.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Inode.lean` | operand-swapped | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Inode.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Open.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Open.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Open.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Open.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Open.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Pipe.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Pipe.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Pipe.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Pipe.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Pipe.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Pipe.lean` | operand-swapped | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Pipe.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Pipe.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/PipeCreate.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/PipeCreate.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/PipeCreate.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/PipeCreate.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/PipeCreate.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Poll.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Poll.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Poll.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Poll.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/ReadWrite.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/ReadWrite.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/ReadWrite.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/ReadWrite.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/ReadWrite.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/ReadWrite.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/ReadWrite.lean` | order-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/ReadWrite.lean` | stop-passthrough | 1 | 1 | 0 | 0 | 0 | 0 |
| `FS/Wait.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Wait.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Wait.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `FS/Wait.lean` | decision-negated | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Wait.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `FS/Wait.lean` | operand-swapped | 1 | 0 | 0 | 0 | 1 | 0 |
| `Kernel/Decision.lean` | comparison-operator | 1 | 0 | 1 | 0 | 0 | 0 |
| `Kernel/Decision.lean` | condition-negated | 1 | 0 | 1 | 0 | 0 | 0 |
| `Kernel/Defs.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `Kernel/Defs.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Defs.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Defs.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Defs.lean` | stop-passthrough | 1 | 1 | 0 | 0 | 0 | 0 |
| `Kernel/Refcount.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `Kernel/Refcount.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Refcount.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Refcount.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Refcount.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Refcount.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `Kernel/Signal.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Signal.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Signal.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Signal.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Signal.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `Kernel/Signal.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `Kernel/Signal.lean` | order-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `Runner.lean` | comparison-operator | 1 | 0 | 1 | 0 | 0 | 0 |
| `Runner.lean` | condition-negated | 1 | 0 | 1 | 0 | 0 | 0 |
| `Runner.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `Runner.lean` | early-return-removed | 1 | 0 | 1 | 0 | 0 | 0 |
| `Seccomp/Bridge.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Bridge.lean` | condition-negated | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Bridge.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Bridge.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Classic.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Classic.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Classic.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Classic.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Classic.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Classic.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Classic.lean` | order-swapped | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Classic.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Decisions.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Decisions.lean` | condition-negated | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Decisions.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Engine.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Engine.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Engine.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Filter.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Filter.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Filter.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Filter.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Filter.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Filter.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Filter.lean` | record-skipped | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Prefill.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Prefill.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Syscalls.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Syscalls.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Syscalls.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Syscalls.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Translate.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Translate.lean` | condition-negated | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Translate.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Translate.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Translate.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `Seccomp/Translate.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `Seccomp/Translate.lean` | order-swapped | 1 | 0 | 0 | 0 | 1 | 0 |
| `Syscalls.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `Syscalls.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `Syscalls.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `Syscalls.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `Syscalls.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/AllowedIps.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/AllowedIps.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/AllowedIps.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/AllowedIps.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/AllowedIps.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/AllowedIps.lean` | operand-swapped | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/AllowedIps.lean` | order-swapped | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/AllowedIps.lean` | stop-passthrough | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Blake2s.lean` | comparison-operator | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/Blake2s.lean` | condition-negated | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/Blake2s.lean` | constant-off-by-one | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/Curve25519.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Curve25519.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Curve25519.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Data.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Data.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Data.lean` | constant-off-by-one | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/Data.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Data.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Data.lean` | operand-swapped | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/Data.lean` | order-swapped | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Data.lean` | record-skipped | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Device.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Device.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Device.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Device.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Device.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Device.lean` | order-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Device.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Device.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Handshake.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Handshake.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Handshake.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Handshake.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Handshake.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Handshake.lean` | operand-swapped | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/Handshake.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Handshake.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Keypair.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Keypair.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Keypair.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Keypair.lean` | record-skipped | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Netlink.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Netlink.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Netlink.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Netlink.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/NetlinkDump.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/NetlinkDump.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/NetlinkDump.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/NetlinkDump.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/NetlinkDump.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/NetlinkDump.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/NoiseCrypto.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/NoiseCrypto.lean` | condition-negated | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/NoiseCrypto.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Peer.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Peer.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Peer.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Peer.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Peer.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Peer.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Peer.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Peer.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/PeerRemove.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/PeerRemove.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/PeerRemove.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/PeerRemove.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/PeerRemove.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/PrevQueue.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/PrevQueue.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/PrevQueue.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/PtrRing.lean` | comparison-operator | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/PtrRing.lean` | condition-negated | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/PtrRing.lean` | constant-off-by-one | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/Receive.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Receive.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Receive.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Receive.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Receive.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Receive.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Receive.lean` | order-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Receive.lean` | record-skipped | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Receive.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/RxData.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/RxData.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/RxData.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/RxData.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/RxData.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/RxData.lean` | operand-swapped | 1 | 1 | 0 | 0 | 0 | 0 |
| `WG/RxData.lean` | order-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/RxData.lean` | record-skipped | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/RxData.lean` | stop-passthrough | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Send.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Send.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Send.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Send.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Send.lean` | early-return-removed | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Send.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Send.lean` | order-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Send.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Socket.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Socket.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Socket.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Socket.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Socket.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Socket.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Socket.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/State.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/State.lean` | condition-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/State.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/State.lean` | early-return-removed | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/State.lean` | record-skipped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/State.lean` | stop-passthrough | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Timers.lean` | comparison-operator | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Timers.lean` | constant-off-by-one | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Timers.lean` | decision-negated | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Timers.lean` | operand-swapped | 1 | 0 | 0 | 1 | 0 | 0 |
| `WG/Types.lean` | comparison-operator | 1 | 0 | 0 | 0 | 1 | 0 |
| `WG/Types.lean` | constant-off-by-one | 1 | 0 | 0 | 0 | 1 | 0 |
| **all** | | **308** | **14** | **5** | **197** | **92** | **0** |

| Class | Generated | Uncompilable | Invalid | Rejected | Survived | No verdict |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| comparison-operator | 51 | 2 | 2 | 35 | 12 | 0 |
| condition-negated | 43 | 3 | 2 | 34 | 4 | 0 |
| constant-off-by-one | 51 | 3 | 0 | 35 | 13 | 0 |
| decision-negated | 36 | 0 | 0 | 34 | 2 | 0 |
| early-return-removed | 42 | 0 | 1 | 19 | 22 | 0 |
| operand-swapped | 27 | 4 | 0 | 18 | 5 | 0 |
| order-swapped | 12 | 0 | 0 | 7 | 5 | 0 |
| record-skipped | 18 | 0 | 0 | 13 | 5 | 0 |
| stop-passthrough | 28 | 2 | 0 | 2 | 24 | 0 |

| Channel | Rejections | Share |
| --- | ---: | ---: |
| hidden_mismatch | 65 | 32% |
| control_flow_mismatch | 53 | 26% |
| mirror_invariant | 20 | 10% |
| domain_filter | 18 | 9% |
| unsupported_path | 11 | 5% |
| semantic_mismatch | 11 | 5% |
| control_flow_mismatch,semantic_mismatch | 10 | 5% |
| control_flow_mismatch,mirror_invariant,semantic_mismatch | 2 | 1% |
| semantic_mismatch,unsupported_path | 1 | 0% |
| control_flow_mismatch,hidden_mismatch | 1 | 0% |
| control_flow_mismatch,semantic_mismatch,unsupported_path | 1 | 0% |
| control_flow_mismatch,hidden_mismatch,unsupported_path | 1 | 0% |
| hidden_mismatch,unsupported_path | 1 | 0% |
| control_flow_mismatch,mirror_invariant | 1 | 0% |
| hidden_mismatch,mirror_invariant | 1 | 0% |

Time per mutant: median 242 s, mean 572 s, total 48 h 58 min of worker time over 308 runs.


## 6. The survivors, one by one

Every mutant that passed its subset and its area suite, with its category:
**EP** an equivalent projection (what the mirror does is unchanged on every
input the relation sees, or the mirror cannot reach the edit on any
correct run); **LO** logging-only, the behaviour intact; **CB** a corpus
boundary, the edit changes behaviour on an input no trace supplies; **R**
a reach problem of the check itself, a changed behaviour no instrument
reports even when a trace takes the path. The fix class follows: a trace,
a declaration, a check rule, or nothing.

### 6.1 Operand swaps (logging-only by class)

The operand channel (`operands_match` in `evaluator/check.py`) matches a
non-constant `KCOV_TRACE_CMP` record in either operand order, because the
compiler canonicalises the order; a constant record needs the declared
variable on the mirror's left and the constant on its right. So a swap at
a non-constant compare is equivalent under the declared relation by
construction, and a swap at a constant compare is visible only when the
two values differ.

| Mutant | Site | Category | Why it survived | Fix |
| --- | --- | --- | --- | --- |
| m-0f81f80729 | `FS/Eventfd.lean:25` `flags & ~EFD_FLAGS_SET` vs 0 | EP | both values 0 on every trace (no invalid eventfd flag in the corpus) | none |
| m-10201516ff | `FS/EventfdOps.lean:33` `cid ≥ 0` | EP on this corpus | the freed context's id was 0 in every trace (one eventfd at a time) | a trace with two eventfds would distinguish it; still logging-only |
| m-805feb4dbd | `FS/Fcntl.lean:41` `(arg ^ flags) & O_APPEND` vs 0 | EP | both values 0: no trace toggles `O_APPEND` | none |
| m-123df34b8b | `FS/File.lean:53` `bitbit ≥ maxfd` | EP | non-constant compare, order-insensitive by the rule | none |
| m-8f9a03dc8d | `FS/FileTable.lean:38` `f_mode & FMODE_NOACCOUNT` vs 0 | EP | both values 0 | none |
| m-6c13ec73b6 | `FS/Inode.lean:139` `tv_sec ≥ s_time_max` | EP | non-constant compare (`sb->s_time_max` is a field) | none |
| m-965d2938de | `FS/Pipe.lean:136` `page_count == 1` | EP on this corpus | the count was 1 at every release (no shared page) | a trace sharing a page between two pipes; still logging-only |
| m-ca3da3a8f3 | `FS/Wait.lean:222` `busy_poll_usecs != 0` | EP | the compare is folded out of the oracle (`CONFIG_NET_RX_BUSY_POLL` off): no record exists | declare the decision branch-free |

### 6.2 Negated decisions

| Mutant | Site | Category | Why it survived | Fix |
| --- | --- | --- | --- | --- |
| m-1c99f9201d | `FS/Fcntl.lean:41` `.setflAppendChanged` | CB | no trace toggles `O_APPEND` through `F_SETFL`, so the compare's operands are 0 either way and the negated arm only runs the `IS_APPEND` test, false on pipefs; the outcome itself is unwitnessed in the built code (the `&&` shares its block) | a trace setting `O_APPEND` on a pipe end (operand 0x400, the arm's path) — fixed in 90bb2b8 (two distinct declared comparisons must match distinct kernel comparison PCs; the campaign's finding 2) |
| m-3fca1634a9 | `FS/Wait.lean:222` `.epBusyLoopOnUsecs` | LO | the outcome is discarded (`_ ←`) and the compare is folded out of the oracle, so neither a witness nor an operand record exists | declare the decision branch-free |

### 6.3 Skipped records

| Mutant | Site | Category | Why it survived | Fix |
| --- | --- | --- | --- | --- |
| m-2f50545f38 | `Seccomp/Filter.lean:463` `hiddenAlloc .kzallocSfilter` → always ok | CB | the kind-305 records are armed only in steered allocation traces, and the seccomp corpus has none: the seccomp sites of design 3.1 are declared but no `s_alloc_*` trace steers them | steered allocation-failure traces for seccomp's recorded sites (the epoll corpus has four such traces; the WireGuard and pipes corpora have the `alloc` suite) |

### 6.4 Stops made pass-through

An `invariant` stop guards the mirror against itself and fires on no
correct run, so removing it is unobservable by design. An `unsupported`
stop marks a path outside the domain; the domain filter keeps every corpus
trace off it, so removing it is invisible unless a trace reaches the path,
which is the definition of the documented exclusions. None is a missed
defect; the `unsupported` ones are the gaps the census lists.

| Mutant | Site | Stop | Category |
| --- | --- | --- | --- |
| m-0262fc1aa6 | `Env/IpStack.lean:111` | invariant: a TOS beyond a byte | EP |
| m-6d59b18f4f | `Env/Stack.lean:111` | invariant: `consume_data_done` trims to `tot_len` | EP |
| m-680f2828ab | `FS/EventfdOps.lean:106` | invariant: eventfd_write buffer shorter than 8 | EP |
| m-e5db213929 | `FS/FileTable.lean:112` | invariant: `d_alloc_pseudo` with a dentry | EP |
| m-ffb382ef8a | `FS/Inode.lean:113` | invariant: `iput` at `i_count` 0 | EP |
| m-43e133f4da | `FS/Pipe.lean:91` | invariant: `put_page` with no reference | EP |
| m-c6c585c607 | `Seccomp/Classic.lean:197` | invariant: a `JA` target past the end | EP |
| m-8f06f1ccd9 | `Env.lean:110` | unsupported: link-local source off loopback | EP (excluded) |
| m-baa08cd485 | `FS/Eventfd.lean:19` | unsupported: ida bitmap allocation at id ≥ 63 | EP (excluded) |
| m-7fcc53a2d9 | `Env/Batch.lean:109` | unsupported: NAPI polls of several peers in one softirq | EP (excluded) |
| m-56a8c05b80 | `FS/Eventpoll.lean:786` | unsupported: a positive `epoll_wait` timeout (tier 2) | EP (excluded) |
| m-580cff30a4 | `FS/Fcntl.lean:58` | unsupported: `f_op->check_flags` | EP (excluded) |
| m-e624aa0bb2 | `FS/File.lean:78` | unsupported: the kvmalloc fallback | EP (excluded) |
| m-623192681e | `Kernel/Refcount.lean:14` | unsupported: `refcount_warn_saturate` | EP (excluded) |
| m-b6965f47ab | `Syscalls.lean:223` | unsupported: `wg_netns_close` outside the fixture | EP (excluded) |
| m-69787d5726 | `WG/Device.lean:35` | unsupported: a lookup retry after a dying peer | EP (excluded) |

### 6.5 Negated conditions, changed operators, constants off by one

| Mutant | Site | Category | Why it survived | Fix |
| --- | --- | --- | --- | --- |
| m-ec0783b3a0 | `Env/Batch.lean:38` the NET_RX section ordinal, condition negated | **R** | its logical twin `w != .netRx` (m-f61392504a) was rejected by the placement-evidence check, while this one passed the subset and the whole suite with 15 inline placements present in the confirming run (`napi_orders`: a 94, bc 15); the placement evidence's sensitivity to the section ordinal depends on which placement runs occur | a check rule: the placement evidence should compare the section ordinals of the steps it replays, not only their control flow — fixed in 8340562: the operand relation on the main path is section-confined (a branch stamped with ordinal k matches only the guest's k-th `net_rx_action` block), on every trace, after the mirror's ordinal was made the guest's (it counted only the NET_RX sections it ran as a worker, not the loopback and flood-producer sections it skips; now every consumed section start counts). 4ca380f's narrow form (the placement evidence forced for every trace with open placements) did not reject this mutant: rx_counter_jump has no open placement, so the evidence never ran |
| m-d7dee84db8 | `Env/IpStack.lean:72` checksum fold negated | rejected (wireguard) | the environment's IP checksum is verified by the receive path on an injected datagram; survived `handwritten` only | none: resolved in 6.8 |
| m-ad789234b2 | `Env/IpStack.lean:72` `>` → `≥` at 0xffff | CB | the boundary value never occurs | none worth a trace |
| m-ab0b08a1e3 | `Env/Stack.lean:72` the TCP ack flag negated | rejected (wireguard) | the TCP helper is exercised by the stage traces; survived `handwritten` only | none: resolved in 6.8 |
| m-f40fbc343a | `Env/Stack.lean:46` `<` → `≤` | CB | boundary only | none |
| m-85b3373196 | `Env/Stack.lean:46` `+1` → `+2` | CB | the sequence increment feeds no observation inside WireGuard's boundary; the ack-flag mutant on the same helper was rejected, so the helper runs | none (outside the boundary) |
| m-9ffcb57df3 | `Env/IpStack.lean:22` `SENDER_PORT` + 1 | rejected (alloc, wireguard) | the injected datagram's source port is observed in those suites | none: resolved in 6.8 |
| m-133ab68446 | `FS/File.lean:60` `roundup_pow_of_two` negated | CB | `alloc_fdtable` runs only when the table grows past 64 descriptors, which no trace does; the wrong size would then reach `findNextFdAllFull`'s operand | a trace holding 65 descriptors |
| m-a0580e9458 | `FS/File.lean:60` `n ≤ 1` → `n ≤ 2` | CB | as above | the same trace |
| m-fa9da72d01 | `Kernel/Defs.lean:907` the allocation-site id map negated | rejected (alloc) | the armed allocation records expose the id map | none: resolved in 6.8 |
| m-bcac7274dc | `Kernel/Defs.lean:907` `58 ≤ i` → `58 < i` | CB | no steered trace targets site 58 exactly (`alloc` survived) | a steered trace at site 58 |
| m-cf6dab30c3 | `Seccomp/Bridge.lean:62` the repeatable mark negated | LO | the per-operation comparison is set-based, so emission multiplicity is invisible by design | none |
| m-208ec53979 | `Seccomp/Decisions.lean:281` `SDecision.all` filter negated | EP | the list is used by the tests, not on the checked path | none |
| m-04f699319f | `Seccomp/Decisions.lean:281` `==` → `!=` | EP | as above | none |
| m-a0c041a9cf | `Seccomp/Translate.lean:106` the 16-bit sign extension negated | CB | no corpus program converts a 16-bit immediate on that path | a trace with a negative 16-bit immediate |
| m-f095e17543 | `Seccomp/Translate.lean:55` `≥ 32768` → `> 32768` | CB | the boundary value | the same trace |
| m-2a64bed551 | `Seccomp/Translate.lean:55` 32768 → 32769 | CB | the boundary value | the same trace |
| m-62fabd29a0 | `FS/Fcntl.lean:43` `S_APPEND != 0` → `== 0` | CB | the line is inside the `O_APPEND`-changed block that no trace enters | the `O_APPEND` trace above |
| m-a863e3ebe4 | `FS/File.lean:55` `bitbit > start` → `≥` | CB | differs only at `bitbit == start` | none worth a trace |
| m-b42171750c | `FS/Inode.lean:114` `i_count > 1` → `≥ 1` | **R** | the last `iput` no longer evicts the pipefs inode and nothing notices: `fs/inode.c` is anchored only for its timestamp helpers, `iput_final`/`evict` have no declared decision, and no observation counts inodes; a mirror that leaks every pipe's inode passes | a declaration on `iput_final`'s path (fs/inode.c) or an observation of the inode count after close — fixed in a8cad18 (`iput` listed with `iput.last_reference` and `iput.lazytime_dirty` declared; the pipefs count decides it, `iputReport` elsewhere) with the trace `p_close_both_ends`, since no pipes trace closed both ends of a pipe inside its operations |
| m-9997959668 | `FS/Wait.lean:184` `ret < 0` → `≤ 0` | CB | the walk breaks after the first callback returning 0; every corpus wait queue has one entry at the walk | a trace with two waiters on one head |
| m-b47970fdce | `Kernel/Refcount.lean:12` `old > 0` → `≥ 0` | EP | differs only at `old == 0`, a use-after-free no correct run reaches | none |
| m-d6cb2b5d37 | `Syscalls.lean:173` `fd ≥ rlimit` → `>` | CB | no trace names exactly the limit's descriptor number | a trace at the boundary |
| m-6297bb9625 | `FS/AnonInodes.lean:22` `-ENODEV` → `-ENOTDIR` | CB | no steered trace fails the anon-inode allocation (`alloc` survived) | a steered trace at that site |
| m-d6e357a769 | `FS/Close.lean:21` `-512` → `-513` | EP (contract) | `ERESTARTSYS` from a pipe close needs a signal the harness never sends | none |
| m-cd402fd597 | `FS/Inode.lean:46` `NSEC_PER_SEC` + 1 | CB | the pipefs timestamps it feeds are never observed (no `fstat` in the corpus) and their compare is non-constant | a trace observing a pipe's `ctime` after a write |
| m-19762748d3 | `FS/Pipe.lean:40` `PIPE_MIN_DEF_BUFFERS` + 1 | CB | no trace reaches the soft pipe-buffer limit (`alloc` survived) | a trace under the soft limit |
| m-fbdcb07871 | `FS/ReadWrite.lean:18` `2^63` → `3^63` | EP (contract) | a count that large cannot be passed | none |
| m-261f7b4645 | `Runner.lean:17` `MAX_IO` + 1 | EP | a runner bound, not the C's | none |

### 6.6 Removed early returns

| Mutant | Site | Category | Why it survived | Fix |
| --- | --- | --- | --- | --- |
| m-545d3ed0ba | `Env/IpStack.lean:182` `-EMSGSIZE` | EP (contract) | no payload exceeds the fragment size | none |
| m-04f1275a2b | `FS/AnonInodes.lean:22` `.anonInodeErr` | CB | no steered trace fails the anon-inode allocation (`alloc` survived) | a steered trace at that site |
| m-5ee912dbd3 | `FS/Close.lean:13` `.closeNoFile` → `-EBADF` | CB | no trace closes an unknown descriptor | a trace: `close` of a never-opened fd |
| m-c94fc660c7 | `FS/Eventfd.lean:25` invalid flags | CB | no trace passes an invalid eventfd flag | a trace |
| m-0177f5cdad | `FS/EventfdOps.lean:76` a short eventfd read | CB | no trace reads an eventfd with fewer than 8 bytes | a trace |
| m-ad049b9b15 | `FS/Eventpoll.lean:90` a dead file at `ep_item_poll` | EP | unreachable on a correct run | none |
| m-9ec4b350ac | `FS/Fcntl.lean:43` `-EPERM` on `S_APPEND` | CB | inside the `O_APPEND` block no trace enters | the `O_APPEND` trace |
| m-e3cceef5de | `FS/FileTable.lean:109` `.allocPathPseudoFail` | rejected (alloc) | `a2_dentry_nomem` steers the failure | none: resolved in 6.8 |
| m-415d0346f2 | `FS/Inode.lean:96` `envOk .allocInode` | CB | no steered trace fails the inode allocation (`alloc` survived) | a steered trace |
| m-00693e433c | `FS/Open.lean:17` `filp_flush` at count 0 | EP | unreachable on a correct run | none |
| m-d070830a74 | `FS/Pipe.lean:101` `envOk .copyPageToIter` | CB | no steered trace fails the page copy (`alloc` survived) | a steered trace |
| m-18e6657307 | `FS/PipeCreate.lean:24` `.getPipeInodeNoInode` | CB | no steered trace fails `get_pipe_inode` (`alloc` survived) | a steered trace |
| m-057152dfc5 | `FS/ReadWrite.lean:18` the negative count | EP (contract) | as above | none |
| m-f83350256b | `FS/Wait.lean:174` the empty-queue return | EP | the walk over an empty queue returns the same value | none |
| m-cbb3079fa2 | `Kernel/Signal.lean:96` `.sigqueueAllocNoUcounts` | CB | no trace exhausts the signal ucounts (`alloc`, `wireguard` survived) | a trace at the sigpending limit |
| m-736cd45d76 | `Runner.lean:177` the pipe-reference descriptor form | invalid | the pipe-reference descriptor form is the runner's input parsing; the mutated runner refuses the pipes and alloc corpora (`domain_filter`, `invalid_output`) | none: not a mirror mutant |
| m-92f6d1fc7b | `Seccomp/Bridge.lean:65` the repeatable dedup | LO | set-based comparison, as above | none |
| m-9a33d70c0c | `Seccomp/Classic.lean:145` a code past the table | CB | no corpus program has such a code (the mutated lookup would panic on one) | a trace with an opcode ≥ the table size |
| m-da2fe3a128 | `Seccomp/Translate.lean:127` a jump target past the end at translation | EP | the classic checker rejects it first, as in the C; the translation's test is defensive | none |
| m-2ce60eff07 | `Syscalls.lean:126` `-EBADF` | CB | no trace passes an unknown descriptor to that syscall | a trace |
| m-07f15a1eb8 | `WG/Data.lean:53` `.padNoMtu` | CB | no trace sends with MTU 0 | a trace (if MTU 0 is settable; else EP) |

### 6.7 Order swaps and the WireGuard survivors of the second pass

Order swaps are logging-only by class: both tests run either way, so the
behaviour is the same unless the first test's arm has an effect the second
depends on. The channel that sees them is the decision order against the
witnesses, so a swap of two tests that are both false on every trace, one
of them unwitnessed, is invisible.

| Mutant | Site | Category | Why it survived | Fix |
| --- | --- | --- | --- | --- |
| m-abcfccd124 | `WG/AllowedIps.lean:117` `.addCidrTooLong` ↔ `.addNoPeer` | LO, CB | both false on all 3,620 adds in the census; `cidr_too_long` is unwitnessed, so the order of two false outcomes is not checked | a trace adding a too-long prefix (the arm, then the order) |
| m-36f6242651 | `WG/Data.lean:87` `.encCowDataFailed` ↔ `.encTooManyFrags` | LO | both false on every encrypt (278); the first is unwitnessed, the second a constant | none (the C's `cow_data` failure is an allocation the mirror steers elsewhere) |
| m-bb18cdf5e7 | `FS/Eventpoll.lean:688` the two `put_user` fault tests | LO | both false on every delivery (83); the first unwitnessed | none (a fault needs an unmapped user buffer, outside the contract) |
| m-74ca2f2010 | `Seccomp/Classic.lean:256` `.basicsLenZero` ↔ `.basicsLenOverMax` | LO | the C compiles `len == 0 \|\| len > MAX` into one test; the corpus has both rejections, and the declared pair is order-free in the built code | none |
| m-51fc08039e | `Seccomp/Translate.lean:194` `.convLenNonpositive` ↔ `.convLenOverMax` | LO | as above | none |

The WireGuard files' survivors came from the second pass (the rerun after
the oracle was rebuilt); every one ran its subset and the whole `wireguard`
suite, and the record-skipped ones `alloc` as well.

| Mutant | Site | Category | Why it survived | Fix |
| --- | --- | --- | --- | --- |
| m-ca4e5c16f1 | `WG/Handshake.lean:23` `HANDSHAKE_ZEROED` 0 → 1 | EP | a mirror-internal state label; the C's enum value is never an operand or an observation | none |
| m-45a739fa51 | `WG/Data.lean:78` `hiddenAlloc .skbCowHead` → ok | CB | no steered trace fails `skb_cow_head` (the `alloc` suite steers other sites) | a steered trace at that site |
| m-22037fe598 | `WG/Keypair.lean:51` `hiddenAlloc .kzallocKeypair` → ok | CB | no steered trace fails the keypair allocation | a steered trace |
| m-37c1d985b6 | `WG/RxData.lean:79` `hiddenAlloc .skbCowDataRx` → ok | CB | as above, the receive-side `skb_cow_data` | a steered trace |
| m-5f7165446a | `WG/Receive.lean:195` `hiddenAlloc .replySkb` → ok | CB | as above, the cookie reply's skb | a steered trace |
| m-1067963e6a | `WG/Handshake.lean:49` the kdf's two constant-false tests, return removed | EP | the condition is constant false by the mirror's construction (pointer tests the thin layer does not model) | none |
| m-3fc43a1223 | `WG/RxData.lean:65` `.decNoKeypair false`, return removed | EP | constant false by construction | none |
| m-7e879b58df | `WG/PrevQueue.lean:47` `.prevQueueTailNotHead false`, stop removed | EP | constant false: a producer mid-enqueue cannot occur on one CPU | none |
| m-cd49baa63b | `WG/NetlinkDump.lean:57` `.getAipNoNest`, return removed | **R** | the arm is taken twice in the suite; falling through, the next `put` fails on the same full buffer and returns the same result, but the mirror now reports an extra decision (`get_allowedips.put_cidr`) the kernel never evaluated, and nothing flags it because that outcome is unwitnessed | a check rule: a reported decision in a function whose coverage ends before it is a mismatch — fixed in 5d2e65b (terminal outcomes declared: after one, the function's next decision is a new call from the top) |
| m-9528a4d447 | `WG/Socket.lean:27` `.sockFreeNull`, return removed | EP | both outcomes taken (386 and 26); the continuation on a missing socket is a no-op | none |
| m-519d8769a1 | `WG/State.lean:218` `loopbackSoftirq`'s "not raised" return removed | EP | every caller tests the flag first; the body on a clear flag changes nothing | none |
| m-90315e93fd | `WG/Receive.lean:48` `.hdrTooShort`, return removed | CB | no injected datagram is shorter than 4 bytes (274 false) | a trace injecting a 3-byte datagram |
| m-3db354f814 | `WG/PeerRemove.lean:81` `upTo == some pid` → `!=` | CB | the partial flush (`upTo` set) runs only in the netns-close fixture, outside the corpus | a trace in that fixture |
| m-efeecf19ba | `WG/RxData.lean:40` `NAPI_POLL_WEIGHT` 64 → 65 | CB | no poll has 64 or more packets pending | a receive batch of 65 datagrams |
| m-c5ebae05a4 | `WG/Types.lean:188` `SMP_CACHE_BYTES` 64 → 65 | CB | the headroom alignment it feeds reaches no declared compare and no observation on the corpus | a declared operand at the headroom test, or a trace whose headroom crosses the alignment |
| m-87d2df8557 | `WG/Types.lean:213` the ring's batch rule `>` → `≥` at `size / 2` | CB | the batch is 16 against a half-size of 512; the boundary never occurs | none worth a trace |
| m-f9ed3f3b36 | `WG/NetlinkDump.lean:38` `NLMSG_GOODSIZE` 3776 → 3777 | CB | no dump sits within one byte of the split boundary | a dump sized to the boundary (the W2 stepped traces could) |
| m-67ee11e735 | `WG/Handshake.lean:284` unsupported: the handshake entry unhashed | EP (excluded) | | none |
| m-45ba4c3730 | `WG/Socket.lean:75` unsupported: a port collision | EP (excluded) | | none |
| m-7628dd8ab0 | `WG/Peer.lean:140` unsupported: an index stolen during insertion | EP (excluded) | | none |
| m-faf3cf1fd2 | `WG/NetlinkDump.lean:153` invariant: a stale allowed-IPs cursor | EP | | none |
| m-c78a7f5817 | `WG/PeerRemove.lean:48` invariant: queued work without a pending flag | EP | | none |
| m-01256f22fa | `WG/Receive.lean:282` invariant: a wrong packet in the handshake queue | EP | | none |
| m-767196a929 | `WG/State.lean:210` invariant: a NET_RX raised while pending | EP | | none |

### 6.8 Confirmation passes beyond the file's subset

The baseline decision census (`--decision-census` on every suite, the four
groups of section 5) showed for several survivors that the distinguishing
outcome is taken in a suite outside their file's subset, so every survivor
was rerun on the suites the census named: `alloc` (the armed allocation
records) for all of them, `handwritten` for the FS, kernel and seccomp
files, `epoll` for the FS files, `pipes` for the runner and the kernel
files, `wireguard` for the environment model. A rejection here moves the
mutant from the survivors to the rejected, with the suite named; the
tables above carry the outcome in their category column; the passes' rejections are:

| Mutant | Site | Rejected by | Channel | What the trace supplied |
| --- | --- | --- | --- | --- |
| m-9ffcb57df3 | `Env/IpStack.lean:22` `SENDER_PORT` + 1 | alloc | semantic mismatch | an injected datagram whose source port is observed |
| m-10201516ff | `FS/EventfdOps.lean:33` operand swap | alloc, handwritten | operand mismatch | a freed eventfd context with id ≠ 0 |
| m-133ab68446 | `FS/File.lean:60` `roundup_pow_of_two` negated | alloc, handwritten | unsupported path | `a2_allocfd_nomem` and `expand_by_allocation` grow the table past 64 |
| m-fcf16f4ca1 | `FS/File.lean:71` order swap | alloc, handwritten | control flow | the table growth's two tests |
| m-e3cceef5de | `FS/FileTable.lean:109` `.allocPathPseudoFail` | alloc | hidden mismatch | `a2_dentry_nomem` steers the failure |
| m-fa9da72d01 | `Kernel/Defs.lean:907` the site-id map negated | alloc | hidden mismatch | an armed allocation record |
| m-5ee912dbd3 | `FS/Close.lean:13` `.closeNoFile` | handwritten | mirror invariant | `failed_producer_reference` closes a descriptor that does not exist |
| m-c94fc660c7 | `FS/Eventfd.lean:25` invalid flags, return removed | handwritten | semantic mismatch | an eventfd with an invalid flag |
| m-0f81f80729 | `FS/Eventfd.lean:25` operand swap | handwritten | operand mismatch | the same trace (operand ≠ 0) |
| m-0177f5cdad | `FS/EventfdOps.lean:76` the short read | handwritten | semantic mismatch | a 4-byte eventfd read |
| m-805feb4dbd | `FS/Fcntl.lean:41` operand swap | handwritten | operand mismatch | `F_SETFL` toggling `O_APPEND` (operand 0x400) |
| m-62fabd29a0 | `FS/Fcntl.lean:43` `S_APPEND` test flipped | handwritten | semantic mismatch | the same trace: `-EPERM` returned |
| m-736cd45d76 | `Runner.lean:177` the pipe-reference form | alloc | invalid input | the alloc traces use the form; the mutated runner rejects its own input, an invalid mutant |
| m-d7dee84db8 | `Env/IpStack.lean:72` the checksum fold negated | wireguard | unsupported path, semantic mismatch | an injected IPv4 datagram whose checksum the receive path verifies (`receive.c:487`) |
| m-ab0b08a1e3 | `Env/Stack.lean:72` the TCP ack flag negated | wireguard | semantic mismatch | a TCP-over-WireGuard exchange in the stage traces |

Two consequences for the tables above. The `O_APPEND` toggle *is* in the
corpus (`handwritten`), so m-1c99f9201d, the negated `.setflAppendChanged`
decision that survived `handwritten` too while its operand-swap twin was
rejected there, is a witness gap and not a corpus boundary: the outcome of
`setfl.o_append_changed` is unwitnessed in the built code and its arm's only
effect on pipefs is the `IS_APPEND` test, so a mirror that takes the wrong
arm with the right operands passes; category **R**, fix a witness or a
declared compare on `IS_APPEND`. And the subset trimming of section 1
(handwritten dropped from the FS subsets to halve the run time) was the
cause of nine provisional survivals, all resolved by the pass; the
reproduction command below keeps `--confirm-survivors`, which runs the
whole area suite, and the subsets in the tool now include `handwritten`
for the FS files.

## 7. What each channel caught: behaviour-changing examples

Each example changes behaviour with the logging intact unless marked
logging-only; the channel named is the one the report carries.

- **Semantic mismatch (an observation differs).** `Env.lean:47`
  `LISTEN_PORT` 51999 → 52000: the device listens on another port and the
  first datagram's observation differs. `FS/Close.lean:25` `if restart
  then return -EINTR` negated: every close returns `-EINTR`.
  `Seccomp/Syscalls.lean:73` `mode == .disabled` → `!=`: the filter runs on
  every call of an unfiltered task; the first probe's return differs.
  `FS/EventfdOps.lean:76` `iterCount < 8` → `≤ 8`: an 8-byte eventfd read
  returns `-EINVAL`.
- **Control-flow mismatch (a decision's outcome against its witness).**
  `FS/EventfdOps.lean:33` `.eventfdFreeCtxHasId` negated: "opposite outcome
  covered" at `eventfd_free_ctx`. `FS/File.lean:29` `.clearCloexecWasSet`
  negated: "outcome not witnessed". The order change: `FS/ReadWrite.lean:41`
  two adjacent early returns exchanged (an `order-swapped` mutant), rejected
  as control flow and, because the second test's arm now runs first, as a
  semantic mismatch; `Kernel/Signal.lean:178` the same class, rejected as
  control flow alone (decision order differs from Linux). The
  placement-evidence rule: `Env/Batch.lean:38` `w != .netRx`, "the placement
  runs differ in control flow, not only in operands".
- **Hidden-input mismatch (a record consumed wrongly or left over).**
  `Env.lean:503` the time-advance record replaced by zeros: "the advance
  moved jiffies from 0 to 0, not by 135025", a behaviour change (no
  virtual time passes) caught at the record. `Env/Batch.lean:70` the
  resched peek's early return removed: "expected resched:wg_packet_tx_worker,
  the record is …", the scheduler consumes the wrong record.
  `Seccomp/Classic.lean:88` `BPF_MEMWORDS` 16 → 17: a program the checker
  now accepts is translated, and "no record left for bpf_prog_insn" on the
  per-instruction records. Logging-only examples in the same channel:
  `FS/Eventfd.lean:25` the invalid-flags compare's constant 0 → 1 with the
  outcome intact on every trace, caught because the mirror then skips a
  `current_time` clock read on the next path ("no record left for
  current_time"); the W9 sentinel's dst-cache jiffies ignored.
- **Operand mismatch (a declared comparison's values).**
  `Seccomp/Filter.lean:42` `SECCOMP_FILTER_FLAG_TSYNC` 1 → 2: the flag test's
  operands differ from the kernel's record on every install; the sentinel
  I8-M1 (the age test's left operand skewed by one nanosecond, every
  outcome unchanged) is the canonical logging-only case of this channel.
  The timer change: `WG/Peer.lean:159` `REKEY_TIMEOUT` 5 → 6 seconds
  (m-94d8944d6f, run on request) and `WG/Peer.lean:160` `KEEPALIVE_TIMEOUT`
  10 → 11 (m-f0adc4b54a): both rejected at the kind-303 arm record, the
  mirror's expiry differing from the kernel's by the extra second's ticks.
  The report names the channel `unsupported_path` with the item-8 arm
  rule's message, "a stall between a timer's two jiffies reads": the rule
  reads any gap above one tick as a stall, so a wrong delay is reported as
  a stall rather than as a wrong delay. A rejection either way, but the
  message misattributes the cause; the sentinel D3-M8 (a delay short by
  `REKEY_TIMEOUT`) is reported the same way. The keepalive one survived its
  subset (`s2_`, `wg_`, `l_`) and was rejected by the whole suite, the
  confirmation step doing its job.
- **Mirror invariant (the mutated mirror stops itself).** `Env.lean:271` the
  "no device" early return removed: the worker runs without a device and
  the invariant "no WireGuard device in this trace's fixture" fires.
  `FS/Fput.lean:32` `.fputFinalNotOpened` negated: "dangling file identity".
- **Unsupported path (the mutated mirror leaves its domain).**
  `Kernel/Signal.lean:119` `sig == SIGSYS` negated: every other signal's
  disposition is asked for and the stop "the disposition of signal 31 is not
  mirrored" fires on the first `SIGSYS`. `FS/Poll.lean:36`
  `.epPtableQueueProcNoEpi` negated.
- **Domain filter (every corpus trace falls out of the domain before Linux
  runs).** `FS/Close.lean:13` `.closeNoFile` negated: every close of a real
  descriptor is treated as `-EBADF`'s path; `FS/Eventfd.lean:19` the ida
  stop's condition negated: every eventfd creation stops. Thirteen such
  mutants; the check reports them as an abort naming the stop, which the
  tool counts as a rejection by the mirror's own stop.

## 8. Conclusion

The check rejects 84 percent of the applicable semantic mutants in the
sample, and every one of the 38 that survive is explained. Thirty-four are
corpus boundaries: an arm, a boundary value or a steered allocation site
that no trace supplies, each with the trace named that would reject it;
twelve of those are steered allocation failures or a steered environment
failure at a site the `alloc` suite does not cover (four WireGuard sites,
five FS sites, seccomp's whole set), and the rest are boundary values and
unexercised error arms. Four are reach problems of the check itself and
are the campaign's findings (each fixed on 2026-10-14; the fix is named in
its row of section 6):

1. `FS/Inode.lean:114` (m-b42171750c): the last `iput` of a pipefs inode no
   longer evicts it and nothing notices; `fs/inode.c` is anchored for its
   timestamp helpers only and no observation counts inodes. Fix: a declared
   decision on `iput_final`'s path or an observation of the inode count.
2. `FS/Fcntl.lean:41` (m-1c99f9201d): a recorded decision whose outcome is
   unwitnessed in the built code (`setfl.o_append_changed`) and whose arm
   has no observable effect on pipefs passes with the outcome inverted,
   although the corpus takes both outcomes. Fix: a witness, or a declared
   compare on the `IS_APPEND` test the arm runs.
3. `WG/NetlinkDump.lean:57` (m-cd49baa63b): a removed early return makes the
   mirror report a decision the kernel never evaluated, and the check does
   not flag an extra reported decision whose outcome is unwitnessed. Fix: a
   check rule tying a reported decision to the coverage of its function
   past the point where the kernel returned.
4. `Env/Batch.lean:38` (m-ec0783b3a0): the NET_RX section ordinal negated
   passes the placement-evidence check in a run with 15 inline placements
   while its logical twin was rejected; the check's sensitivity to the
   ordinal depends on which placement runs occur. Fix: the placement
   evidence should compare the section ordinals it replays. (After the
   fix the site is line 39 and the same mutation is m-cef7af2b2a.)

What the channels' shares say: control flow and hidden records catch most
of what is caught (the witnesses and the records are the instruments with
reach), the domain filter catches a wrong mirror before Linux runs
thirteen times, and the operand channel alone catches only the
logging-only edits it was built for. The sentinel set is confirmed as
representative: every channel it names rejected mutants here in the same
way. Recommended additions, from the survivors: no new sentinel (the four
findings are check rules and declarations, not channels), and the
thirty-four traces listed, of which the steered allocation sites and the
`O_APPEND` toggle are the cheapest.

Cost: median 242 s, mean 572 s, total 48 h 58 min of worker time over 308 runs. The confirmation passes added about 230 further suite runs.

Reproduction, from a clean checkout on the s2 oracle:

```sh
export LEANUX_KERNEL_DIR=/path/to/.artifacts/kernel-net-choice-s2   # identity cea1e9a3…
capped -- scripts/in-bundle python3 scripts/mutate.py --list --cap 1            # the sample
capped -- scripts/in-bundle python3 scripts/mutate.py --run --cap 1 --workers 4 --confirm-survivors \
    --results .artifacts/mutation/results.jsonl
capped -- scripts/in-bundle python3 scripts/mutate.py --reclassify --workers 4 --results .artifacts/mutation/results.jsonl
capped -- scripts/in-bundle python3 scripts/mutate.py --report docs/mutation-tables.md --results .artifacts/mutation/results.jsonl
```
