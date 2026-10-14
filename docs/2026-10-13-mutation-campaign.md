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

Provenance: [USER 2026-10-13] "let's plan to work on fidelity improvements /
audit / census gaps while the proof campaign is running"; the campaign's
shape (the classes, the sampling, the subsets) is [AGENT, fork of the
coordinator].

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

RESULTS_PLACEHOLDER
