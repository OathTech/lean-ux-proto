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
SURVIVOR_CONFIRMATION_SENTENCE

## 5. The counts

COUNTS_PLACEHOLDER

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
| m-1c99f9201d | `FS/Fcntl.lean:41` `.setflAppendChanged` | CB | no trace toggles `O_APPEND` through `F_SETFL`, so the compare's operands are 0 either way and the negated arm only runs the `IS_APPEND` test, false on pipefs; the outcome itself is unwitnessed in the built code (the `&&` shares its block) | a trace setting `O_APPEND` on a pipe end (operand 0x400, the arm's path) |
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
| m-ec0783b3a0 | `Env/Batch.lean:38` the NET_RX section ordinal, condition negated | **R** | its logical twin `w != .netRx` (m-f61392504a) was rejected by the placement-evidence check, while this one passed the subset and the whole suite with 15 inline placements present in the confirming run (`napi_orders`: a 94, bc 15); the placement evidence's sensitivity to the section ordinal depends on which placement runs occur | a check rule: the placement evidence should compare the section ordinals of the steps it replays, not only their control flow |
| m-d7dee84db8 | `Env/IpStack.lean:72` checksum fold negated | CB | the environment's IP checksum is never observed on `handwritten`; a WireGuard injection would carry it (confirmation on `wireguard` pending) | PENDING_WG |
| m-ad789234b2 | `Env/IpStack.lean:72` `>` → `≥` at 0xffff | CB | the boundary value never occurs | none worth a trace |
| m-ab0b08a1e3 | `Env/Stack.lean:72` the TCP ack flag negated | CB | the environment's TCP helper is not exercised on `handwritten` (confirmation on `wireguard` pending) | PENDING_WG |
| m-f40fbc343a | `Env/Stack.lean:46` `<` → `≤` | CB | boundary only | none |
| m-85b3373196 | `Env/Stack.lean:46` `+1` → `+2` | CB | as above (confirmation pending) | PENDING_WG |
| m-9ffcb57df3 | `Env/IpStack.lean:22` `SENDER_PORT` + 1 | CB | the sender port of injected packets is not observed on `handwritten` (confirmation pending) | PENDING_WG |
| m-133ab68446 | `FS/File.lean:60` `roundup_pow_of_two` negated | CB | `alloc_fdtable` runs only when the table grows past 64 descriptors, which no trace does; the wrong size would then reach `findNextFdAllFull`'s operand | a trace holding 65 descriptors |
| m-a0580e9458 | `FS/File.lean:60` `n ≤ 1` → `n ≤ 2` | CB | as above | the same trace |
| m-fa9da72d01 | `Kernel/Defs.lean:907` the allocation-site id map negated | CB (subset) | the kind-305 records are unarmed outside the `alloc` suite, which the subset did not include (confirmation on `alloc` pending) | PENDING_ALLOC |
| m-bcac7274dc | `Kernel/Defs.lean:907` `58 ≤ i` → `58 < i` | CB (subset) | as above, for site 58 | PENDING_ALLOC |
| m-cf6dab30c3 | `Seccomp/Bridge.lean:62` the repeatable mark negated | LO | the per-operation comparison is set-based, so emission multiplicity is invisible by design | none |
| m-208ec53979 | `Seccomp/Decisions.lean:281` `SDecision.all` filter negated | EP | the list is used by the tests, not on the checked path | none |
| m-04f699319f | `Seccomp/Decisions.lean:281` `==` → `!=` | EP | as above | none |
| m-a0c041a9cf | `Seccomp/Translate.lean:106` the 16-bit sign extension negated | CB | no corpus program converts a 16-bit immediate on that path | a trace with a negative 16-bit immediate |
| m-f095e17543 | `Seccomp/Translate.lean:55` `≥ 32768` → `> 32768` | CB | the boundary value | the same trace |
| m-2a64bed551 | `Seccomp/Translate.lean:55` 32768 → 32769 | CB | the boundary value | the same trace |
| m-62fabd29a0 | `FS/Fcntl.lean:43` `S_APPEND != 0` → `== 0` | CB | the line is inside the `O_APPEND`-changed block that no trace enters | the `O_APPEND` trace above |
| m-a863e3ebe4 | `FS/File.lean:55` `bitbit > start` → `≥` | CB | differs only at `bitbit == start` | none worth a trace |
| m-b42171750c | `FS/Inode.lean:114` `i_count > 1` → `≥ 1` | **R** | the last `iput` no longer evicts the pipefs inode and nothing notices: `fs/inode.c` is anchored only for its timestamp helpers, `iput_final`/`evict` have no declared decision, and no observation counts inodes; a mirror that leaks every pipe's inode passes | a declaration on `iput_final`'s path (fs/inode.c) or an observation of the inode count after close |
| m-9997959668 | `FS/Wait.lean:184` `ret < 0` → `≤ 0` | CB | the walk breaks after the first callback returning 0; every corpus wait queue has one entry at the walk | a trace with two waiters on one head |
| m-b47970fdce | `Kernel/Refcount.lean:12` `old > 0` → `≥ 0` | EP | differs only at `old == 0`, a use-after-free no correct run reaches | none |
| m-d6cb2b5d37 | `Syscalls.lean:173` `fd ≥ rlimit` → `>` | CB | no trace names exactly the limit's descriptor number | a trace at the boundary |
| m-6297bb9625 | `FS/AnonInodes.lean:22` `-ENODEV` → `-ENOTDIR` | CB (steered) | the anon-inode failure is a steered path (confirmation on `alloc` pending) | PENDING_ALLOC |
| m-d6e357a769 | `FS/Close.lean:21` `-512` → `-513` | EP (contract) | `ERESTARTSYS` from a pipe close needs a signal the harness never sends | none |
| m-cd402fd597 | `FS/Inode.lean:46` `NSEC_PER_SEC` + 1 | CB | the pipefs timestamps it feeds are never observed (no `fstat` in the corpus) and their compare is non-constant | a trace observing a pipe's `ctime` after a write |
| m-19762748d3 | `FS/Pipe.lean:40` `PIPE_MIN_DEF_BUFFERS` + 1 | CB (steered) | used only under the soft pipe-buffer limit, a steered path (confirmation pending) | PENDING_ALLOC |
| m-fbdcb07871 | `FS/ReadWrite.lean:18` `2^63` → `3^63` | EP (contract) | a count that large cannot be passed | none |
| m-261f7b4645 | `Runner.lean:17` `MAX_IO` + 1 | EP | a runner bound, not the C's | none |

### 6.6 Removed early returns

| Mutant | Site | Category | Why it survived | Fix |
| --- | --- | --- | --- | --- |
| m-545d3ed0ba | `Env/IpStack.lean:182` `-EMSGSIZE` | EP (contract) | no payload exceeds the fragment size | none |
| m-04f1275a2b | `FS/AnonInodes.lean:22` `.anonInodeErr` | CB (steered) | PENDING_ALLOC | PENDING_ALLOC |
| m-5ee912dbd3 | `FS/Close.lean:13` `.closeNoFile` → `-EBADF` | CB | no trace closes an unknown descriptor | a trace: `close` of a never-opened fd |
| m-c94fc660c7 | `FS/Eventfd.lean:25` invalid flags | CB | no trace passes an invalid eventfd flag | a trace |
| m-0177f5cdad | `FS/EventfdOps.lean:76` a short eventfd read | CB | no trace reads an eventfd with fewer than 8 bytes | a trace |
| m-ad049b9b15 | `FS/Eventpoll.lean:90` a dead file at `ep_item_poll` | EP | unreachable on a correct run | none |
| m-9ec4b350ac | `FS/Fcntl.lean:43` `-EPERM` on `S_APPEND` | CB | inside the `O_APPEND` block no trace enters | the `O_APPEND` trace |
| m-e3cceef5de | `FS/FileTable.lean:109` `.allocPathPseudoFail` | CB (steered) | PENDING_ALLOC | PENDING_ALLOC |
| m-415d0346f2 | `FS/Inode.lean:96` `envOk .allocInode` | CB (steered) | PENDING_ALLOC | PENDING_ALLOC |
| m-00693e433c | `FS/Open.lean:17` `filp_flush` at count 0 | EP | unreachable on a correct run | none |
| m-d070830a74 | `FS/Pipe.lean:101` `envOk .copyPageToIter` | CB (steered) | PENDING_ALLOC | PENDING_ALLOC |
| m-18e6657307 | `FS/PipeCreate.lean:24` `.getPipeInodeNoInode` | CB (steered) | PENDING_ALLOC | PENDING_ALLOC |
| m-057152dfc5 | `FS/ReadWrite.lean:18` the negative count | EP (contract) | as above | none |
| m-f83350256b | `FS/Wait.lean:174` the empty-queue return | EP | the walk over an empty queue returns the same value | none |
| m-cbb3079fa2 | `Kernel/Signal.lean:96` `.sigqueueAllocNoUcounts` | CB (steered) | PENDING_ALLOC | PENDING_ALLOC |
| m-736cd45d76 | `Runner.lean:177` the pipe-reference descriptor form | CB (subset) | the form is used by the pipes corpus, which the runner's subset did not include (confirmation on `pipes` pending) | PENDING_PIPES |
| m-92f6d1fc7b | `Seccomp/Bridge.lean:65` the repeatable dedup | LO | set-based comparison, as above | none |
| m-9a33d70c0c | `Seccomp/Classic.lean:145` a code past the table | CB | no corpus program has such a code (the mutated lookup would panic on one) | a trace with an opcode ≥ the table size |
| m-da2fe3a128 | `Seccomp/Translate.lean:127` a jump target past the end at translation | EP | the classic checker rejects it first, as in the C; the translation's test is defensive | none |
| m-2ce60eff07 | `Syscalls.lean:126` `-EBADF` | CB | no trace passes an unknown descriptor to that syscall | a trace |
| m-07f15a1eb8 | `WG/Data.lean:53` `.padNoMtu` | CB | no trace sends with MTU 0 | a trace (if MTU 0 is settable; else EP) |

ORDER_SWAPPED_PLACEHOLDER

## 7. What each channel caught: behaviour-changing examples

EXAMPLES_PLACEHOLDER

## 8. Conclusion

CONCLUSION_PLACEHOLDER

Reproduction, from a clean checkout on the s2 oracle:

```sh
export LEANUX_KERNEL_DIR=/path/to/.artifacts/kernel-net-choice-s2   # identity cea1e9a3…
capped -- scripts/in-bundle python3 scripts/mutate.py --list --cap 1            # the sample
capped -- scripts/in-bundle python3 scripts/mutate.py --run --cap 1 --workers 4 --confirm-survivors \
    --results .artifacts/mutation/results.jsonl
capped -- scripts/in-bundle python3 scripts/mutate.py --reclassify --workers 4 --results .artifacts/mutation/results.jsonl
capped -- scripts/in-bundle python3 scripts/mutate.py --report docs/mutation-tables.md --results .artifacts/mutation/results.jsonl
```
