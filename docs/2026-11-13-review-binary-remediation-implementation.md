# Review of the first binary-remediation implementation batch

Independent review [AGENT 2026-11-13]. Baseline `80d17ae2`; reviewed
implementation `6153f81a`, source-cut change `312da83c` (equivalent
integration `fb1ec2da`), results-document revision `236dc847`, and final
recipe correction `b953155f`. Work stayed in a separate review
worktree, with at most one heavy job and an 8 GiB job ceiling.

## Verdict and scope

No unresolved implementation correctness finding was identified in this
bounded batch. One reproducibility finding against the draft results
document was raised and corrected; its committed disposition is below.
This is a review of the capture/checker changes and their stated evidence,
not approval of main integration or admission of the outstanding binary
claims.

The implementation preserves the relevant distinctions:

* `PairCapture.run` now runs `IndexLookup.callBoundary` through
  `IndexLookup.runFrom` before interpreting the same captured invocation.
  Full coverage allocation is required. History pruning changes retained
  snapshots while the instruction sequence, accesses and loop checks remain
  active. The streaming endpoint comparison retains malformed-byte,
  unmapped-byte, register, flag and overlap rejection.
* The replacement diagnostic executes the original completed-operation
  mirror twice using this boot's PC-mode records. Neither execution is
  presented as observing the internal replacement entry. Its proposal to
  observe the original `beginSession` before `indexReplaceHandshake`
  addresses the missing cut without filling source state from native bytes.
* The C2 checker implements the archived `Kept` count/register clauses and
  an explicitly different, finite physical-memory frame observation. A
  translated, changed virtual alias outside the footprint is a valid
  counterexample to an all-native-virtual-byte interpretation. It is not a
  counterexample to Kraken's flat-memory theorem. The checker never returns
  complete admission, and the report preserves that distinction.

The inventory correctly leaves universal permissions, transport premises,
independent mutator caller alignment, complete captured joins and native
memory representation unresolved. C2's bounded visits do not establish
complete-interval capture, lifetime reuse, the required replay/boundary
cases, or an environment-transition relation. Its proposed projection is
not yet an executable complete replacement statement. These limitations
are disclosed in the implementation reports; they must remain visible
before any new proof or composition is commissioned. This batch does not
complete remediation stages 1–6 or renew historical external acceptance.
The mirror proof register's existing lag is unchanged.

## Finding F1: explicitly select the recording harness's s5 image

**Priority:** P2, reproduction defect in the draft first-batch report.

**Location:** the environment setup preceding the direct `evaluator.check`
command in `docs/2026-11-13-binary-remediation-first-batch.md:164`, under
“Reproduce the lookup experiment”; compare `harness/linux.py:28` and
`binary/target.py:13`.

The draft selected the binary prerequisites but omitted the harness's
separate `LEANUX_KERNEL_DIR` and `LEANUX_KERNEL_IDENTITY`. In a fresh shell,
the binary target selects `.artifacts/kernel-net-choice-s5`, whereas the
direct checker selects `.artifacts/kernel-net-choice`. Read-only inspection
confirmed that the latter directory is absent on this box. Current identity
files happen to agree; that does not make the paths interchangeable, and
the capture also checks the recorded kernel path. The recipe therefore
fails before reproducing the advertised experiment unless it inherits
undocumented environment state. This does not invalidate the recorded
runs, whose pins are a separate question.

**Remedy:** use the checked setup already in `binary/REPRODUCING.md`: require
the saved s5 directory, call `verify_image()` and `pins()`, and export both
harness variables before recording. Keep this local to the experiment's
shell.

**Disposition: fixed and rechecked.** `236dc847` adds the checked setup and
both harness variables. Final review also requested explicit export of
`LEANUX_BINARY_KERNEL_DIR`: an ordinary shell assignment must reach the
Python target selector, particularly for a non-default saved-image path.
`b953155f` adds that export before verification in both the first-batch
report and `binary/REPRODUCING.md`. Inspection of the committed correction
confirms the required order. No finding remains open.

## Independent checks

The following checks passed in the review worktree:

* Private Kraken bootstrap and a fresh `PairCapture` / `binary-pair-runner`
  build: 455 jobs, no compiler warnings observed.
* All 23 binary Python tests, all six C2 memory/observer controls, and
  elaboration of the new `ReplacementPrefixes.lean` helper.
* The streaming endpoint diagnostic: consistent overlap accepted and all
  eight malformed/changed controls rejected.
* The generated lookup suite: 48 calls and 18 rejection controls, including
  the missing final coverage byte.
* An independent temporary experiment compared `IndexLookup.runFrom` with
  default history and `some #[]` on the generated hit and same-bucket miss,
  at both undefined-value seeds. Final machine data/PC, source device/step
  projection, coverage, comparisons, instruction PCs, read/write records,
  undefined count and returned report all agreed. The hit executed 506
  instructions and retained 507 versus one state; the miss executed 191
  and retained 192 versus one. This is fixture evidence, not a native run.

The first binary Python test attempt failed with seven setup errors because
the fresh review worktree lacked `.tmp`. After creating that private
directory, one infrastructure rerun passed all 23 tests. No shared setup
was changed, no semantic failure was retried, and no cap failure occurred.

Read-only inspection of the two discovery lookup snapshots independently
confirmed capacity and captured extent of 4,194,304 words, a 33,554,432-byte
coverage block, identical entry/return block extents, 33,624,268 captured
bytes, sequential mode, completed operations `[0, 1, 2]`, and the reported
506/191 instruction counts. Their saved replay reports contain passes at
both seeds. Read-only inspection of the two fresh repeat replay reports
also confirmed the same counts and the reported entry count `0x80000000`.
The complete native replays were not independently rerun: their
reported 16 GiB job cap exceeds this review's 8 GiB ceiling. The original
C2 RAM captures had been removed before review, so their 32-visit numerical
results were not independently rerun. Source inspection and the synthetic
controls support the observer's method; they do not reproduce those boots.

The full binary proof gate, external export acceptance, full mirror suites,
controls and sentinel runs were not independently repeated. The review
does not turn the coordinator's validation report into those additional
claims.

## Reproduction of the retained checks

From a task worktree, with the documented bundle and saved-image setup:

```sh
binary_python=$(command -v python3)
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
mkdir -p .tmp
CAPPED_MEM_MAX=8G cap scripts/in-bundle "$binary_python" -B binary/run.py --bootstrap-only
CAPPED_MEM_MAX=8G cap scripts/in-bundle lake -d binary build PairCapture binary-pair-runner
CAPPED_MEM_MAX=1G cap scripts/in-bundle "$binary_python" -B -m unittest discover -s binary -p 'test_*.py'
CAPPED_MEM_MAX=1G cap "$binary_python" -B -m unittest discover -s binary/remediation -p test_c2_memory.py
CAPPED_MEM_MAX=8G cap scripts/in-bundle lake -d binary env lean binary/remediation/ReplacementPrefixes.lean
CAPPED_MEM_MAX=8G cap scripts/in-bundle lake -d binary env lean --run binary/remediation/CaptureEndpointChecks.lean
```

For the generated suite, prepare either lookup input using
`binary/pair_run.py` and the pinned recording instructions in the first-batch
report, then run `CAPPED_MEM_MAX=8G cap binary/.lake/build/bin/binary-pair-runner INPUT.json`.
For the history experiment, use the same parsed `ProbeInput` and
`replayPrefix`/`startSession` fixture. Install the normal lookup ABI once,
call `IndexLookup.runFrom` twice with the identical fixture and seed, varying
only the final history argument between `none` and `some #[]`, and compare
the fields listed above. Test the recorded entry index and that index plus
8,192 at seeds zero and `0xffffffffffffffff`. The temporary input and
experiment source were removed after recording this conclusion.

No implementation change was authored during review. The review commit
contains only this report. The review worktree's `.tmp`, `.lake`,
`binary/.lake`, `.deps`, `.cache` and `.artifacts` were removed afterward;
the branch and report remain available for integration review.
