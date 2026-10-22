# Independent review: the front-facing documentation pass (`task/shop-window`)

Subject: branch `task/shop-window` at `a9e958bf`, one commit on main
`c63423ef`, 13 files: `README.md`, `REPRODUCING.md`, `binary/README.md`, the
new `binary/REPRODUCING.md`, `correspondence/README.md`, `docs/README.md`,
`docs/proofs.md`, `docs/history/README.md`, `docs/offline-usage.md`,
`docs/upstream-tray/INDEX.md` and `README.md`, `harness/README.md`, and the new
`docs/2026-10-22-setup-findings.md`. Main has since moved to `8702e79f`.
Judged against the base, with what the rebase must preserve named below.

Authorities used: the register in `docs/proofs.md` (rows and claim-carrying
theorems, at the base and on main), the three campaign landing reviews, the
two binary landing reviews and the s5 landing assessment, the fresh-eyes
scope review, `AGENTS.md`, and the code the documents describe
(`harness/linux.py`, `evaluator/check.py`, `scripts/proof-gate`,
`scripts/binary-proof-gate`, `scripts/restore-toolchains.py`,
`scripts/stage-resources.py`, `scripts/build-kernel`, `binary/run.py`,
`binary/target.py`, the lock files).

## Verdict

**Land with named changes.** The pass is a real improvement. The front page
now separates differential evidence, mirror proofs, the binary experiment and
source-only kernel drafts. It also names the conditional T4/T5 premises, the
unjoined T2 binding and the journal-completeness boundary. It corrects several
stale or false statements, and the binary README cut kept the trust surface,
both gates, the nine patches and the saved-ELF limit. The health warning
survives with the same meaning: the only change is the link label ("scope
table" became "scope").

Two things stop it landing as committed. First, the setup guide's first step
cannot succeed from a clone on an ordinary machine, and the guide says it can
(B1). Second, the branch states a register state that its own tree does not
have (B2). B2 goes away with a correct rebase. B1 needs a small edit to the
documents. The should-fix items are short wording changes, mostly to carry
two of the scope review's priority findings onto the front page.

## Checks run

All checks ran in a detached copy of `a9e958bf`
(`.worktrees/review-sw-copy`, now removed), through `capped -- scripts/in-bundle`.
None hit the memory cap.

| Check | Result |
| --- | --- |
| `lake build leanux-model leanux-fixed-width-tests` | PASS, 133 jobs, no warnings |
| Model-only eventfd example from `REPRODUCING.md` §2 | PASS: fd 8, bytes `0500000000000000`, as documented |
| Five-module fast tier | PASS: 144 tests, 1 skip (no kernel at the default path) |
| `harness.test_noise harness.test_d1_keepalive` | PASS: 29 tests |
| `harness.test_d1_keys` (setup finding F1) | FAIL as the note says: ambiguous `M`; `k`, `env`, `timing`, `hidden` are not `World` fields; `ambient`, `tasks`, `fs` are missing |
| `scripts/proof-gate` | PASS: 6,680 jobs, 2,448 terminal statements, axioms within the standard three |
| `scripts/proof-counterexamples` | **FAIL, 14 of 15**: `h5-namespace-pin` (the concrete input no longer parses). This is expected for the base tree. It contradicts the branch's prose (B2) |
| Binary bootstrap with the README's host-Python recipe | PASS: private clone from the shared upstream, nine patches applied, tip `43df9468`, matching `sources.lock.json` and `TrustBase.krakenCommit` |
| `lake -d binary build` | PASS: 1,119 jobs, no warnings |
| `scripts/binary-proof-gate` (host Python inside the bundle) | PASS, including the trust-surface diff |
| Lean 4.35.0 restore as a fresh clone would run it (`restore-toolchains.py --only lean`, in a scratch directory with no snapshot archive) | **FAIL**: "No snapshot and no upstream release for lean" (B1) |
| Link and anchor check over the 13 files (relative links, Markdown anchors) | PASS: no missing targets, no bad anchors |
| `git merge-tree` of the branch with main `8702e79f` | One conflict, in `docs/proofs.md`'s opening sections |
| Factual spot checks against the code: suite names, `--trace alias_close`, report keys (`status`, `aborted`, `failures`, `napi_before_put_sections`), the 16-slot default and lock location, the wrapper behavior, `LEANUX_KERNEL_BUILD`/`LEANUX_JOBS`, the kernel config values, the QEMU command line, the identity files, the s5 ELF hash, `section_agreement`/`replay_problem`, the theorem names in the binary table, the nine export roots, `leanexport` in the toolchain | All as documented |

Not run: kernel build, differential suites, controls and mutants, binary image
tests (they need the saved ELF), `lake check` (it needs to run outside nono).

## Findings

### Blocking

**B1. The pinned Lean toolchain cannot be obtained from a clone, and the
setup guide says it can.** `REPRODUCING.md` §1 tells the reader to run
`scripts/restore-toolchains.py --only lean`, and says the staging commands
download from the Ubuntu snapshot service, kernel.org and GitHub and verify
the locked hashes. `dependencies/toolchains.lock.json` has two rows named
`lean`. The 4.33.1 row (legacy, not needed at this revision) has an upstream
URL. The 4.35.0 row, the one `lean-toolchain` names and `scripts/in-bundle`
requires, has only a box-local snapshot archive (`.deps/downloads/…`, which is
not in Git) and no `upstream_url`. A fresh clone therefore downloads about
750 MB of Lean 4.33.1 and then exits with "No snapshot and no upstream release
for lean"; I reproduced this offline in a scratch directory. Nothing after §1
works without that toolchain: model, tests, proofs, binary. The README's
"Run it" section and the commit message both present the setup as usable from
a clone. This is a project-wide portability defect that the setup-findings
note missed. The lock fix is an implementation change outside a documentation
pass. What the pass must do is stop claiming otherwise:
(a) say in `REPRODUCING.md` §1 (and in `README.md` "Run it" if it keeps its
from-a-clone wording) that Lean 4.35.0 currently has to be supplied as a
snapshot, or installed and staged by hand at `.tools/lean-4.35.0`, until the
lock gains an upstream row;
(b) add the defect to the setup-findings note (see S4).

**B2. As committed, the branch states a proof-register state that its base
does not contain.** At `c63423ef`, the register's T1–T6 rows say the
speedbump FAILED (14/15), and H5 is supplied-mode only and lagging on the
namespace-pin recipe. The branch rewrites those seven rows and the H5 entry in
the claim-carrying table. The rewritten text is copied from the then-unlanded
`ec3e34b7`. The branch's prose says all 15 recipes pass and every row is
current. `README.md` says accepted boundaries have no pending work units in
either record mode. On the branch's own tree, the speedbump fails 14/15 (run
above). The commit message is candid that these rows assume the follow-on
lands, and it has landed (`6bfde8bb`). The branch's row text is now
byte-identical to main's. So the defect goes away with a correct rebase, and
the branch must not land without one. Note also that the brief's description
of the `docs/proofs.md` change ("prose, not rows") is inaccurate: rows were
edited. Rebase conditions:
- After rebasing onto `8702e79f` or later, `git diff main -- docs/proofs.md`
  must show no change to any Results row or claim-carrying-table row.
- The conflict in the opening sections must keep main's **Bounded scope
  probes** section: the lifetime fault-exclusion probe and its countermodel
  `LifetimeSafety.FaultProbe.allocation_invariant_does_not_exclude_lookup_faults`,
  and the one-event removal probe. The branch's "Reading the claims" section
  can replace main's opening paragraph. It must not replace the probes.
- "Current register" cites 6,680 jobs and 2,448 terminal checks as the
  combined validation. Main is now at 2,455 terminal statements and 6,681
  jobs (`8702e79f`'s record, after the FaultProbe module). Either update the
  counts or label them as the campaign-2 follow-on checkpoint.

### Should fix before landing

**S1. The README's lifetime summary still reads as weaker-than-stated only on
failed lookups. It should say outright that R2 does not establish absence of
invalid dereferences.** The scope review's priority-1 finding was that
lifetime safety of resolved events does not exclude invalid dereferences.
Main's probe now proves that R2's allocation invariant alone does not exclude
peer/keypair lookup faults. The README's campaign-1 cell ("lifetime safety for
recorded committed accesses (failed lookups are outside the statement)") is
accurate. Still, a reader without context will take "lifetime safety" as
memory safety. Add a clause such as "it does not establish that no invalid
dereference occurs; see the fault-exclusion probe". Add the same in
`docs/proofs.md` "Reading the claims" after the rebase.

**S2. "Per-allocation nonce uniqueness" needs its scope stated on the front
page.** The scope review (finding 5) is explicit: T1's tokens are keyed by the
keypair's allocation identity. Distinct allocations do not imply distinct key
bytes, so this is not a key-material/nonce uniqueness claim. "Per-allocation"
is the correct technical word, but a security reader will read "nonce
uniqueness" as freedom from nonce reuse. Add "keyed by key allocation, not by
key material" or similar.

**S3. The binary README dropped the statement that the milestone-1 review
obligations remain open.** The s5 landing assessment (its section on
outstanding review obligations, and the landing condition that the README
state them as open) lists open items. F1: no `Pre_lookup` theorem witness for
the NULL-owner path. F2: the original M1 headline still takes callback
contracts as hypotheses. F6: transport representation/separation premises.
F7: entry realism. F9: scaling. The old README said they remained. The new
results table covers F6 and F7 in substance. It also says the lookup theorem
covers "NULL, zero-count and live peer-get paths", which, without F1, reads as
witnessed coverage. Add one sentence under the table saying the milestone-1
obligations recorded in the landing assessment remain open, with a link to
that section. Qualify the NULL path as covered by the theorem, with
non-vacuity witnessed for the hit paths only.

**S4. The setup-findings note is accurate, but it is incomplete.** I confirmed
F1 and F2 against the code: `harness/linux.py` defaults to 16 slots;
`docs/worktree-practices.md` says 8. Add:
- F3: the Lean 4.35.0 lock row has no upstream source (B1). As a side defect,
  `--only lean` also fetches the obsolete 4.33.1 stage.
- F4: `AGENTS.md` gives `.artifacts/kernel-net-choice-e2` in the main checkout
  as the example oracle path. No such directory exists. The approved identity
  is satisfied by `.artifacts/kernel-net-choice-s5`, whose `vmlinux` hashes to
  the pinned `06513d05…`. The branch's own commit message records that the e2
  preflight failed, but the note does not. `AGENTS.md` is the
  working-practices doc, so correcting it is a proposal to the user, as the
  note already says for F2's document.

**S5. The documentation index should pick up main's new reports after the
rebase.** Main added `docs/2026-10-21-proof-probes.md` and the three probe
reports but did not edit `docs/README.md` (contrary to the brief, main did not
change that file). The rebased guide should list them, at least next to the
scope review in "Choose a starting point", because they are the current state
of the scope review's findings 2–4.

### Notes

- N1. The health warning is intact in meaning; only the anchor's link text
  changed. The second blockquote summary was folded into the first section.
  The no-equivalence, no-Linux-security and no-C-correspondence statements
  all survive in plain prose.
- N2. Corrections the pass gets right and that should be kept:
  - The old binary README said the mirror's oracle differs from s5. The two
    identity files are byte-identical in their hashes. The new "currently name
    the same image" is correct.
  - The harness README's "three slots" is corrected to 16.
  - The stale e2 path is dropped from `docs/offline-usage.md`.
  - The tray now separates the two traced reports from the two source-only
    ones.
  - Seccomp and Net are added to the correspondence map.
- N3. The binary README no longer states the BT ZF vendor question. The
  landing review asked for it only if Intel's rule was kept. The semantics now
  leave ZF undefined (vendor-neutral), so nothing is owed. One line saying
  that BT's undefined flags include ZF on purpose would still help a trust
  reviewer. The exact Kraken pin is now given only by reference (lock file,
  `TrustBase.lean`). That is acceptable.
- N4. `binary/README.md` asks for a pyelftools import check before bootstrap.
  Bootstrap, the proof build and the binary gate do not import pyelftools; only
  the image generators and pairing scripts do. A newcomer without it is told to
  stop when the proof checks would work. Also, pyelftools is declared in no
  project file and pinned to no version. Move the check to the image-test
  section and consider declaring the dependency.
- N5. The `docs/README.md` index leaves about 38 dated documents unindexed.
  This was already so at the base. They include the binary milestone-1 review,
  the adequacy report, campaign-3 sub-reviews and the C2 follow-up notes.
  `AGENTS.md` says the dated documents are indexed there. The pass improves
  this slightly (landing reviews are reachable from the campaign rows). A
  completeness sweep is follow-on work.
- N6. The tray's "Ranking [AGENT]" section is replaced by "numbers are stable
  identifiers, not a severity ranking". The commit message records this as an
  agent decision, which is the right place. After the rebase, `INDEX.md`
  could mention main's 2026-10-21 qualification of report 04: the
  single-CPU window is conditional, with no UP reproducer.
- N7. Newcomer wording in `REPRODUCING.md`:
  - "the main checkout" (on a fresh clone, the clone itself) and "overseer
    follow-up" are project jargon.
  - "Allow space" gives no figures. The two Lean stages alone are about
    1.5 GB, plus the Linux tree and the build.
  - The kernel build runs under the default `cap`, which is 32G on these
    boxes. `AGENTS.md` uses `-m 64G` for the same command. Use one figure in
    both places.
- N8. The README's campaign table omits a few register qualifiers. H2 holds
  at normal initialized endpoints only. H4's readback is one-directional,
  under an entry invariant not derived at initialized endpoints. The S1–S3
  replay-window spike result is not mentioned at all. The table defers to the
  register, which is acceptable, but H4's "readback for four peer fields" is
  the phrase most likely to be over-read.
- N9. No sentence in the 13 files calls the mirror "verified" or "equivalent",
  calls anything "proved secure", or presents T4/T5 as unconditional. Binary
  results are described as function/component results under premises, not
  adequacy of the mirror. Per-allocation nonce safety (S2) and lifetime safety
  (S1) are the two places where a front-page reading can still exceed the
  theorem.

*Independent reviewer (Claude Opus 5.5), 2026-10-22.*
