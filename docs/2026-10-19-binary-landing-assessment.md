# Binary experiment: prospective landing assessment

Status: landing preparation in progress. The initial compatibility findings
below are historical; the split-state port is described at the end. Final
validation, the trust-surface diff and external kernel replay remain pending.

## Scope and inputs

[USER 2026-10-19] The experiment targets refinement of the WireGuard subsystem
against the compiled image under explicitly unrealistic sequential/environment
assumptions. Its scientific question is whether executable invariant discovery
and reusable proofs make wider subsystem coverage affordable. Proving realistic
kernel callers or concurrent contextual refinement is outside this increment.

[USER 2026-10-19] Assess landing after the pending environment fixes, preserving
the existing experiment and leaving main unchanged.

[AGENT 2026-10-19] Use `task/binary-pair-landing` in
`.worktrees/binary-pair-landing` for a trial merge, rather than rebasing the
experiment in place. Inputs are fixed for this assessment:

| Input | Commit |
| --- | --- |
| Experiment, `task/binary-pair-runner` | `272104798c4c0cd0acd34212e1ec4712d52d0d66` |
| Main at assessment | `783510e850e187549cbb9380e53790e1ed232c77` |
| Pending fixes, `task/env-requests` | `d811b0ba58a1d98dd6c2a2d7757789b2c32c9824` |
| Mirror underlying the existing binary results | `cb2348e2175326f67392cae27d2132f9676897e7` |
| Private Kraken, unchanged | `cd2ae360bfcf8e1fc719793405811ff49c3e75ce` |

The trial merges the pending-fix snapshot (which contains the assessed main)
into a new branch from the experiment. It does not assert that those pending
fixes have landed. The original experiment worktree remains clean at its
original commit. No main update or push was performed.

The experiment is small in covered behavior, not in source volume: its
preparation diff against the pending-fix snapshot is about 105,000 added lines
in 785 tracked files before this note and the new bootstrap test. There are 719
top-level binary Lean modules. This includes the earlier M1 and partial M2 work
and the later sibling experiments.

## Merge and compatibility findings

### 1. Git conflicts are small; state migration is substantive

There were three conflicted files:

- `docs/README.md`: retain both sets of document links.
- `harness/linux.py`: retain main's initramfs-size provenance and the
  experiment's optional binary-coverage ranges.
- `scripts/proof-gate`: retain main's root-module enumeration, stricter escape
  scan, string/comment handling and capped commands, while retaining the
  binary target and its explicit imports/artifact directory.

The merged harness's unit tests pass. No standing rule in `AGENTS.md` was
edited beyond incorporating the existing main version.

The first required binary compilation failures are `MirrorLoop.lean` and
`ProbeSupport.lean`. The attempted headline build reports 43 error lines;
downstream modules do not thereby become checked. Representative failures are
the removed `World.k` and `World.steps` fields, the removed `getK`, and functions
whose monad/state argument changed. Updating field names alone is insufficient:

| Old surface | Current surface and required treatment |
| --- | --- |
| `World.k.wg` | `World.wg.dev`; keep the relation over the WireGuard projection |
| `World.steps`, hidden input and dispatch bookkeeping | `World.ambient`; keep supplied input/history separate from physical reconstruction |
| WireGuard functions directly in `Leanux.M` | `WG.M = StateT WGWorld AmbientM`; port source inversion/history lemmas to this state or use the actual `liftWG` adapter explicitly |
| Index removal/insertion/replacement directly over the device | `IndexM = StateT (List IndexEntry) AmbientM`; use the actual `liftIndex` at device boundaries |
| Trie traversal directly over the device | `AipM` and `liftAip`; reestablish source bridges without adding unrelated fields to R |
| Prefix replay's `initialKernel` and flat World construction | Current Runner initialization, routing boot, timer lookahead and split state |

A textual census finds `.k.` in 77 binary modules and `: World` in 155.
These counts overlap and are not proof-obligation counts. Import traversal
finds 665 modules transitively importing `Leanux.*`, leaving only 54 without a
mirror import path. In particular `TrustBase` imports mirror projection and
input definitions; `CallbackContracts` reaches that surface. Its separate
build therefore fails at `MirrorLoop` too. Several machine-only modules,
including the literal image/layout and `CommonBitsRegions`, did build in the
trial; this is not a successful callback or headline replay.

The state split should reduce future framing obligations, but this branch has
not received that benefit yet. The port must preserve the claimed accepted
paths, including NULL/dead peers, and the existing explicit environment
assumptions. Reintroducing the old global World as an operational mirror or
narrowing Pre to make the port close would defeat the purpose.

### 2. Pending environment fixes affect workload preparation

Relative to the assessed main, `task/env-requests` changes worker refill fuel,
pending device-work dispatch/completion, and netlink dump cancellation. It
does not directly edit the anchored index/allowed-IPs functions. The moved
pending-bit clear in `AmbientM.hidden` acts at section-start sites, not the
index insertion's random-input site. This is a source inspection, not a proof
that all existing source lemmas survive.

`ProbeSupport.replayRecordedPrefix` contains its own entry initialization and
completion checks. Its port must include the new pending-work rejection, as
well as routing boot and timer lookahead already added on main. Merely moving
its field accesses would leave a stale copy of the Runner's domain checks.
The recorded workloads must then be regenerated/replayed; old successful
captures cannot validate this new prefix implementation.

### 3. The pinned proof image is s4; main's oracle is s5

The existing proof, literal addresses, layouts, witnesses and capture scripts
target s4. The merged kernel identity file selects s5, while
`binary/census.py` still selects the shared s4 file. Existing probe preparation
compares those two identities and must reject them. A global identity override
would not establish that the old literal instruction tables describe s5.

Read-only ELF comparison found unchanged function sizes but moved addresses:

| Function | s4 entry | s5 entry | Bytes |
| --- | --- | --- | --- |
| index lookup | `ffffffff813a0470` | `ffffffff813a0670` | 208 |
| peer-get | `ffffffff81399610` | `ffffffff81399810` | 250 |
| index remove | `ffffffff813a0400` | `ffffffff813a0600` | 98 |
| index replace | `ffffffff813a0350` | `ffffffff813a0550` | 161 |
| index insert | `ffffffff813a01a0` | `ffffffff813a03a0` | 426 |
| `common_bits` | `ffffffff813a0750` | `ffffffff813a0950` | 224 |
| KCOV PC | `ffffffff810f3100` | `ffffffff810f31f0` | 91 |
| BH-enable | `ffffffff810732c0` | `ffffffff810732c0` | 63 |

The first seven bodies differ in bytes. BH-enable and the three inspected
comparison wrappers have identical body bytes, though the wrappers moved.
This comparison does not prove relocation equivalence or establish that every
instruction difference is an address adjustment. There are literal kernel
addresses in 117 binary Lean modules.

Landing an explicitly historical s4 experiment is possible in principle; it
requires a separate, explicit binary identity and reproducible compatible
workloads. Retargeting to the current s5 oracle instead requires regeneration,
symbolic revalidation and fresh captures. These are different scopes. The trial
has done neither, and retains the original trust pin. Do not silently describe
the s4 theorem as a theorem about the current oracle.

To reproduce the comparison, use `nm -S --defined-only` and
`objdump -d --disassemble=wg_index_hashtable_lookup` on each read-only image;
repeat for the other named symbols. ELF symbol bytes were compared directly
in this assessment, not through a normalized assembler listing.

### 4. Fresh dependency bootstrap was broken; repaired locally

The original bootstrap applied all seven patches with a fixed committer
identity. The last three patches have a different author/committer, so a fresh
replay produced `d5a30250` instead of the locked `cd2ae360`, although their tree
IDs are identical (`eeedaf8a9af1fa64db16340f062ebcaf59b775f5`). The exact-commit
gate correctly refuses that substitute. Bootstrap also tried to verify the
Lake dependency manifest before a fresh worktree had generated it.

The repair preserves each patch's original author/committer identity and equal
dates using command-scoped Git configuration, generates both local manifests
before verification, and locates shared input via Git's common directory rather
than assuming a particular worktree depth. `--keep-toolchain` explicitly keeps
the consumer's v4.35.0 choice over upstream Kraken's nightly declaration.
No global configuration or shared dependency was changed.

The fresh bootstrap regression reconstructs the exact locked commit from the
staged upstream repository, checks an idempotent second invocation and checks
that a dirty source tree is still rejected. Both manifests start absent. It
passes without warnings. For the initial compilation diagnosis, the private
trial checkout was populated from the original experiment's exact local commit;
the new regression independently checks patch reconstruction.

Other portability work remains: the probe's hard-coded Elan toolchain location,
the census's fixed worktree-depth/image lookup, and README commands naming old
development worktrees. These are preparation issues, not new proof hypotheses.

### 5. Warnings and historical status need cleanup

The cold binary build emits 260 warning lines, including unused simp arguments,
module-system imports and a Kraken deprecation. Fifteen binary modules contain
file-wide `linter.unusedSimpArgs` suppression. These are inherited findings,
not an acceptable warning-clean landing. Fix the warnings and remove broad
suppression; an unavoidable dependency constraint needs the narrowly documented
exception permitted by the working rules. The main mirror build also emits the
inherited `String.mk` deprecation at `Leanux/Env.lean:873`; report/coordinate that
source cleanup with the mirror lane rather than changing behavior for a proof.

The historical reports retain their original results and pins. The current
register/README must distinguish those results from a successful port. The
latest callback export's external acceptance is still pending and, even when
accepted, covers its original revision rather than this integration trial.
The allowed-IPs sequential-result row also mixes its completed function result
with older future-tense boundary status; reconcile it against the actual
headline when carrying the register forward.

An existing verbatim human approval appears in
`kernel/identity-x86_64-net-choice.txt`'s historical s1 comment. It predates this
trial and was left untouched; removal is the user's decision under the working
rules. No human message was copied into this note or the preparation commits.

## Validation and remaining sequence

All heavy commands ran through `capped`. No cap kill or timeout is counted as
success.

| Check | Result |
| --- | --- |
| `capped lake build leanux-model leanux-netlink-dump-tests` | PASS, 133 jobs; inherited deprecation noted above |
| Mirror/harness unit command below | PASS, 136 tests, one existing skip |
| `capped .lake/build/bin/leanux-netlink-dump-tests` | PASS, cancellation leaves 3724 bytes |
| Binary Python discovery below | PASS, 15 tests including fresh bootstrap |
| `capped lake -d binary build PairCallbackSurface PairCallAdequacy` | FAIL, state-split errors at `MirrorLoop` and `ProbeSupport` |
| `capped lake -d binary build CallbackContracts` | FAIL, transitive source dependency at `MirrorLoop` |
| Current paired workloads, full differential claim-point checks, headline replay/export gate | Not run: port/image decisions and successful binary build required first |

The initial mirror unit attempt failed because the fresh checkout did not yet
contain `leanux-model` (29 failures and one error). Building the declared
executable resolved that setup failure; the single rerun is the passing result
above. Logs and generated manifests are ephemeral under this worktree.

Reproduce the passing unit checks from the worktree root:

```sh
capped scripts/in-bundle python3 -B -m unittest \
  evaluator.test_evaluation evaluator.test_model_replay \
  harness.test_trace harness.test_wg harness.test_linux
capped python3 -B -m unittest discover -s binary -p 'test_*.py'
```

Suggested preparation order (no new proof scope is introduced):

1. Port source execution/history bridges and replay initialization to the native
   split states and adapters. Keep the machine-region arguments intact where
   possible; inspect semantic changes rather than mechanically rewriting every
   theorem. Preserve the original experiment branch as a comparison point.
2. Select the landing's image scope explicitly: historical s4 or retargeted s5.
   Regenerate the executable inputs and any image-dependent declarations that
   choice requires. Keep identity checks fail-closed.
3. Rebuild all experimental headlines/witnesses, repair warnings and carry the
   printed trust/statement surface forward with an explained diff. Verify that
   the accepted domain and unrealistic environment hypotheses have not changed
   accidentally during the port.
4. Rerun paired workloads/captures and the relevant mirror/harness checks. At
   the landing claim point, run the required differential/controls/sentinels,
   fresh kernel replay and the external `lake check --from-export` gate on a
   newly generated export. Record exact commits and image identities.
5. Update the current README/register and present the concrete integration
   revision for main approval. Broad WireGuard coverage and contextual
   refinement are not prerequisites for landing this experiment.

The honest present conclusion is that this needs a source-API port plus an
explicit image policy, not merely a clean rebase. The pending environment
fixes are a smaller part of that work than the changes already on main.

## Split-mirror port checkpoint

[USER 2026-10-19] Prepare the isolated landing branch, preserve the experiment
branch, and rebase onto main after the environment fixes land. Keep a separate
binary gate and state the outstanding milestone-1 review obligations as open.

[AGENT 2026-10-19] Retain the exact s4 image. Its instruction/layout proofs are
already extensive; relocating them to s5 is a separate port with no benefit to
this landing's limited experimental claim. `binary/target.py` validates the
s4 ELF and explicitly selects its kernel identity for recordings and captures.
The main mirror's default s5 oracle remains unchanged.

`Binary.Source` abbreviations call the current mirror through `liftWG`,
`liftIndex` and `liftAip`. The accessor and component-composition lemmas prove
the old World-facing proof presentation equivalent to those actual adapters;
they do not copy a historical mirror. All physical state relations remain over
the WireGuard projection. History lives in `World.ambient`, and unrelated
components are preserved by the real product adapter.

One source-interface distinction matters: the split allowed-IPs component
checks device presence even for an empty root. The old unguarded logged loop
is therefore erased only at a state with a device. Accepted execution of the
actual lookup supplies this fact; no binary precondition or relation is
strengthened, and no missing-device execution is silently accepted. Dead and
NULL index-owner paths remain in scope.

The recorded-prefix runner now initializes the actual split components and
checks pending work at each operation boundary, matching the landed runner's
completion guards. Runtime adapter diagnostics compare the finite device and
history projections; the adapter equations prove the complete resulting World
equality. These diagnostics do not claim decidable equality of function-valued
environment fields.

The default binary build and executable validation are being rerun against this
port. The 15 binary Python tests pass, including exact Kraken reconstruction,
dirty-tree rejection, trust-surface drift, and remote capture transport. The
new `scripts/binary-proof-gate` is independent of `scripts/proof-gate`, which
retains main's mirror-proof behavior. Expected theorem text will be updated
only after inspection of the port's printed statements. Historical external
gate acceptances do not validate this port.
