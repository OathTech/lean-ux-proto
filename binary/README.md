# Binary refinement experiment

This package experiments with relating selected compiled WireGuard functions
to the executable Lean mirror under Kraken's x86-64 semantics. The
[project health warning](../README.md) applies here too. The theorems assume
explicit memory, environment and service contracts; they do not establish
whole-WireGuard correctness or behavior in a concurrent Linux kernel.

The target is the saved **s5** Linux image, pinned independently of the
mirror's test oracle. The two identity files currently name the same image,
but future changes need not keep them aligned. Proofs use committed decoded
image terms. Running the image tests additionally needs the exact saved ELF; there is no
recipe here that promises to regenerate it from a fresh clone.

## Results and limits

| Part | What is established | What remains outside the claim |
| --- | --- | --- |
| Index lookup | `LookupAdequacy.lookup_simulation` relates the complete lookup and bucket loop to an accepted mirror run, including NULL, zero-count and live peer-get paths; transport lemmas carry properties through the relation | Named service, serialization, permission and initial-memory premises; only the hit paths have theorem witnesses showing the lookup premises can be met. A NULL-owner witness and general kernel-entry realism remain unproved |
| Replay-state frame | `LookupSnapshotTransport.lookup_snapshot_transport` preserves the represented frontier and source-live lifetime/replay fields through lookup | Initial representation and separation are extra premises, not supplied by the existing lookup Pre witness; no physical allocator-membership or whole-receive theorem |
| Sequential paired execution | Checked entry assertions and retained-heap composition for selected index operations, plus a sequential allowed-IPs lookup and bounded callback proofs | No concurrent-context result; input coupling and service/permission contracts remain where stated. A dying-peer retry is a source refusal in the trie experiment |
| Allowed-IPs mutation scaling | Tested component proofs for placement, reassignment and initialization/publication segments; an extended lookup reconstruction | Zero newly completed functions in this increment. Insertion, allocation/failure handling and full function/sequence composition remain open |

The milestone-1 [review obligations at landing](../docs/2026-10-19-binary-landing-assessment.md#outstanding-review-obligations-at-landing)
remain open as stated there, including the NULL-owner `Pre_lookup` witness,
callback assumptions in the original headline, transport representation and
separation premises, general entry realism and subsystem-wide scaling.
Concrete NULL-owner execution tests do not supply the missing theorem witness.

The two allowed-IPs rows describe different stages: the sequential lookup
experiment predates the unfinished mutation work. Passing a component proof
or an executable test does not complete the larger function theorem.
The detailed [binary register](../docs/proofs.md#binary-adequacy-standalone-charter-target)
and reports below name statements, premises and historical validation commits.

## Build from a clone

Use a non-main worktree as described in [setup](../REPRODUCING.md). The
package needs Git, the Lean toolchain named by
[`lean-toolchain`](lean-toolchain), and Python 3.12+ with pyelftools available
to the interpreter launching `run.py`. The mirror's staged tools are also
needed for QEMU-backed tests. Select the host Python before entering the
bundle: the staged Python does not include pyelftools. The commands below use that interpreter with the
staged Lean and build tools; no host Lean installation is required.

Check the interpreters before bootstrapping, from the worktree root:

```sh
binary_python=$(command -v python3)
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
scripts/in-bundle "$binary_python" -c 'import elftools; print(elftools.__version__)'
scripts/in-bundle lean --version
cap scripts/in-bundle "$binary_python" -B binary/run.py --bootstrap-only
cap scripts/in-bundle lake -d binary build
cap scripts/in-bundle "$binary_python" scripts/binary-proof-gate
```

If the import check fails, select a project-local Python environment with
pyelftools installed and set `binary_python` to its interpreter before
continuing. The root and binary toolchain pins currently agree; compare them
before reusing these commands after a toolchain change.
Bootstrap creates a private patched Kraken checkout at `.deps/kraken`, using
a shared upstream clone when available and the locked upstream URL otherwise.
It applies the committed patches and checks the exact resulting Git identity.
It refuses a dirty or differently pinned existing checkout. When network access
is needed, run bootstrap in an environment that permits the fetch.

The semantics pin is declared in
[`dependencies/sources.lock.json`](../dependencies/sources.lock.json) and
[`TrustBase.lean`](TrustBase.lean), including nine committed Kraken patches.
Patch nine adds the register BT forms needed by the insertion image. Those
forms deliberately leave the zero flag (ZF) undefined, along with BT's other
undefined flags. These semantics are part of the trust boundary; their tests are not a proof of ISA
fidelity. Unsupported forms fail explicitly.

The package imports the operational mirror by path and does not import
`Leanux.Proofs`. Its local source-model definitions and execution equations
are in `AllowedipsSourceModel.lean` and `AllowedipsSourceRun.lean`.

**Compatibility exception:** `BinaryProofs.allowNonModules = true` permits
Kraken's new-style modules and the mirror's legacy modules in the same
library, because the symbolic proofs need Kraken definition bodies. This
suppresses Lake's import-style warning for this library only; it does not
suppress Lean proof, axiom or replay diagnostics. The package does not migrate
the mirror's module system or change Kraken's public API.

## Check the proof boundary

`scripts/binary-proof-gate` checks the locked, clean Kraken dependency, builds
the package, checks headline and witness axioms, and scans proof sources for
escapes. It also compares the printed statements, relations and trust
contracts against [`TrustSurface.expected.txt`](TrustSurface.expected.txt).
A passing comparison means those declarations match the reviewable specification;
it does not prove the contracts. The mirror proof gate is separate.

Kernel replay is a further check. From the worktree root, create a temporary
output directory, then export from `binary/` after the build succeeds:

```sh
mkdir -p .tmp
cd binary
cap ../scripts/in-bundle lake env leanexport LookupSnapshotTransport LookupWitness LookupHitWitness \
  AllowedipsWitnessPre PairCallbackSurface PairCallWitness \
  PairAllowedipsLookupAdequacy AllowedipsCommonChecked AllowedipsInsertionSurface \
  > ../.tmp/binary-check.ndjson
```

Require export exit status 0. A partial file from a failed export is not a
valid gate input. Still in `binary/`, run:

```sh
cap ../scripts/in-bundle lake check --from-export ../.tmp/binary-check.ndjson
```

On the shared devboxes, the user runs this last command outside nono: the
checker's own sandbox cannot start inside it. An inside-nono check with
`--inadvisably-no-sandbox` is a diagnostic run and does not replace that gate.
The export avoids a sandboxed build of this package's parent path dependencies.
Exports can be large; delete the temporary file after checking it.

Acceptance is specific to a source commit and export closure. The earlier
combined s5 export was accepted at `736492453c292ba9caafa78b353ae19f4ce9671b`
on 2026-10-19. That acceptance does **not** cover the later allowed-IPs
mutation additions or patch nine; their
[closing report](../docs/2026-10-20-binary-allowedips.md#experimental-close-and-landing-preparation)
records local validation and pending external acceptance.
`AllowedipsInsertionSurface` is a partial-proof export root, not a completed
insertion theorem.

## Run image tests with the saved ELF

Set `LEANUX_BINARY_KERNEL_DIR` to the directory containing the s5 `vmlinux`.
[`target.py`](target.py) checks its exact SHA-256 against
[`kernel-identity-s5.txt`](kernel-identity-s5.txt) and selects that identity
for guest captures. It does not follow changes to the mirror's oracle.
The default artifact location is `.artifacts/kernel-net-choice-s5` in the
common checkout; its presence is not guaranteed by setup.

With that artifact and the build prerequisites in place, run from the worktree
root (return there with `cd ..` if following the export example):

```sh
# Check committed image/layout data against the saved ELF
cap scripts/in-bundle "$binary_python" -B binary/generate.py --check
cap scripts/in-bundle "$binary_python" -B binary/generate_allowedips.py --check
cap scripts/in-bundle "$binary_python" -B binary/generate_index_mutators.py --check
cap scripts/in-bundle "$binary_python" -B binary/generate_random_service.py --check
cap scripts/in-bundle "$binary_python" -B binary/generate_random_layout.py --check

# Paired index lookup and allowed-IPs mutation experiments
cap scripts/in-bundle "$binary_python" -B binary/pair_run.py --trace d1_wrong_receiver_index_same_bucket
cap scripts/in-bundle "$binary_python" -B binary/allowedips_mutation.py
cap scripts/in-bundle "$binary_python" -B binary/allowedips_seq_wrap.py
```

The sequence-wrap witness tests the fixed-width counter correction found by
this experiment. It is a regression test, not a general refinement theorem.
Use the [execution recipes](REPRODUCING.md) for recorded comparisons and capture replays:
constructed entry heaps, captured kernel memory and symbolic proofs are
separate evidence. A constructed heap is not a captured kernel state, and
running a few undefined-value seeds is not quantification over those choices.

## Allowed-IPs mutation scaling

For the recorded comparison and capture commands, use the
[detailed execution recipes](REPRODUCING.md#allowed-ips-mutation-scaling).
The [export command above](#check-the-proof-boundary) includes the nine roots
used for the mutation experiment. The [closing report](../docs/2026-10-20-binary-allowedips.md)
gives the component boundaries and measured results; full insertion remains
open.

## Detailed reports

These preserve the experiments' original boundaries and commands. Read their
validation commits and later corrections before treating a historical pass
as acceptance of the current source.

| Report | Contents |
| --- | --- |
| [Adequacy report](../docs/2026-10-15-binary-adequacy.md) | Index lookup theorem, trust premises and milestone review obligations |
| [Sequential experiment](../docs/2026-10-16-goal-binary-proof-refactoring.md) | Endpoint-only sibling and its limits |
| [Executable correspondence](../docs/2026-10-16-plan-executable-binary-correspondence.md) | Constructed/captured entry states, trie loop and complete-call experiments |
| [Index subsystem](../docs/2026-10-18-paired-index-subsystem.md) | Removal, replacement and retained-heap composition |
| [Index insertion](../docs/2026-10-18-paired-index-insertion.md) | Recorded inputs, service contracts and mixed sequences |
| [Callback proofs](../docs/2026-10-19-paired-callbacks.md) | Bounded image callbacks and first-return permissions |
| [s5 landing assessment](../docs/2026-10-19-binary-landing-assessment.md) | Port to the split mirror, relocation, repairs and acceptance |
| [Allowed-IPs scaling](../docs/2026-10-20-binary-allowedips.md) | Partial mutation result, open composition and reproduction commands |

A typed heap view over the machine semantics is follow-on work on a separate
branch. It is not part of the results above; the design is preserved at
`de18ce37:docs/2026-10-20-design-heap-view-overlay.md`.
