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
| Receive replay window (C2) | `Binary.C2.refines`: the 70-instruction inlined `counter_validate` range of `wg_packet_rx_poll`, `[0xffffffff8139d2a6, 0xffffffff8139d3ea)`, computes the mirror's `counterValidate` (exit, acceptance byte, window bytes). `exits_cleanly`: from every entry state it reaches an exit without faulting and keeps what `Kept` says. `replay_witness`: one counter presented twice to a retained window is accepted, then refused. In the bridge library, `Binary.C2.Bridge.no_counter_accepted_twice` and `headline : HeadlineRefinement`: over visits between which the window bytes are unchanged, no packet counter is accepted twice. All closed, no hypothesis beyond the statement's premises | A single-CPU, coverage-instrumented build with no lock: nothing carries to an SMP build. The entry context (`Context`) is argued from the disassembly, not derived, and no captured kernel state was checked against it. That the window is unchanged between visits is a premise about the rest of the kernel. The range ends at `setb %bpl`: that a replayed packet is dropped (the unlock, the branch, the drop path, that every delivery passes through the range) is not claimed. Decoder agreement is tested, not proved; Kraken's semantics with the tenth patch is the base; `Refines` says no more than the mirror. See the [closing report](../docs/2026-11-10-c2-replay-window.md) |
| Allowed-IPs insertion (C1) | `Binary.Statements.C1.Proof.signed : Signed` (`C1Signed.lean`; statement `StatementC1*.lean`), closed with no hypothesis. `Headline`: for every decoder, layout and allocator meeting `Premises`, there is an invariant that holds at a physically empty table, survives changes outside the heap and the caller taking or dropping a reference on an existing peer, and is carried by every accepted call of `wg_allowedips_insert_v4/_v6` (through `add`, on all nine paths, allocation failure and rollback included) and of `lookup`, each returning the mirror's answer. With it a witness that the premises can be met and the calls run, and two exclusions (an insertion is then found; a failed insertion is invisible). The component theorems of the earlier increment (placement, reassignment, initialization and publication segments) are what the proof is built from | Closed-world from an empty table: peer creation or removal between insertions is outside, so a `wg set` that creates its peers is covered for its first peer only. A claim about the six WireGuard functions against any code at the two service addresses that meets `AllocatorContract`; the image's allocator is not shown to meet it and under this semantic base cannot. Parent pointers and peer lists are not claimed. A single-CPU, coverage-instrumented image and a sequential model. Decoder agreement is tested, not proved. The caller's conditions are premises, shown at 20 captured calls and not proved of any real call. The witness is a stub with artificial aspects ([closing report](../docs/2026-11-11-c1-allowedips-insertion.md)). Removal, the dump and the walk-by-peer remain open |

The milestone-1 [review obligations at landing](../docs/2026-10-19-binary-landing-assessment.md#outstanding-review-obligations-at-landing)
remain open as stated there, including the NULL-owner `Pre_lookup` witness,
callback assumptions in the original headline, transport representation and
separation premises, general entry realism and subsystem-wide scaling.
Concrete NULL-owner execution tests do not supply the missing theorem witness.

The two allowed-IPs rows describe different stages: the sequential lookup
experiment predates the insertion result, which is the first completed
mutation function. Passing a component proof or an executable test does not
complete a larger function theorem.
The detailed [binary register](../docs/proofs.md#binary-adequacy-standalone-charter-target)
and reports below name statements, premises and historical validation commits.

## Build from a clone

Use a non-main worktree as described in [setup](../REPRODUCING.md). The
package needs Git, the Lean toolchain named by
[`lean-toolchain`](lean-toolchain), and Python 3.12+. Bootstrap, proof builds
and the binary proof gate do not need pyelftools; image generators and
pairing/capture scripts do. The mirror's staged tools are also needed for
QEMU-backed tests. Select the host Python before entering the bundle; the
commands below use that interpreter with the selected Lean and build tools.

Check the interpreters before bootstrapping, from the worktree root:

```sh
binary_python=$(command -v python3)
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
scripts/in-bundle lean --version
cap scripts/in-bundle "$binary_python" -B binary/run.py --bootstrap-only
cap scripts/in-bundle lake -d binary build
cap scripts/in-bundle "$binary_python" scripts/binary-proof-gate
cap scripts/in-bundle "$binary_python" scripts/c2-bridge-gate    # builds C2Bridge: result C2's headline
```

Both gates are claim-point checks of the binary track. The binary gate does
not build the bridge, so the headline of result C2 is checked only by the
second line. `scripts/in-bundle` resets `PATH`, so the gates cannot find
`capped` themselves and print a notice: wrap the whole command, as above.

The root and binary toolchain pins currently agree; compare them
before reusing these commands after a toolchain change.
Bootstrap creates a private patched Kraken checkout at `.deps/kraken`, using
a shared upstream clone when available and the locked upstream URL otherwise.
It applies the committed patches and checks the exact resulting Git identity.
It refuses a dirty or differently pinned existing checkout. When network access
is needed, run bootstrap in an environment that permits the fetch.

The semantics pin is declared in
[`dependencies/sources.lock.json`](../dependencies/sources.lock.json) and
[`TrustBase.lean`](TrustBase.lean), including ten committed Kraken patches.
Patch nine adds the register BT forms needed by the insertion image. Those
forms deliberately leave the zero flag (ZF) undefined, along with BT's other
undefined flags. Patch ten adds one form of BTS, the one in the replay-window
range: a 64-bit register bit offset on a memory quadword, unlocked. It is
defined only when the offset is below 64 and the quadword is mapped; CF takes
the old bit, the quadword is written back with the bit set, and the other
five status flags are undefined. These semantics are part of the trust
boundary; their tests are not a proof of ISA fidelity. Unsupported forms fail
explicitly.

The patches carry their own tests (`#guard` in `Kraken/X64/*Tests.lean`).
The package imports no test module, so no build and no gate compiles them;
they are run by hand when a patch is made or changed, from the worktree root:

```sh
(cd .deps/kraken && cap ../../scripts/in-bundle lake -d ../../binary build \
  +Kraken.X64.LookupTests +Kraken.X64.ParserTests +Kraken.X64.BsrTests +Kraken.X64.PrintATTTests \
  +Kraken.X64.SystemFlagsTests +Kraken.X64.GreaterTests +Kraken.X64.StosTests +Kraken.X64.MovsTests \
  +Kraken.X64.XaddTests +Kraken.X64.BtTests +Kraken.X64.BtsTests)
```

The package imports the operational mirror by path and does not import
`Leanux.Proofs`. One file outside the package's default library does:
[`bridge/C2Bridge.lean`](bridge/C2Bridge.lean), the non-default lake library
`C2Bridge`, imports the package and exactly four modules of the proof tree
(`Leanux.Proofs.WG.CounterWindow.Model`, `.Refinement`, `.MirrorCalls`,
`.Bounds`) to join C2's refinement with the landed uniqueness theorem. It has
its own gate, `scripts/c2-bridge-gate`; the exemption from the proof tree's
import rule that admits it is recorded in [AGENTS.md](../AGENTS.md).
The package's local source-model definitions and execution equations
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

Kernel replay is a further check. Run it in a worktree whose `.deps/kraken`
is the bootstrapped, patched checkout (`binary/run.py --bootstrap-only`
above), and whose package has just been built from the source being checked.
The main checkout's `.deps/kraken` is the unpatched shared upstream clone:
the build fails there. From the worktree root, create a temporary
output directory, then export from `binary/` after the build succeeds:

```sh
mkdir -p .tmp
cd binary
cap ../scripts/in-bundle lake env leanexport LookupSnapshotTransport LookupWitness LookupHitWitness \
  AllowedipsWitnessPre PairCallbackSurface PairCallWitness \
  PairAllowedipsLookupAdequacy AllowedipsCommonChecked AllowedipsInsertionSurface \
  C2Headline \
  > ../.tmp/binary-check.ndjson
```

Result C2's closure, the bridge and its four proof-tree modules included, is
exported on its own. Build the bridge from the source being checked
immediately before the export (`cap scripts/in-bundle lake -d binary build
C2Bridge`, from the worktree root): the export reads whatever was last built,
and the replay accepts a stale output without complaint. Then, in `binary/`:

```sh
cap ../scripts/in-bundle lake env leanexport C2Headline C2Bridge > ../.tmp/c2-check.ndjson
cap ../scripts/in-bundle sh -c 'PATH="$PATH:/usr/bin" COMPARATOR_BWRAP=/usr/bin/bwrap exec lake check --from-export ../.tmp/c2-check.ndjson'
```

Result C1's closure is exported on its own as well (about 1.8 GB), after
`cap scripts/in-bundle lake -d binary build` from the worktree root:

```sh
cap ../scripts/in-bundle lake env leanexport C1Signed > ../.tmp/c1-check.ndjson
cap ../scripts/in-bundle sh -c 'PATH="$PATH:/usr/bin" COMPARATOR_BWRAP=/usr/bin/bwrap exec lake check --from-export ../.tmp/c1-check.ndjson'
```

The check lines need both settings, and the single quotes matter (`PATH`
must expand inside the bundle):

- `lake check` finds its sandbox helper by running `which`, which lives in
  `/usr/bin`; `scripts/in-bundle` resets `PATH` without `/usr/bin`, so
  without the appended directory the lookup fails ("bwrap … was not
  found").
- `in-bundle` puts a staged copy of `bwrap` on `PATH`
  (`.tools/sysroot/usr/bin/bwrap`), and `which bwrap` would resolve to it.
  On a distribution that restricts unprivileged user namespaces by path
  (Ubuntu's AppArmor profile is attached to `/usr/bin/bwrap`), the staged
  copy must not be the one used: set `COMPARATOR_BWRAP` to the system
  `bwrap`. Where that lives is a box matter; `/usr/bin/bwrap` is the
  devboxes' value.
- A line "Lean default kernel rejected the solution" directly after a
  `bwrap` error line (for example `bwrap: loopback: Failed RTM_NEWADDR:
  Operation not permitted`) is the sandbox failing to start, not a kernel
  verdict.

Require export exit status 0. A partial file from a failed export is not a
valid gate input. Still in `binary/`, run:

```sh
cap ../scripts/in-bundle sh -c 'PATH="$PATH:/usr/bin" COMPARATOR_BWRAP=/usr/bin/bwrap exec lake check --from-export ../.tmp/binary-check.ndjson'
```

On the shared devboxes, the user runs the `lake check` lines outside nono:
that run is the gate. In the form above the checker's sandbox has also
started inside nono (2026-11-11); such a run, like one with
`--inadvisably-no-sandbox`, is a diagnostic and does not replace the gate.
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

First install the pinned [Python requirements](requirements.txt) in a local
virtual environment using the [optional image-dependency setup](../REPRODUCING.md#6-optional-binary-image-dependencies).
From the worktree root, select that interpreter before entering the bundle:

```sh
binary_python="$PWD/.tmp/binary-python/bin/python"
scripts/in-bundle "$binary_python" -c 'import elftools; print(elftools.__version__)'
```

The bundle's staged Python does not include pyelftools. Keep `binary_python`
set for the image generators, paired executions and capture recipes below.

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
cap scripts/in-bundle "$binary_python" -B binary/generate_c2.py --check
cap scripts/in-bundle "$binary_python" -B binary/generate_c1_callbacks.py --check

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
| [Replay window, C2](../docs/2026-11-10-c2-replay-window.md) | The closed refinement headline for the receive counter window, its premises, the bridge library and its gate |
| [Callback proofs](../docs/2026-10-19-paired-callbacks.md) | Bounded image callbacks and first-return permissions |
| [s5 landing assessment](../docs/2026-10-19-binary-landing-assessment.md) | Port to the split mirror, relocation, repairs and acceptance |
| [Allowed-IPs scaling](../docs/2026-10-20-binary-allowedips.md) | Partial mutation result, open composition and reproduction commands |

A typed heap view over the machine semantics is follow-on work on a separate
branch. It is not part of the results above; the design is preserved at
`de18ce37:docs/2026-10-20-design-heap-view-overlay.md`.
