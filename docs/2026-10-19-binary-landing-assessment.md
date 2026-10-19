# Binary experiment: landing preparation and validation

Status: **landing conditions in progress**, rebased onto main `3308c49a`, using
the actual split mirror and an explicit s5 image pin. At the preceding
`9af3b709` checkpoint, the full build, standalone
binary gate, unit tests, selected differential recordings, exact witnesses,
paired suites and all six actual-capture replays pass. **The external export
gate passed on 2026-10-19**, and no merge to main or push is authorized or
performed. Earlier assessment/checkpoint sections below retain their failed
attempts and historical pins; the current landing conditions are at the end.
The coordinator will rerun the package gate and mirror fast tier on the
completed landing-condition series before presenting it for integration.

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

## Outstanding review obligations at landing

The independent milestone-1 review is historical and is not superseded by this
port. Its findings have the following narrower dispositions; this experiment
must not be described as closing the original campaign.

| Finding | Landing disposition and remaining obligation |
| --- | --- |
| F1, hit-path non-vacuity | Dead and live hit witnesses compile against the split mirror and their exact states execute to return on s5 under both seeds; the live projection is compared with its recorded prefix. NULL-owner execution is covered by concrete tests; a separate M1 `Pre_lookup` theorem witness for that path remains open, as does the suggested wrong-kind/KCOV-mode-3 theorem witness. |
| F2, callback contracts | The later sibling proves all five index-family callbacks from the pinned image and uses them in its sequential headlines. The original M1 headline still takes callback contracts as hypotheses; those are not silently removed. Discharging the contracts in every original transport and broader subsystem theorem remains open. |
| F3, honest hypotheses | The tree prunes unused trust declarations and explicitly takes serialization/permission hypotheses. They describe an intentionally unrealistic environment, not established kernel-context facts. |
| F4, reusable post-state | The M1 post exports restored preempt count, the KCOV-buffer invariant and the softirq word. This does not establish arbitrary caller/environment composition. |
| F5, composition method | The unused `compose_regions` was retired. Composition remains bespoke; no generic generated composition mechanism is claimed. |
| F6, transport premises | **Open:** initial representation and heap-separation premises for snapshot transport remain assumptions. No unconditional transport of the mirror campaign's whole WireGuard properties is claimed. Minimal R and separate frame theorems are the settled scope. |
| F7, entry realism | **Open and deferred:** general kernel-entry reachability, pending softirqs at BH-enable, user-modified KCOV counts, and allocator membership are not proved. Captured selected entries are tests, not a general realism theorem. Realistic concurrent contexts are outside this increment. |
| F8, trusted inputs | The separate binary gate checks the clean pinned Kraken tree, axioms and printed statements/trust declarations. ELF/table comparison is a claim-point check. The user ran the new s5 export from code commit `73649245` outside Nono on 2026-10-19; the default kernel accepted it using only the three standard axioms. Old accepted exports do not cover this port. |
| F9, scaling | **Open:** subsystem-wide proof cost and coverage are unestablished. Historical region throughput and sibling adaptation costs are not a campaign forecast. |
| F10, branch hygiene | Binary coverage is opt-in and ranges are supplied rather than hard-coded in the guest. The landing does not alter AGENTS.md. All three unfinished Kraken example proofs are isolated outside the dependency's library/proof import path; the original F10 report explains that the reverted AGENTS paragraph was intended to advertise the charter gate. Its commands now live in `binary/README.md`. |
| F11, claim limits | The explicit limits below remain part of the claim. Historical F1/F3/F4 defects are distinguished from the implemented corrections, rather than repeated as current facts. |

The M1 lookup has no hidden-input hook, so its theorem alone exercises no
record-stream consumption. Later insertion results exercise the supplied random
tape under explicit provider assumptions; they do not establish all kernel
inputs or whole-trace behavior. M1 interpretations are per-call. The sequential
retained-heap results share their address interpretation across their specified
calls, but do not establish a global allocator or arbitrary allocation/release
lifetimes. KCOV contents are confined to the proved footprint; their complete
returned sequence is not a WireGuard theorem observable.

Insertion still uses the broader execution-permission premise: first-return
control flow through the random provider is not proved. The bounded callback
increment deliberately leaves that approximately 1,267-instruction obligation
open. Allowed-IPs coverage, index-family coverage and callback proofs do not
constitute coverage of the whole mirrored WireGuard subsystem. No realistic
interrupt, RCU, concurrent-caller, whole-operation or whole-trace contextual
refinement follows from this landing.

## Rebase and validation status

The landing branch now contains main `3f3879e0`, including the three environment
fixes and the register's lag notices. The original experiment remains at
`272104798c4c0cd0acd34212e1ec4712d52d0d66`. Before rebase, the complete default
binary build passed (902 jobs). Rebase conflicts were resolved with the already
reviewable combined harness/documentation versions; the final source tree
differs from the port checkpoint only by main's register updates and removal of
the superseded README trial notice. Final post-rebase validation is pending.

The port's printed headline diff replaces old `Leanux.WG.* : World → ...`
uses with `Binary.Source.*` abbreviations of the actual split adapters, and
changes `World.k.wg` projections to `World.wg.dev`. Existing headline premises
are unchanged. The gate now also prints these abbreviations and `liftWG`, so
the adapter's connection to the operational mirror is visible in the reviewed
surface. It includes the allowed-IPs loop and complete-call sibling headlines
and their two-family witnesses, previously absent from the combined gate.

The private Kraken pin advances to
`dc3824fd5ca36c28b11321b8e7f7e2389b6f6ec4` only to replace the deprecated
`dif_pos` proof rewrite with `dite_eq_left`. Patch 0008 preserves the exact
commit during bootstrap. No instruction semantics change. The mirror has one
compatibility spelling change, `String.mk` to `String.ofList`, for the same
Lean 4.35 deprecation; its packet formatting behavior is unchanged.

Post-rebase build: **PASS**, all 1,263 jobs for `BinaryProofs` and every declared
binary executable, with no warnings. Mirror/harness unit suite: **PASS**,
136 tests, one skipped. Binary Python suite: **PASS**, 15 tests including fresh
reconstruction at the new Kraken pin. The callback runtime suite passes
3,032 KCOV cases and 50 BH cases (51,935 instructions), its conditional-access
controls, and return-overlap rejection.

Exact generation comparisons pass for `Image`, `ServiceImage`, `ImageLayout`,
`Layouts`, `AllowedipsImage`, `AllowedipsLayout`, `IndexMutatorImage`,
`IndexMutatorLayout`, `IndexInsertImage`, and `IndexInsertLayout` against the
pinned s4 ELF. Reproduce with the three `binary/generate*.py --check` commands
listed in the README.

One infrastructure attempt failed before execution: simultaneous lookup
recordings collided in a second-resolution output directory. The launcher now
includes the trace identity and microseconds; that failed recording was
restarted once. No simulation failure is being reclassified as infrastructure.

Fresh workload validation at this checkpoint is **FAIL**: both index traces
(`d1_second_response` and `d1_wrong_receiver_index_same_bucket`) stop at
operation 1 expecting `timer_clk` site 428 but receiving site 8; the allowed-IPs
trace (`b1_trie_routing`) stops at operation 2 expecting site 428 but receiving
site 41. The current mirror requires the B3 timer-wheel records introduced in
s5. The pinned s4 image does not emit them. These are genuine compatibility
failures, not infrastructure outcomes, and no paired-runtime pass is claimed.

The four independent `leanchecker` replays for `PairCallbackSurface`,
`LookupSnapshotTransport`, `PairCallWitness`, and `LookupHitWitness` pass.
They establish kernel acceptance of their built closures, not that the failed
workload preparations succeeded or that the external export gate has passed.

[AGENT 2026-10-19] Assess a bounded s5 port, within the user's authorized
low-cost alternative, because inventing missing timer records or bypassing the
independent differential check would invalidate workload provenance. Read-only
comparison finds identical instruction counts and byte extents for the seven
anchored bodies and the shared callbacks; their changed instructions so far
are relocated branches and RIP-relative loads. The random-provider bodies
also retain their byte extents. Regenerate literal terms, recheck the existing
proofs and run fresh workloads before claiming this alternative works.

## s5 carry of the same statements

[AGENT 2026-10-19] Select the authorized s5 alternative. The mechanical carry
began at approximately 20:56 UTC after the s4 workload failures; the full
1,263-job build and separate gate passed at approximately 21:03 UTC. This is
a relocation carry of existing proofs, not a measurement of new-function
proof cost. The original experiment and its s4 claims are preserved on their
branch. No kernel was rebuilt or modified.

The target is now kernel identity
`b44d958f09743feddc5fdbc3410cb5de89cead4bffdd62b06582b0c560454767`, ELF SHA256
`06513d05fc37506b6cea546e8f11b9fe328e482265341ca41c242157bfa5e88e`, independently
pinned in `binary/kernel-identity-s5.txt` and `TrustBase.lean`. The private
Kraken pin remains `dc3824fd5ca36c28b11321b8e7f7e2389b6f6ec4`.

Read-only symbol/instruction comparison checked the 31 extracted anchor,
callback and random-provider bodies: byte extents and instruction lengths
are unchanged; changed operands are direct branch addresses and RIP-relative
displacements to their relocated static targets. All used DWARF record
layouts agree. The image generators then independently regenerated the Lean
terms and layouts from s5, rather than treating that comparison as a theorem.
All five documented generator `--check` commands pass. Lean re-proved the
existing physical and composed results over those new terms.

The first build failed on six signed decimal address literals missed by the
mechanical substitution. After correcting those literals, **all proof and
executable targets build without warnings (1,263 jobs)**. The printed
trust-surface diff contains only the image identities and relocated service
or random-provider addresses; no hypothesis was added, removed or weakened.
The reviewed baseline was updated explicitly. **The separate binary gate
passes**, including all 48 printed headline axiom checks and the clean private Kraken pin.
The 15 Python tests also pass at the s5 carry.

All six fresh s5 differential recordings pass: the two index lookup traces,
`b1_trie_routing`, removal and replacement profiles of
`c_remove_after_handshake`, and insertion's `s2_index_collision`. Paired lookup
passes 96 calls across the two recordings, each with 17 rejection controls;
the corresponding actual-service instruction totals are 22,404 and 21,774.
Allowed-IPs three-way comparisons pass for operations 5 and 8: 1,592 and 1,510
instructions respectively. The callback suite passes 3,082 generated cases;
the actual random-provider cache/refill/recording suite also passes.

One paired IPv6 synthetic run failed its 10,000-instruction execution budget
at depth 32. That is a failed run. The existing README explicitly specifies
100,000 for this suite (the historical deep case already required 10,994);
the input is regenerated with that documented budget. No theorem precondition,
execution bound in a theorem, or machine behavior changes for this correction.
Fresh exact witnesses, retained-heap tests, capture replays and external
kernel acceptance are reported below when complete.

### Completed runtime checks and gate input

The following runs completed on the s5 carry at code commit `73649245`:

| Check | Result |
| --- | --- |
| Paired allowed-IPs, IPv4 | PASS: 9 cases, 20 calls, 32,918 instructions, 20 controls |
| Paired allowed-IPs, IPv6 (documented budget 100,000) | PASS: 10 cases, 22 calls, 43,514 instructions, 20 controls |
| Original M1 exact miss witness | PASS: 191 instructions, two undefined-value seeds |
| Original M1 exact dead/live hit witnesses | PASS: 441 / 506 instructions, two seeds, owner/count/output and decisions checked |
| Both-family paired call witnesses | PASS: four executions of the exact formal entry states |
| Removal and replacement paired suites | PASS: 54 / 24 calls, 4,550 / 2,174 instructions |
| Insertion paired suite | PASS: 40 calls, 23,450 instructions, supplied random-service returns |
| Non-inserting retained-heap sequences | PASS: 8 sequences, 80 calls, 21,268 instructions |
| Inserting retained-heap sequences | PASS: 32 sequences, 416 calls, 434,064 instructions, actual provider bodies |
| Exact removal/replacement/insertion formal witnesses | PASS: four runs each |

The constructed and mutated cases remain labelled as such. Kernel entry
realism does not follow from a materialized prefix or a positive Pre witness.
Selected actual captures are a separate test channel, reported below.

The combined leanexport finished with exit zero at code commit `73649245`,
root modules `LookupSnapshotTransport`, `LookupWitness`, `LookupHitWitness`,
`AllowedipsWitnessPre`, `PairCallbackSurface`, and `PairCallWitness`, including
their complete declaration closure. It was the disposable
`.tmp/binary-pair-landing.ndjson` (1,649,492,180 bytes), not a committed evidence file.
The user ran the README's `lake check --from-export` command outside Nono
on 2026-10-19. **The Lean default kernel accepted this export**, reporting
only `propext`, `Quot.sound`, and `Classical.choice`. This acceptance is specific
to the port's exported closure; historical exports are not its evidence.

Fresh `leanchecker --fresh` replays also pass for `LookupSnapshotTransport`,
`LookupHitWitness`, `PairCallWitness`, and `PairCallbackSurface`, each including
its imported closure. These local replays do not replace external export
acceptance. The external check was deferred to the final handoff and has now
passed separately, as recorded above.

Landing hygiene: main remains `3f3879e0` and the experiment branch remains
`272104798c4c0cd0acd34212e1ec4712d52d0d66`. `AGENTS.md` and the mirror campaign's
`scripts/proof-gate` match main. The separate binary gate is executable and
self-contained. At that checkpoint the historical removal of the mirror
package's `-j1` option was retained; the landing conditions below restore it.
The library and executable targets remain separate from the default mirror build. No shared
Kraken checkout, oracle image, machine-global configuration, main ref or remote
was changed.

The insertion capture replay's Python preflight now explicitly uses the
binary identity and ELF pin, as the capture commands do. It no longer inherits
main's future oracle identity. The existing identity tests pass (15 Python
tests total), and the new preflight accepts the freshly captured s5 input.
This wrapper-only repair does not alter the Lean closure exported at
`73649245`.

Actual lookup and both-family allowed-IPs captures and replays pass under two
undefined-value seeds. Lookup compares 870,372 captured return bytes over
506 instructions. The trie captures independently record 5 / 3 loop headers,
execute 1,592 / 1,510 instructions, and compare 814,496 / 819,428 captured
return bytes, plus the header bytes; all five corruption controls per family
reject. Both load the complete 32 MiB callback allocation at entry. That full
entry allocation is distinct from the smaller captured return ranges.
Replay elapsed times were about 4 seconds (lookup) and 302 / 289 seconds
(IPv4 / IPv6), with all work capped and concurrent. These remain deliberately
serialized captures with interrupts and timers deferred within each call.

### Final local disposition

All six actual-capture replays finish with exit zero. In addition to lookup
and both trie families above, removal compares 33,625,468 captured bytes over
100 instructions and replacement compares 33,625,500 bytes over 115
instructions, each under both seeds and with their corruption controls.
Insertion compares all 33,626,368 captured endpoint bytes under both seeds,
interprets 1,338 instructions including both actual random-service calls,
and matches 1,354 native stops with exact REP multiplicities. Its full-buffer
replay took approximately 11.4 minutes; it was never truncated, retried,
or reported as passing before completion. No KILLED banner or host timeout
occurred in the final s5 validation. The earlier explicit instruction-budget
failure remains recorded above.

The local acceptance set is complete: warning-free full binary build,
standalone gate (48 headline statements, only the three standard axioms,
clean locked Kraken and reviewed statement/trust diff), five image-generation
comparisons, 136 mirror/harness unit tests (one skip), 15 binary Python tests,
six fresh differential recordings, paired and retained-heap suites, exact
formal-witness executions, four fresh kernel replays, and the six actual
capture replays. The named M1 obligations in the table remain open as stated;
this carry adds no whole-WireGuard or concurrent-context claim.

### External kernel gate acceptance (2026-10-19)

The user reported successful execution **outside Nono**, from the repository
root, of:

```sh
cd .worktrees/binary-pair-landing/binary
capped lake check --from-export ../.tmp/binary-pair-landing.ndjson
```

The accepted export is the Lean closure at
`736492453c292ba9caafa78b353ae19f4ce9671b`, rooted at
`LookupSnapshotTransport`, `LookupWitness`, `LookupHitWitness`,
`AllowedipsWitnessPre`, `PairCallbackSurface`, and `PairCallWitness`.
The default kernel accepted the solution with only `propext`, `Quot.sound`,
and `Classical.choice`. Subsequent changes are the Python identity preflight
and documentation, with no Lean statement
or implementation changes. The landing's validation is complete; theorem
hypotheses and the open obligations above remain unchanged. The original
experiment remains intact, and the landing branch is preserved for the user's
integration decision. Disposable
capture/recording outputs are removed after their conclusions are recorded;
the accepted export is likewise removed after recording this result and can
be regenerated using the command in `binary/README.md`. This gate acceptance
does not authorize a merge to main or a push.

### Landing conditions after the shared proof carry

[USER 2026-10-19] Rebase the landing branch onto the shared proof carry at
`3308c49a` and prepare separate cleanup commits before integration review.
The coordinator owns the package-gate and mirror fast-tier reruns on the
resulting head. No integration or push is authorized by this preparation.

The rebase preserves the existing experiment history and imports the shared
carry without changing `binary/`, the harness, or the evaluator relative to
`9af3b709`. Recreating the historical merge required its original resolutions
in `docs/README.md`, `harness/linux.py`, and `scripts/proof-gate`; none of those
files changed in the shared carry. The mirror proof tree, `AGENTS.md`, and the
mirror gate match `3308c49a`. The experiment branch remains at `272104798c4c0cd0acd34212e1ec4712d52d0d66`.

[AGENT 2026-10-19] Restore the mirror package's `moreLeanArgs = ["-j1"]`
rather than carry a build-policy change as part of this experiment. The root
`lakefile.toml` now matches main `3308c49a` exactly; the binary package's own
settings are unchanged. The coordinator's rerun will validate this restored
setting on the final head.
