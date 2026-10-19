# Shared callback image proofs: increment report

Status: bounded increment complete locally on `task/binary-pair-runner`; external
acceptance pending. Start 2026-10-19 17:24:01 UTC,
baseline `d61a8027`. The [charter](2026-10-19-charter-paired-callbacks.md) governs
the scope and budget. All five image contracts, lookup/remove/replace first-return headlines and the
non-inserting sequence boundary are proved and locally checked. Independent
review findings are repaired. External acceptance of this increment is pending.

## Review and dependency

The independent [charter review](2026-10-19-review-paired-callback-charter.md)
found R1: insertion's first-return claim requires an additional random-service
interior safety proof. Its endpoint frame and input coupling do not imply this.
The finding is accepted; the user chose the bounded revision recorded in the charter.
Five-callback implementation proceeds independently after review, starting
2026-10-19 17:30 UTC. First-return is now scoped to lookup/remove/replace;
insertion and mixed insertion retain the documented broader permission premise.

Baseline assumptions are the five behavioral callback contracts, decoding,
serialized environment and access permissions; insertion additionally uses
RandomReturnContract and RandomInputCoupling. The preceding insertion export
from `5433d7781d9d809b82ea4c19faa13d40af9a4957` remains externally pending.

## Measurements and failures

Preparation and charter review occupied roughly six elapsed minutes. This is
wall time with the independent reviewer running concurrently, not aggregate
person-hours. A read-only Lean API probe exited with errors for three guessed
identifiers; it established the actual load/store definitions, not a passing
build or theorem. Implementation, tests and proof measurements follow below.

### First callback calibration, 17:49 UTC

`CallbackBh.bh_image_contract` proves the existing `BhEnableContract` from
`ServiceImage.fetch`, including modular count subtraction, conditional pending
word reads, its exact memory frame and preserved ABI. The execution retains a
fixed-stack interior guard, useful for the subsequent first-return proof.
`#print axioms` lists only propext, Classical.choice and Quot.sound. This is a
local build result, not yet the external export gate.

Implementation from 17:30 to 17:49 took about 19 elapsed minutes: roughly the
first eight built executable cases, diagnosed runtime parser reduction, and
prepared shared machinery; the remainder developed and debugged the BH proof.
These categories overlap and are approximate, not instrumented task timings.
The proof is 189 lines; the reusable execution module is 78 lines. Remaining
callbacks and first-return integration are still open. This calibration leaves
room in the eight-hour budget, so the increment continues.

The generated suite executes 3,032 coverage cases and 50 BH cases, totaling
51,636 instructions. It tests early returns, modulo wrap, aliased destinations,
argument widths, nested counts and a rejected return-word overlap. These are
generated machine states, not captures. The executable readiness assertions
have ordinary Lean implication proofs to the unchanged named readiness
predicates. Reproduction: `capped lake build binary-callbacks CallbackBh`, then
`capped .lake/build/bin/binary-callbacks`, from `binary/`.

[AGENT 2026-10-19] Service decoding now produces literal instruction terms at
elaboration, as the anchored images already do. The old runtime parser is
retained for a per-listed-instruction executable comparison. Both reject the
unreachable UD2 at the hardirq failure site; rejection remains a failing fetch.
This avoids kernel reduction through a text parser and does not add an ISA
assumption. The external ELF/decoder interpretation remains explicit.

Development failures: the bundle Python lacked elftools (the system Python
regenerated successfully); runtime parser reduction hit recursion/heartbeat
limits; a compile-time parse experiment correctly rejected UD2; intermediate
Lean proofs failed elaboration, arithmetic normalization or framing until
repaired. One edit command used a wrong relative path and made no edit. No
KILLED banner, timeout or sandbox denial occurred. Inherited dependency lint
warnings remain visible; the new modules emit no warnings. The first
successful callback build checked the current complete proof and reported no
sorry axiom; failed intermediate elaborations are not counted as proofs.

### PC callback calibration, 18:00 UTC

The full `pc_image_contract` and ambient-decoder `pc_contract` now build with
only standard axioms, over unchanged `KcovReady .pc`. This includes every
preemption/mode early return, conditional metadata reads, capacity boundary,
64-bit increment wrap and potentially aliased stores. `bh_contract` likewise
transports the first image proof. `ServiceDecoderAgreement` is the explicit
literal-decoder premise; it does not assert callback behavior.

This callback took approximately eleven additional elapsed minutes and 329
function-specific lines, with 70 lines of new reusable memory/arithmetic facts
and 47 lines of decoder transport. The comparison store tail is already proved
using the same framing mechanism. All wrappers and consumers remain open.
`capped lake build CallbackContracts CallbackCmp binary-callbacks` passed; the
same generated suite passed again. New modules have no lint warnings. The
ordinary intermediate elaboration failures primarily concerned numeric
normalization, instruction-state unification and conditional-branch arithmetic;
no counterexample or new readiness restriction was introduced.

### Five callbacks and consumer integration

All five image contracts were complete by 18:06 UTC. The shared comparison
body takes 380 lines; its three wrappers share `wrapper_plan` and
`wrapper_body`, with roughly 24 execution-proof lines per wrapper and a short
contract corollary. This added about six minutes after the PC checkpoint.
The comparison body covers capacity arithmetic and shifts modulo 64 bits,
including wrap and aliased store destinations. No readiness predicate changed.

`CallbackContracts` supplies each contract under only
`ServiceDecoderAgreement`. Fresh replay with
`capped lake env leanchecker --fresh CallbackContracts` exited zero.
`capped lake build PairCallbackAdequacy` passed, printing only standard axioms
for the four single-call and two finite-sequence corollaries. All six reuse
the existing accepted mirror run, reconstruction and physical postconditions;
the five behavioral callback hypotheses have been removed. Insertion and
mixed insertion still explicitly require their random-service and input
coupling contracts. The sequence corollaries retain their broader permission
premises at this intermediate checkpoint. First-return work remains open.

Consumer integration required 151 lines of explicit theorem statements and
applications, with no new physical invariant. The dependency rebuild checked
477 jobs. The generated service suite passed again with unchanged counts.
A temporary simplifier loop in shift normalization failed at the recursion
limit and was replaced by a specific shift-by-three equality; this was an
ordinary proof-development failure, not a changed ISA or hidden assumption.
New-module lints were repaired, including a deprecated theorem alias. External
export acceptance is still pending and no campaign coverage percentage changes
as a result of these shared-service proofs.

### First-return mechanism and mutators, 18:32 UTC

Removal and replacement now export their unchanged physical/reconstruction
postcondition, the actual instruction history, `BeforeOuterReturn`, and
`RunEnvironment` for that same history. The named hypothesis is
`FirstReturnCallPermissions`: access safety on actual prefixes before the
first state with both the supplied return PC and the consumed outer stack
word. The proof establishes the stronger interior stack exclusion, even if
the supplied return PC aliases an image address. Removal's tail-call to
BH-enable is included. No entry predicate, reconstruction or physical
separation premise changed.

`StackCps`, `StackPath` and `region_guarded` retain instruction stack effects
while reusing the physical region calculations. The five callback proofs
supply the same guard through their interiors. There is no executable
certificate classifier or classifier soundness assumption: the small tactic
selects a candidate stack delta, then proves its instruction-semantic lemma.
The first-return compositions currently duplicate the original composition
scripts, sharing their state, frame, arithmetic and source lemmas. This is a
real maintenance cost, not counted as new physical proof discovery.

The local build of `PairRemoveFirstEnvironment` and
`PairReplaceFirstEnvironment` passed (254 jobs), and both headlines print
only the three standard axioms. Approximate elapsed development since the
18:09 integration checkpoint is 23 minutes; a material portion diagnosed
stack automation. Nested machine subtraction expanded into expensive modular
integer cases under `omega`. Direct bit-vector cancellation replaced it and
checks wraparound without an extra range hypothesis. The region tactic also
now chooses stack deltas deterministically before proving them. These fixes
made each new mutator composition module build in approximately 0.7–2.2 s.

Failures in this stage include ordinary elaboration/name-resolution errors,
deterministic heartbeat/recursion failures, and manually terminated diagnostic
Lean runs after their owned PIDs were checked. The `capped` direct-Lean runs
printed KILLED with exit 143 on termination; these are failures, not passes,
and no OOM is inferred from that banner. A wrong-directory edit/build command
also failed without changing the intended file. The final checked mutator
proofs contain no admitted theorem. Lookup first-return, sequence integration,
closing review and external export acceptance remain outstanding.

### Conditional-memory review repairs, 18:45 UTC

The independent review identified two test defects: the fixtures left
conditionally unused metadata mapped, and an initial negative-control helper
accepted any failure. Both are repaired. Seventeen positive cases remove bytes
that the selected path must not read. Thirty-nine negative cases require the
specific expected error and address, so a step-budget failure or unrelated
fetch failure does not pass. Four missing-return-word cases are runner entry
rejections during its initial metadata read, not ISA memory faults.

The reviewer independently reran the executable: 3,032 KCOV cases, 50 BH cases,
17 conditional positives, 39 negatives, and 51,935 instructions in successful
cases. All passed. The review's lookup/sequence boundary finding remains open.

The new `history_guard` lemma recovers an interior guard from a universally
proved complete region history. Its witness selection establishes only the
current guard; the execution proof still retains every undefined branch.
Lookup's ten-instruction prologue, its first callback, and reusable guarded
coverage calls now check using this mechanism and the original memory proofs.
This is intermediate progress, not a lookup first-return theorem. The sibling
composition scripts still duplicate existing bookkeeping; that cost remains
visible in this increment's assessment.

### Lookup and retained-heap composition, 19:07 UTC

The full lookup sibling and non-inserting sequence theorem now build with the
first-return guard. The physical bucket loop, NULL/dead/live peer-get branches,
owner store and BH-enable/epilogue all retain their original entry predicates
and postconditions. `PairLookupFirstEnvironment.lookup_first_return` constructs
its actual history and applies `FirstReturnCallPermissions` to that same history.
`PairSequenceFirstAdequacy.sequence_checked` derives each next Pre from retained
resources and uses `FirstReturnDomainPermissions`. Insertion and mixed insertion
continue to expose the broader permission premise and random-service contracts.

`history_guard_suffix` recovers guards from existing exact region histories.
`guarded_forget` and `guarded_lift` compose endpoint-only segments without claiming
that an arbitrary supplied history is actual; actual history is established
at the outer headline. `GuardedSegment.bind` is used by the bucket-loop sibling.
`guarded_mapped` reuses the ISA memory-preservation proof while retaining the guard.
Stack-slot exclusions are derived by modular cancellation, including wraparound;
they are not new entry hypotheses. Much of the composition and post-processing
remains duplicated and will be counted as such.

The final sequence build passed 468 jobs with standard headline axioms. An
overlapping earlier build failed while writing `PairLookupFootprint.olean`; the
same target subsequently passed in the remaining build. This was an artifact
race between two builds launched here, not a successful check. Subsequent builds
in this worktree are serialized. Ordinary proof elaboration failures during
the sibling conversion were repaired; no failed build is counted as evidence.
Closing review and combined validation are in progress.

The closing review found that sequence composition used the first-return fact
for its permission audit but dropped that fact from the exported postcondition.
The revised `First.SequencePost` now retains `BeforeOuterReturn` for every call
record, proved by the same sequence induction. The rebuilt surface checks with
only standard axioms. A variable-shadowing elaboration error in that repair was
fixed before the successful build. Insertion also has an explicit-environment
`insert_simulation_from_image` corollary, retaining `ReturningCallPermissions`.

### Trust surface and limits

The revised public statements are printed in `PairCallbackSurface.lean`, with
their definitions and full trust declarations diffed by `binary/surface.py`.
The new callback proofs conclude the five existing contracts; they do not
replace them with another behavioral premise. Existing general conditional
lemmas remain available. The preferred new headlines are:

- `IndexLookup.lookup_first_return`, `Remove.remove_first_return`, and
  `Replace.replace_first_return`: unchanged Pre/Post, image decoder agreements,
  `SerializedEnvironment`, and `FirstReturnCallPermissions`.
- `Sequence.First.sequence_checked`: same executable initial resources,
  source-only admissibility and caller preparation; `FirstReturnDomainPermissions`.
  Every call's recorded history exports its first-return boundary.
- `Insert.insert_simulation_from_image` and `InsertSequence.sequence_from_image`:
  proved shared callbacks, but explicit `RandomReturnContract`,
  `RandomInputCoupling` and broader returning-history permissions remain.

All five service interpretations use `ServiceDecoderAgreement`; anchored
functions retain their named decoder agreements. Executable entry checks,
Names/layout interpretation, accepted mirror runs and supplied input assertions
remain explicit domains, not facts about every real kernel entry. The external
ELF bytes/decoder agreement and Kraken's model are interpretation obligations.
The local kernel axiom set is the standard three; external acceptance is pending.

This does not establish concurrent contextual refinement, IRQ/preemption/RCU
interleavings, compiled caller execution, allocation/free correctness, or whole
WireGuard operation/trace simulation. BH-enable covers its original physically
ready no-pending-work domain, including nested counts; pending work is not
proved absent in every real invocation. Insertion's random-service interior
first-return safety remains outside this increment. Tests of those bodies do
not discharge their universal contracts. Allowed-IPs' additional comparison
contracts and the original M2 correspondence theorem remain separate work.
Reconstructed recorded prefixes and generated witness states are not captured
kernel snapshots and do not prove entry reachability. No new campaign function
coverage or campaign-wide throughput claim follows. The mirror baseline is
`cb2348e`, lagging current main; no merge was performed.

### Cost and scientific assessment

At code checkpoint `86ea5488`, the increment adds 90 Lean modules and 10,170
lines (including comments, declarations, tests and surface printing). This is
gross new source, not a reduction in the original proof tree. Of those lines,
1,742 are callback machinery/proofs/tests; 8,220 are first-return machinery and
sibling compositions; 208 are consumer corollaries and the export root. The
1,742 include 269 lines of executable tests/readiness checks. Large parts of
the 8,220 copy already-proved composition/post-processing while importing the
original physical regions. They are not 8,220 lines of new ISA discovery.

| Work | Approximate elapsed interval | Result |
|---|---|---|
| Charter and independent dependency review | 17:24–17:30, 6 min | Bounded random-service scope |
| First BH callback, including initial test/decoder work | 17:30–17:49, 19 min | Existing conditional contract proved |
| PC callback and reusable memory/decoder facts | 17:49–18:00, 11 min | Full existing readiness domain |
| Shared comparison body and three wrappers | 18:00–18:06, 6 min | One common execution body |
| Initial six consumer corollaries | 18:06–18:09, 3 min | Callback hypotheses discharged |
| First-return mechanics, mutators, lookup and sequences | 18:09–19:08, 59 min | Same Pre/R, stronger history/post |

The final interval overlaps independent review, test repairs and build time.
These are wall-clock checkpoints, not measured person-hours; aggregate compute
time and individual diagnosis/search time were not instrumented. The first
callback's test/diagnosis split is approximate as recorded above. The initial
consumer applications required no new physical invariant; subsequent wrappers
share their comparison proof and take roughly 24 execution-proof lines each.

The experiment supports reusable service proofs: five behavioral assumptions
are removed from every revised client at a small application cost. It also
shows that changing a global history guarantee remains expensive in source
volume. Execution regions were reused, but the original composition interfaces
did not retain the stack information needed by the permission theorem. The
new guard mechanism avoids repeating instruction calculations; it does not
yet remove duplicated frame and postcondition bookkeeping. Independent review
identified factoring those pure post-processing implications as a concrete next
refactoring opportunity. It is outside this increment. No campaign forecast
is inferred from these timings.

Review found missing test coverage, an overly permissive negative-test
verdict and the sequence's missing exported boundary. Test reruns and the
rebuilt postcondition verify those repairs. No callback
contract/readiness defect or new ISA gap was discovered in this bounded domain.
The evidence supports the fail-early workflow and shared proof reuse, but does
not establish that broader mutation/lifecycle proofs have become inexpensive.

### Closing validation and reproduction

Code checkpoint: `86ea5488`. Oracle ELF hash rechecked as
`16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774`; private
Kraken remains clean at `cd2ae360bfcf8e1fc719793405811ff49c3e75ce`. No mirror,
harness, kernel, AGENTS.md, main or other-worktree change was made.

- Generated callbacks: 3,032 KCOV, 50 BH, 17 conditional-memory positives,
  39 exact negative outcomes; 51,935 successful instructions.
- Lookup/removal/replacement independent three-way comparisons passed before
  sequence execution. Lookup: 48 paired calls, 94 headers, 22,404 instructions,
  17 controls, 6.107 s. Removal: 54 calls, 4,550 instructions, 2.561 s;
  replacement: 24 calls, 2,174 instructions, 1.245 s. Inputs are reconstructed recorded prefixes and labelled variants.
- Eight non-inserting sequences: 80 calls, 21,268 instructions, 3.050 s.
- Insertion three-way comparison passed, six cases, 3.901 s; this particular
  runner executes real shared callbacks with supplied random returns.
- Thirty-two mixed insertion sequences: 416 calls, 434,064 instructions,
  62.673 s, retaining the heap and running the initialized random-service body.
- Exact formal witness states: removal and replacement each execute eight
  calls including repeats; insertion executes four states to return, two seeds
  for linked/unlinked entries, including its actual initialized provider body.
- The revised surface and runtime targets build (850 jobs). Six trust-gate
  unit tests pass. All revised headline axiom reports list only `propext`,
  `Classical.choice`, `Quot.sound`; new modules emit no compiler warnings.
  Inherited warnings remain visible in unchanged dependencies, including the
  mirror's deprecated string constructor and old unused simplifier arguments.
- Full default build (883 jobs), headline axiom checks, source-escape scan,
  pinned-clean-Kraken check and printed trust-surface diff all pass through
  `scripts/proof-gate --binary`.
- `leanexport PairCallbackSurface` exited zero at code commit
  `86ea5488e288998ea4aa0b26335c64428ffeaf04`: 1,331,952,229 bytes. This root includes
  the new callback/first-return clients and the earlier index/insertion
  surfaces, formal witnesses, TrustBase and Execution through its import closure.
  External acceptance remains pending; earlier gate acceptance is not reused.
- Final `capped lake env leanchecker --fresh PairCallbackSurface` exited zero
  for the committed code closure. This was rerun after adding the explicit
  insertion environment corollary; the earlier successful replay alone was
  not used to claim that later corollary was checked.
- Identity-verified actual captured insertion replay exited zero under both
  seeds: 33,626,368 captured bytes compared per run, 1,338 interpreted
  instructions, 1,354 native stops with exact REP multiplicities, two random
  services, unchanged 4,194,304-word KCOV capacity. The captured system-flag
  corruption control rejects as expected. This is actual captured memory,
  unlike the reconstructed-prefix/generated tests above. It took approximately
  eleven minutes; the existing full-buffer comparison dominates closing test
  runtime. The generated callback suite took under one second. No capture
  optimization or reduced-capacity substitution was introduced.
- All independent findings R1–R3 are repaired and rechecked. R3's sequence
  postcondition repair retains the first-return fact for every recorded call.
  The review finds no remaining proof-surface blocker.

Local closing checkpoint: 2026-10-19 19:22 UTC, approximately 1 hour 58 minutes
after the recorded start, within the eight-hour budget. This elapsed figure
includes concurrent review and validation, not aggregate agent/CPU time.
The combined external gate was requested for the export above and remains
pending. No merge or push was performed. Source-code changes stop at
`86ea5488`; the closing documentation commit records the result.

Additional command failures during closure were ordinary missing-import and
wrong-relative-path errors, repaired before the successful checks. The missing
import arose while adding the insertion environment corollary. No final check
was replaced with a passing interpretation of those failures.

From the worktree root (existing recordings are reproducible by the preceding
increment's README recipes):

```sh
LEANUX_QEMU_SLOTS=16 capped python3 -B binary/sequence_probe.py \
  --lookup-check .artifacts/check/binary-tv-20261016-234706 \
  --remove-check .artifacts/check/binary-remove-20261018 \
  --replace-check .artifacts/check/binary-replace-20261018
LEANUX_QEMU_SLOTS=16 capped python3 -B binary/insert_probe.py \
  --check .artifacts/check/binary-insert
LEANUX_QEMU_SLOTS=16 capped python3 -B binary/insert_sequence_probe.py \
  --base-input .tmp/binary-sequence/input.json --insert-input .tmp/binary-insert/input.json
capped scripts/proof-gate --binary
```

Use a Python environment with the documented ELF dependencies. From `binary/`:

```sh
capped lake build PairCallbackSurface binary-callbacks
capped .lake/build/bin/binary-callbacks
capped lake env leanchecker --fresh PairCallbackSurface
capped lake env leanexport PairCallbackSurface > ../.tmp/binary-pair-callbacks.ndjson
# Outside nono, after export exits zero:
capped lake check --from-export ../.tmp/binary-pair-callbacks.ndjson
```

The captured regression is reproducible after regenerating the capture using
the insertion README recipe (the prior reviewed capture includes the dropped
record counter):

```sh
capped python3 -B binary/pair_insert_capture.py .tmp/binary-insert/input.json \
  .tmp/cap-index-insert-dropped/snapshot.json .tmp/cap-index-insert-dropped/layouts.json
```

### TrustBase.lean, verbatim at the code checkpoint

This includes the older general interfaces and allowed-IPs obligations, not
only the hypotheses used by this increment's preferred headlines. Definitions
of contracts are propositions, not axioms. The revised headlines above show
which remain hypotheses and which the image theorems discharge.

```lean
import FiniteExecution
import Image
import IndexMutatorImage
import IndexInsertImage
import AllowedipsImage
import ServiceImage
import Memory
import LookupProjection
import AllowedipsProjection
import AllowedipsSelection
import AllowedipsWords
import RandomState
import PairInsertInput

/-! Named trust surface for the pinned lookup proof, under construction.
    These are explicit hypotheses, not globally asserted facts. No declaration
    here assumes the lookup result, a region's R-preservation, or a mirror run.
    Pre_lookup is accompanied by its concrete satisfying witness.
    The final milestone report must reproduce this file verbatim.

    External interpretation: binutils 2.42 supplied the literal AST and DWARF
    layouts from the ELF below. Lean checks execution of those terms, not the
    binutils decoder, DWARF producer, SHA computation or correspondence of
    Kraken's model with x86 hardware. The loader checks identity and branch
    encodings. Mutable runtime globals are NOT assumed equal to ELF initial
    bytes at a function entry; their current values belong in Pre_lookup.
    A fixed fetch models stable text; the external ELF interpretation requires
    no runtime text patch in these ranges. Independent review measured no
    alternatives entry in the ranges, no jump table, empty smp_locks, no RET
    thunk rewriting, and no GS use. These are interpretation facts, not unused
    Lean premises. Permissions and serialization below are headline hypotheses.

-/
namespace Binary.TrustBase

def krakenCommit : String := "cd2ae360bfcf8e1fc719793405811ff49c3e75ce"
def kernelIdentity : String := "6b2018b99f086345ce9fa316a89c76d27b40b536d5feb4402510e5fb62a5ae24"
def elfSha256 : String := "16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774"
def decoderVersion : String := "GNU objdump (GNU Binutils for Ubuntu) 2.42"

local instance : Labels := Image.linkedLabels

/-- The partial linked decoder for both anchored functions and all reached
    service bodies. A rejected instruction remains a failing fetch; neither
    its semantics nor successful execution is assumed by this definition. -/
def pinnedFetch (pc : Int64) : Option Decoded :=
  (Image.fetch pc).orElse (fun _ => ServiceImage.fetch pc)

/-- The ambient decoder agrees with the pinned literal instructions/lengths.
    Interpreting those literals as this ELF is the external decoding assumption. -/
def AnchoredDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, Image.fetch pc = some instruction → fetch pc = some instruction

/-- Literal instructions and lengths of the five shared index services.
Their behavior is proved from these terms, rather than assumed separately. -/
def ServiceDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, ServiceImage.fetch pc=some instruction → fetch pc=some instruction

/-- Sequential paired removal uses the same pinned ELF interpretation, with
its separately generated literal instruction range. -/
def IndexRemoveDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, IndexMutatorImage.Remove.fetch pc = some instruction → fetch pc = some instruction

/-- The separately generated replacement range of the same pinned ELF. -/
def IndexReplaceDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, IndexMutatorImage.Replace.fetch pc = some instruction → fetch pc = some instruction

/-- External paging/access permissions, absent from Kraken MachineState. -/
structure Permissions where
  read : BitVec 64 → Width → Prop
  write : BitVec 64 → Width → Prop
  execute : Std.Rco Int64 → Prop

/-- Kraken's All grants permission requests. This separate premise makes
    that grant explicit for every effect, including every undefined outcome. -/
def AccessAllowed (permissions : Permissions) : Effects → Prop
  | .done _ => True
  | .unimplemented _ | .gp_unaligned .. | .nonmem_load .. | .nonmem_store .. => False
  | @Effects.undefined α _ next => ∀ value : α, AccessAllowed permissions (next value)
  | .require_read_access address width next =>
      permissions.read address width ∧ AccessAllowed permissions (next ())
  | .require_write_access address width next =>
      permissions.write address width ∧ AccessAllowed permissions (next ())
  | .require_exec_access pc next =>
      permissions.execute pc ∧ AccessAllowed permissions (next ())

/-- Every actually executed instruction has its requested accesses granted;
    the final return destination is not itself executed by this run. -/
def RunAccessAllowed (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, ∃ decoded, fetch s.pc = some decoded ∧
    permissions.execute ⟨s.pc, s.pc + .ofNat decoded.size⟩ ∧
    AccessAllowed permissions
      (decoded.instruction.interp s.data ⟨s.pc, s.pc + .ofNat decoded.size⟩
        (fun d => .done ⟨d, s.pc + .ofNat decoded.size⟩) (fun pc d => .done ⟨d, pc⟩))

/-- The environment places no interrupt, preemption or competing CPU action
    inside this anchored call; the records place such actions between calls. -/
structure SerializedEnvironment (onlineCPUs : Nat) (externalActions : List Nat) : Prop where
  singleCPU : onlineCPUs = 1
  noInterleaving : externalActions = []

/-- Permission safety of finite actual prefixes through the first outer RET.
    This is safety only: no termination, source result or relation is assumed.
    Service interiors are included; the unexecuted return destination is not. -/
def InvocationPermissions (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (initial : MachineState) (returnPC : Int64) : Prop :=
  ∀ history, ActualHistory fetch initial history → NoEarlyReturn returnPC history →
    RunAccessAllowed fetch permissions history

/-- The exported interpretation audit of this actual instruction history. -/
def RunEnvironment (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (onlineCPUs : Nat) (externalActions : List Nat) (history : List MachineState) : Prop :=
  SerializedEnvironment onlineCPUs externalActions ∧ RunAccessAllowed fetch permissions history

/-- Kernel ABI: the stack word is the actual CALL return address. Eight-byte
    alignment follows this kernel's compiler flags, not a userspace ABI guess. -/
def EntryFrame (s : MachineState) (returnAddress : UInt64) : Prop :=
  s.data.regs.rsp.toNat % 8 = 0 ∧
  s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 = some (returnAddress.toNat : Int)

/-- Only ABI-preserved registers are constrained; caller-save registers and
    flags may change. The callee has consumed the actual return-address word. -/
def Returned (entry final : MachineState) (returnAddress : UInt64) : Prop :=
  final.pc = .ofBitVec returnAddress.toBitVec ∧
  final.data.regs.rsp = entry.data.regs.rsp + 8 ∧
  final.data.regs.rbx = entry.data.regs.rbx ∧
  final.data.regs.rbp = entry.data.regs.rbp ∧
  final.data.regs.r12 = entry.data.regs.r12 ∧
  final.data.regs.r13 = entry.data.regs.r13 ∧
  final.data.regs.r14 = entry.data.regs.r14 ∧
  final.data.regs.r15 = entry.data.regs.r15

/-- No earlier state has reached the outer ABI boundary. Both the supplied
return PC and consumed return-word stack position matter; internal RETs and
an alias between the return PC and image code do not define this boundary. -/
def BeforeOuterReturn (initial : MachineState) (returnAddress : UInt64)
    (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, ¬(s.pc=returnAddress.toInt64 ∧
    s.data.regs.rsp=initial.data.regs.rsp+8)

/-- Access safety only for actual prefixes before the first outer ABI
return, including the instruction that reaches it. This assumes neither
termination nor a source result, and omits the unexecuted continuation. -/
def FirstReturnCallPermissions (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (initial : MachineState) (returnAddress : UInt64) : Prop :=
  ∀ history, ActualHistory fetch initial history → BeforeOuterReturn initial returnAddress history →
    RunAccessAllowed fetch permissions history

/-- The same prefix permission premise for caller-prepared entry states. -/
def FirstReturnDomainPermissions (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (returnAddress : UInt64) (domain : MachineState → Prop) : Prop :=
  ∀ initial, domain initial → FirstReturnCallPermissions fetch permissions initial returnAddress

/-- External access safety for actual finite histories completing this ABI
call, including service interiors. It asserts no run exists, no source
result, and no reconstruction. The unexecuted caller continuation is omitted.
This form also covers a function that tail-calls its returning service. -/
def ReturningCallPermissions (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (initial : MachineState) (returnAddress : UInt64) : Prop :=
  ∀ history final, ActualHistory fetch initial history → history.getLast?=some final →
    Returned initial final returnAddress → RunAccessAllowed fetch permissions history

/-- The same explicit permission premise for a family of caller-prepared
entries. It grants access on actual returning histories; it neither asserts
their existence nor supplies any future reconstruction or precondition. -/
def ReturningDomainPermissions (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (returnAddress : UInt64) (domain : MachineState → Prop) : Prop :=
  ∀ initial, domain initial → ReturningCallPermissions fetch permissions initial returnAddress

/-- Service internals emit no anchored observation or cut. The final state
    may return to an anchored address; it is deliberately not excluded. -/
def NoAnchoredReentry (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, Image.fetch s.pc = none

/-- A service contract uses the same fetched-instruction execution as the
    function proof. Its readiness and write footprint are physical predicates;
    their concrete instantiations must be part of the witnessed entry domain. -/
def ServiceReturns (fetch : Int64 → Option Decoded) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop) : Prop :=
  ∀ s returnAddress, s.pc = address → ready s → EntryFrame s returnAddress →
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧
        effect s t.machine ∧ NoAnchoredReentry t.history)
      ⟨s, [s]⟩

def preemptCountAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c8
def currentTaskAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c0
def softirqPendingAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85e0

inductive KcovKind where
  | pc | cmp1 | cmp4 | cmp8 | constCmp4 | constCmp1
  deriving DecidableEq

structure WordWrite where
  address : BitVec 64
  value : BitVec 64

def load64 (memory : Mem 64) (address : BitVec 64) : Option (BitVec 64) :=
  (memory.loadInt address 8).map (.ofInt 64)

def load32 (memory : Mem 64) (address : BitVec 64) : Option (BitVec 32) :=
  (memory.loadInt address 4).map (.ofInt 32)

/-- Physical callback metadata, fixed during an anchored call except for the
    separately balanced preempt count. Capacity is a count of 64-bit words. -/
structure KcovLayout where
  task : BitVec 64
  area : BitVec 64
  capacity : BitVec 32
  mode : BitVec 32
  softirqEnabled : BitVec 32

/-- Exact runtime metadata reads, not the ELF's initial global bytes. -/
def KcovMetadata (layout : KcovLayout) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some layout.task ∧
  load32 memory (layout.task + 0x6e0) = some layout.mode ∧
  load32 memory (layout.task + 0x6e4) = some layout.capacity ∧
  load64 memory (layout.task + 0x6e8) = some layout.area ∧
  load32 memory (layout.task + 0x704) = some layout.softirqEnabled

/-- Mapped buffer and bounded runtime header. A full buffer is allowed; no
    callback is required to have room for a record. This predicate says
    nothing about the peer state or the lookup result. -/
def KcovBuffer (layout : KcovLayout) (memory : Mem 64) : Prop :=
  (∀ word < layout.capacity.toNat,
    (memory.loadInt (layout.area + .ofNat 64 (8 * word)) 8).isSome = true) ∧
  ∃ count : Nat, count ≤ layout.capacity.toNat ∧
    load64 memory layout.area = some (.ofNat 64 count)

def KcovBufferBytes (layout : KcovLayout) : BitVec 64 → Prop :=
  InRange layout.area (8 * layout.capacity.toNat)

/-- Storage read by an active callback. Even capacity zero still requires
    the header; caller writes must preserve it as well as the buffer words. -/
def KcovStorageBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  InRange layout.area 8 address ∨ KcovBufferBytes layout address

def KcovMetadataBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 address ∨
  InRange (layout.task + 0x6e0) 4 address ∨
  InRange (layout.task + 0x6e4) 4 address ∨
  InRange (layout.task + 0x6e8) 8 address ∨
  InRange (layout.task + 0x704) 4 address

/-- Physical disjointness from protected memory (metadata, live stack and
    represented objects). Readiness is proved from this, not assumed at
    every callback. The caller chooses the actual protected footprint. -/
def KcovSeparated (layout : KcovLayout) (protectedBytes : BitVec 64 → Prop) : Prop :=
  ∀ address, KcovBufferBytes layout address → ¬protectedBytes address

/-- Physical state carried between callbacks. Disabled tracing requires no
    mapped coverage area; the mode field itself still belongs to the task. -/
def KcovState (layout : KcovLayout) (preempt : BitVec 32) (memory : Mem 64) : Prop :=
  KcovMetadata layout memory ∧
  load32 memory preemptCountAddress = some preempt ∧
  (layout.mode = 2 ∨ layout.mode = 3 → KcovBuffer layout memory)

/-- Bytes that caller stores must preserve. Buffer storage is needed only
    in an active mode; metadata and preemption state are always physical. -/
def KcovStateBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  KcovMetadataBytes layout address ∨ InRange preemptCountAddress 4 address ∨
    ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout address)

/-- KCOV comparison record encoding: width in bits 1..2, constant bit 0. -/
def KcovRecordTag : KcovKind → BitVec 64
  | .pc => 0 | .cmp1 => 0 | .cmp4 => 4 | .cmp8 => 6
  | .constCmp4 => 5 | .constCmp1 => 1

/-- Callback argument width is fixed by the called entry point. -/
def KcovArgument (kind : KcovKind) (s : MachineState) (reg : Reg64) : BitVec 64 :=
  if kind = .constCmp1 ∨ kind = .cmp1 then (s.data.regs.get (.low reg .W8)).setWidth 64
  else if kind = .cmp8 then s.data.regs.get64 reg
  else (s.data.regs.get (.low reg .W32)).setWidth 64

/-- Physical KCOV callback specification, with the actual early-return read
    dependencies and machine-width arithmetic. It is not a proof checker. -/
def KcovPlan (kind : KcovKind) (s : MachineState) : Option (List WordWrite) := do
  let memory := s.data.dmem
  let preempt ← load32 memory preemptCountAddress
  let returnPC ← load64 memory s.data.regs.rsp.toBitVec
  let task ← load64 memory currentTaskAddress
  if preempt &&& 0xff0100 != 0 then
    if preempt &&& 0x100 == 0 || preempt &&& 0xff0000 != 0 then return []
    let softirqEnabled ← load32 memory (task + 0x704)
    if softirqEnabled == 0 then return []
  let mode ← load32 memory (task + 0x6e0)
  if mode != (if kind = .pc then 2 else 3) then return []
  let area ← load64 memory (task + 0x6e8)
  let capacity ← load32 memory (task + 0x6e4)
  let count ← load64 memory area
  if kind = .pc then
    let next := count + 1
    if next.toNat ≥ capacity.toNat then return []
    return [⟨area, next⟩, ⟨area + 8 * next, returnPC⟩]
  else
    let slot := 4 * count
    let ending := 8 * slot + 40
    if 8 * (capacity.setWidth 64) < ending then return []
    let tag := KcovRecordTag kind
    let arg1 := KcovArgument kind s .rdi
    let arg2 := KcovArgument kind s .rsi
    return [⟨area, count + 1⟩, ⟨area + ending - 32, tag⟩,
      ⟨area + ending - 24, arg1⟩, ⟨area + ending - 16, arg2⟩,
      ⟨area + ending - 8, returnPC⟩]

/-- Planned destinations are mapped and do not overwrite the return word.
    Separation from all represented objects is an additional entry obligation. -/
def KcovReady (kind : KcovKind) (s : MachineState) : Prop :=
  ∃ stores, KcovPlan kind s = some stores ∧
    ∀ write ∈ stores,
      (s.data.dmem.loadInt write.address 8).isSome = true ∧
      ∀ address, InRange write.address 8 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

def KcovWrites (kind : KcovKind) (s : MachineState) (address : BitVec 64) : Prop :=
  ∃ stores, KcovPlan kind s = some stores ∧
    ∃ write ∈ stores, InRange write.address 8 address

/-- Exact callback stores keep repeated-call buffer readiness provable;
    allowing arbitrary corruption of the coverage buffer would not suffice. -/
def KcovEffect (kind : KcovKind) (before after : MachineState) : Prop :=
  ∃ stores, KcovPlan kind before = some stores ∧
    after.data.dmem = stores.foldl
      (fun memory write => memory.storeInt write.address 8 write.value.toInt) before.data.dmem

/-- KCOV PC callback: only its physically planned stores may occur. -/
def TracePcContract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)

/-- KCOV variable/variable 32-bit comparison callback. -/
def TraceCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4)

/-- KCOV constant/variable 32-bit comparison callback. -/
def TraceConstCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4)
    (KcovWrites .constCmp4) (KcovEffect .constCmp4)

/-- KCOV constant/variable 8-bit comparison callback used by peer-get. -/
def TraceConstCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1)
    (KcovWrites .constCmp1) (KcovEffect .constCmp1)

/-- The actual no-work BH-enable path, including nested disable counts.
    The softirq word is needed only on the branch that reads it. -/
def BhEnableReady (s : MachineState) : Prop :=
  ∃ count : BitVec 32,
    s.data.dmem.loadInt preemptCountAddress 4 = some (count.toNat : Int) ∧
    count &&& 0x000f0000 = 0 ∧
    ((count + 1 - s.data.regs.get (.low .rsi .W32)) &&& 0x00ffff00 = 0 →
      s.data.dmem.loadInt softirqPendingAddress 2 = some 0) ∧
    ∀ address, InRange preemptCountAddress 4 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

/-- BH enable balances the actual low-32-bit count argument, modulo 2^32.
    Readiness must justify that its softirq path runs no pending work. -/
def BhEnableContract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810732c0) BhEnableReady
    (fun _ => InRange preemptCountAddress 4)
    (fun before after => ∀ old : BitVec 32,
      before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) →
      after.data.dmem.loadInt preemptCountAddress 4 =
        some ((old - before.data.regs.get (.low .rsi .W32)).toNat : Int))

/-- Additional anchored decoder domain for M2; M1 agreement is separate
    because peer-get is shared. The linked-label interpretation is unchanged. -/
def AllowedipsDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, AllowedipsImage.fetch pc = some instruction → fetch pc = some instruction

/-- A callback's interior is not another anchored M2 invocation. -/
def NoAllowedipsReentry (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, AllowedipsImage.fetch s.pc = none

/-- M2 uses the same physical callback specification, with its additional
    anchored ranges excluded from callback interiors. The original M1
    contracts and their hypotheses remain unchanged. -/
def AllowedipsServiceReturns (fetch : Int64 → Option Decoded) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop) : Prop :=
  ∀ s returnAddress, s.pc = address → ready s → EntryFrame s returnAddress →
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧
        effect s t.machine ∧ NoAnchoredReentry t.history ∧ NoAllowedipsReentry t.history)
      ⟨s, [s]⟩

def AllowedipsTracePcContract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3100)
    (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)

def AllowedipsTraceCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3e40)
    (KcovReady .cmp1) (KcovWrites .cmp1) (KcovEffect .cmp1)

def AllowedipsTraceCmp8Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3ea0)
    (KcovReady .cmp8) (KcovWrites .cmp8) (KcovEffect .cmp8)

def AllowedipsTraceConstCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3ec0)
    (KcovReady .constCmp1) (KcovWrites .constCmp1) (KcovEffect .constCmp1)

def AllowedipsTraceConstCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3f00)
    (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4)

/-- As in M1, this contract covers the no-pending-work BH-enable path.
    M2's Pre must justify the actual read conditions and stack separation. -/
def AllowedipsBhEnableContract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810732c0) BhEnableReady
    (fun _ => InRange preemptCountAddress 4)
    (fun before after => ∀ old : BitVec 32,
      before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) →
      after.data.dmem.loadInt preemptCountAddress 4 =
        some ((old - before.data.regs.get (.low .rsi .W32)).toNat : Int))

/-- Whether the actual callback reads softirqEnabled before its mode test. -/
def LookupSoftRead (preempt : BitVec 32) : Prop :=
  preempt &&& 0xff0100 ≠ 0 ∧
  ¬(preempt &&& 0x100 = 0 ∨ preempt &&& 0xff0000 ≠ 0)

/-- The callback reaches its mode read only after the preemption/softirq gate. -/
def LookupModeRead (coverage : KcovLayout) (preempt : BitVec 32) : Prop :=
  if preempt &&& 0xff0100 ≠ 0 then
    ¬(preempt &&& 0x100 = 0 ∨ preempt &&& 0xff0000 ≠ 0) ∧ coverage.softirqEnabled ≠ 0
  else True

/-- PC callbacks occur before and after BH-disable. Comparisons occur only
    with a nonempty selected bucket, after the actual modular increment. -/
def LookupBufferNeeded (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) : Prop :=
  (coverage.mode = 2 ∧ (LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt))) ∨
  (coverage.mode = 3 ∧ v.bucket ≠ [] ∧ LookupModeRead coverage (512+preempt))

/-- Only callback metadata reached in one of this lookup's two contexts.
    Unused layout values impose no equality on memory. The active coverage
    allocation is mapped uniformly; a full buffer is permitted. -/
def LookupCoverageAt (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some coverage.task ∧
  ((LookupSoftRead preempt ∨ LookupSoftRead (512+preempt)) →
    load32 memory (coverage.task+0x704) = some coverage.softirqEnabled) ∧
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt)) →
    load32 memory (coverage.task+0x6e0) = some coverage.mode) ∧
  (LookupBufferNeeded coverage preempt v →
    load32 memory (coverage.task+0x6e4) = some coverage.capacity ∧
    load64 memory (coverage.task+0x6e8) = some coverage.area ∧ KcovBuffer coverage memory)

def LookupMetadataBytes (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨
  ((LookupSoftRead preempt ∨ LookupSoftRead (512+preempt)) ∧ InRange (coverage.task+0x704) 4 a) ∨
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt)) ∧ InRange (coverage.task+0x6e0) 4 a) ∨
  (LookupBufferNeeded coverage preempt v ∧
    (InRange (coverage.task+0x6e4) 4 a ∨ InRange (coverage.task+0x6e8) 8 a))

def LookupCoverageWrites (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupBufferNeeded coverage preempt v ∧ KcovBufferBytes coverage a

def LookupServiceBytes (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupMetadataBytes coverage preempt v a ∨ InRange preemptCountAddress 4 a ∨
  (LookupBufferNeeded coverage preempt v ∧ KcovStorageBytes coverage a)

/-- The helper is called for a selected owner even when its peer word is NULL. -/
def LookupStackWords (c : LookupRelation.Config) : Nat := if c.focus.owner.isSome then 13 else 6

def LookupStackWrites (c : LookupRelation.Config) (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c)

def LookupLiveStack (c : LookupRelation.Config) (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c+8)

def LookupBucketBytes (c : LookupRelation.Config) (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  InRange (c.table + .ofNat 64 (8*(c.query%8192))) 8 a ∨
  ∃ e ∈ v.bucket, BucketShapeReads (LookupRelation.ownerAddress c e.owner) a

def LookupOwnerBytes (c : LookupRelation.Config) (a : BitVec 64) : Prop :=
  ∃ owner, c.focus.owner = some owner ∧ InRange (LookupRelation.ownerAddress c owner) 8 a

def LookupCountBytes (c : LookupRelation.Config) (a : BitVec 64) : Prop :=
  ∃ pid, c.focus.peer = some pid ∧ InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a

def LookupDataWrites (c : LookupRelation.Config) (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupOwnerBytes c a ∨ ((∃ n, v.count = some n ∧ n ≠ 0) ∧ LookupCountBytes c a)

/-- A conditional output requirement, not a count bound on the entry domain.
    Dead, NULL, miss and rejected-saturation inputs need no output storage. -/
def LookupOutputNeeded (v : LookupRelation.View) : Prop :=
  ∃ n, v.count = some n ∧ n ≠ 0 ∧ n+1 < 2^31

def LookupOutputWrites (v : LookupRelation.View) (s : MachineState) (a : BitVec 64) : Prop :=
  LookupOutputNeeded v ∧ InRange s.data.regs.rcx.toBitVec 8 a

def LookupPendingRead (preempt : BitVec 32) : Prop := (preempt+1) &&& 0x00ffff00 = 0

/-- Named physical entry obligations. Separation is an explicit allocation
    discipline, not a claim that every safe x86 alias is admitted. No live-
    peer or positive-count invariant is imposed. Every byte range belongs
    to lookup, its helper, its stack or its named service callbacks. -/
structure LookupEntry (c : LookupRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState)
    (world : Leanux.World) (v : LookupRelation.View) : Prop where
  pc : s.pc = Image.Lookup.entry
  frame : EntryFrame s returnAddress
  table : s.data.regs.rdi.toBitVec = c.table
  query : (s.data.regs.get (.low .rdx .W32)).toNat = c.query
  kinds : KindMask (s.data.regs.get (.low .rsi .W32)) c.kinds
  projected : LookupRelation.project c world = some v
  focus : LookupRelation.EntryFocus c v
  physical : LookupRelation.Physical c [s] [LookupObservation.call "wg_index_hashtable_lookup" s] s v
  steps : world.steps.toList = c.incomingSteps
  rxSection : world.netRxSection = c.rxSection
  coverageAt : LookupCoverageAt coverage preempt v s.data.dmem
  preemptAt : load32 s.data.dmem preemptCountAddress = some preempt
  stackMapped : ∀ n < LookupStackWords c,
    (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true
  outputMapped : LookupOutputNeeded v → (s.data.dmem.loadInt s.data.regs.rcx.toBitVec 8).isSome = true
  bhHardirq : (512+preempt) &&& 0x000f0000 = 0
  bhPending : LookupPendingRead preempt → s.data.dmem.loadInt softirqPendingAddress 2 = some 0
  readsScratch : ∀ a, LookupRelation.Reads c v a →
    ¬(LookupStackWrites c s a ∨ LookupCoverageWrites coverage preempt v a ∨ InRange preemptCountAddress 4 a)
  serviceStack : ∀ a, LookupServiceBytes coverage preempt v a → ¬LookupStackWrites c s a
  coverageStack : ∀ a, LookupCoverageWrites coverage preempt v a → ¬LookupLiveStack c s a
  coverageMetadata : ∀ a, LookupCoverageWrites coverage preempt v a → ¬LookupMetadataBytes coverage preempt v a
  coveragePreempt : ∀ a, LookupCoverageWrites coverage preempt v a → ¬InRange preemptCountAddress 4 a
  bhStack : ∀ a, InRange preemptCountAddress 4 a → ¬LookupLiveStack c s a
  bhMetadata : ∀ a,
    (LookupMetadataBytes coverage preempt v a ∨
      (LookupBufferNeeded coverage preempt v ∧ KcovStorageBytes coverage a)) →
    ¬InRange preemptCountAddress 4 a
  dataService : ∀ a, LookupServiceBytes coverage preempt v a → ¬LookupDataWrites c v a
  dataReturn : ∀ a, InRange s.data.regs.rsp.toBitVec 8 a → ¬LookupDataWrites c v a
  dataBucket : ∀ a, LookupBucketBytes c v a → ¬LookupDataWrites c v a
  ownerCount : ∀ a, LookupCountBytes c a → ¬LookupOwnerBytes c a
  outputProtected : ∀ a, LookupOutputWrites v s a →
    ¬(LookupRelation.Reads c v a ∨ LookupServiceBytes coverage preempt v a ∨
      InRange (s.data.regs.rsp.toBitVec-48) 56 a ∨ LookupCoverageWrites coverage preempt v a)
  pendingFrame : LookupPendingRead preempt → ∀ a, InRange softirqPendingAddress 2 a →
    ¬(LookupStackWrites c s a ∨ LookupCoverageWrites coverage preempt v a ∨
      LookupDataWrites c v a ∨ LookupOutputWrites v s a)

/-- Entry domain relative to the supplied source World and fixed ABI/address
    interpretation. Its machine-side domain existentially closes world and
    these interpretation parameters. No execution or R-preservation premise
    occurs here; LookupWitness supplies a concrete inhabitant and its test
    executes that exact state to the recorded return. -/
def Pre_lookup (c : LookupRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState) (world : Leanux.World) : Prop :=
  ∃ v, LookupEntry c coverage preempt returnAddress s world v


/-- M2 calls PC and comparison instrumentation in both BH phases. Buffer
    metadata is required only when the physical callback reads it. -/
def AllowedipsCoverageNeeded (coverage : KcovLayout) (preempt : BitVec 32) : Prop :=
  LookupModeRead coverage preempt ∧ (coverage.mode = 2 ∨ coverage.mode = 3)

def AllowedipsCoverageAt (coverage : KcovLayout) (preempt : BitVec 32) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some coverage.task ∧
  (LookupSoftRead preempt → load32 memory (coverage.task+0x704) = some coverage.softirqEnabled) ∧
  (LookupModeRead coverage preempt → load32 memory (coverage.task+0x6e0) = some coverage.mode) ∧
  (AllowedipsCoverageNeeded coverage preempt →
    load32 memory (coverage.task+0x6e4) = some coverage.capacity ∧
    load64 memory (coverage.task+0x6e8) = some coverage.area ∧ KcovBuffer coverage memory)

def AllowedipsCoverageWrites (coverage : KcovLayout) (preempt : BitVec 32)
    (a : BitVec 64) : Prop :=
  (AllowedipsCoverageNeeded coverage preempt ∨ AllowedipsCoverageNeeded coverage (preempt+512)) ∧
    KcovBufferBytes coverage a

def AllowedipsMetadata (coverage : KcovLayout) (preempt : BitVec 32) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨
  ((LookupSoftRead preempt ∨ LookupSoftRead (preempt+512)) ∧ InRange (coverage.task+0x704) 4 a) ∨
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (preempt+512)) ∧ InRange (coverage.task+0x6e0) 4 a) ∨
  ((AllowedipsCoverageNeeded coverage preempt ∨ AllowedipsCoverageNeeded coverage (preempt+512)) ∧
    (InRange (coverage.task+0x6e4) 4 a ∨ InRange (coverage.task+0x6e8) 8 a)) ∨
  (LookupPendingRead preempt ∧ InRange softirqPendingAddress 2 a)

def AllowedipsServiceBytes (coverage : KcovLayout) (preempt : BitVec 32) (a : BitVec 64) : Prop :=
  AllowedipsMetadata coverage preempt a ∨
  ((AllowedipsCoverageNeeded coverage preempt ∨ AllowedipsCoverageNeeded coverage (preempt+512)) ∧
    KcovStorageBytes coverage a)

/-- Outer saves/local words, the shared call slot, and the deepest peer-get
    saves/call: every word of this interval is used on a covered path. -/
def AllowedipsStackWrites (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec-144) 144

def AllowedipsLiveStack (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec-144) 152

def AllowedipsCountWrites (c : AllowedipsRelation.Config) (v : AllowedipsRelation.View)
    (a : BitVec 64) : Prop :=
  ∃ pid count, c.focus.peer = some pid ∧ v.count = some count ∧ count ≠ 0 ∧
    InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a

/-- Physical entry domain for both IP families. Focus is a total pure source
    selection, not an assumption that the binary or mirror terminates; a
    refused source search gives no selected node. No peer positivity premise.
    Both address families have executed concrete witnesses in AllowedipsWitnessPre. -/
structure AllowedipsEntry (c : AllowedipsRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState)
    (world : Leanux.World) (v : AllowedipsRelation.View) : Prop where
  pc : s.pc = AllowedipsImage.Lookup.entry
  entry : EntryFrame s returnAddress
  root : s.data.regs.rdi.toBitVec = AllowedipsRelation.pointer c.nodes c.root
  bits : s.data.regs.get (.low .rsi .W8) = .ofNat 8 c.bits
  projection : AllowedipsRelation.project c world = some v
  related : AllowedipsRelation.R c [s] [LookupObservation.call "lookup" s] s world
  focusNode : c.focus.node = (AllowedipsSource.select v.nodes c.root c.bits c.key).join
  focusPeer : c.focus.peer = c.focus.node.bind (fun id => (v.nodes id).bind (·.peer))
  input : Allowedips.NetworkKey s.data.dmem s.data.regs.rdx.toBitVec c.bits c.key
  stack : ∀ i < 18,
    (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec-.ofNat 64 ((i+1)*8)) 8).isSome = true
  preemptField : load32 s.data.dmem preemptCountAddress = some preempt
  coverageBefore : AllowedipsCoverageAt coverage preempt s.data.dmem
  coverageDuring : AllowedipsCoverageAt coverage (preempt+512) s.data.dmem
  hardirq : (preempt+512) &&& 0x000f0000 = 0
  pending : LookupPendingRead preempt → s.data.dmem.loadInt softirqPendingAddress 2 = some 0
  stackData : ∀ a, AllowedipsRelation.Reads c v a → ¬AllowedipsStackWrites s a
  stackInput : ∀ a, Allowedips.NetworkReads s.data.regs.rdx.toBitVec c.bits a → ¬AllowedipsStackWrites s a
  stackServices : ∀ a, (AllowedipsServiceBytes coverage preempt a ∨ InRange preemptCountAddress 4 a) →
    ¬AllowedipsStackWrites s a
  bufferData : ∀ a, AllowedipsRelation.Reads c v a → ¬AllowedipsCoverageWrites coverage preempt a
  bufferInput : ∀ a, Allowedips.NetworkReads s.data.regs.rdx.toBitVec c.bits a →
    ¬(AllowedipsCoverageNeeded coverage preempt ∧ KcovBufferBytes coverage a)
  bufferStack : ∀ a, AllowedipsCoverageWrites coverage preempt a → ¬AllowedipsLiveStack s a
  bufferMetadata : ∀ a, AllowedipsCoverageWrites coverage preempt a →
    ¬AllowedipsMetadata coverage preempt a
  bufferPreempt : ∀ a, AllowedipsCoverageWrites coverage preempt a → ¬InRange preemptCountAddress 4 a
  countStack : ∀ a, AllowedipsCountWrites c v a → ¬AllowedipsLiveStack s a
  countTrie : ∀ a, AllowedipsCountWrites c v a →
    ¬AllowedipsRelation.TrieReads c.nodes v.nodes c.root c.bits c.key a
  countServices : ∀ a, AllowedipsCountWrites c v a →
    ¬(AllowedipsServiceBytes coverage preempt a ∨ InRange preemptCountAddress 4 a)
  preemptData : ∀ a, AllowedipsRelation.Reads c v a → ¬InRange preemptCountAddress 4 a
  preemptStack : ∀ a, AllowedipsLiveStack s a → ¬InRange preemptCountAddress 4 a
  preemptServices : ∀ a, AllowedipsServiceBytes coverage preempt a → ¬InRange preemptCountAddress 4 a

/-- The function's named machine-entry domain, witnessed before it lands. -/
def Pre_allowedips (c : AllowedipsRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState) (world : Leanux.World) : Prop :=
  ∃ v, AllowedipsEntry c coverage preempt returnAddress s world v

/-- Literal instruction agreement for the anchored insertion image. Callback
behavior and agreement with supplied random draws are separate obligations. -/
def IndexInsertDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, IndexInsertImage.Insert.fetch pc=some instruction → fetch pc=some instruction

/-- Read locations of instrumentation in the random call's unchanged BH
phase. Pending-work words and the insertion heap do not belong here. -/
def RandomMetadata (coverage : KcovLayout) (preempt : BitVec 32) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨ InRange preemptCountAddress 4 a ∨
  (LookupSoftRead preempt ∧ InRange (coverage.task+0x704) 4 a) ∨
  (LookupModeRead coverage preempt ∧ InRange (coverage.task+0x6e0) 4 a) ∨
  (AllowedipsCoverageNeeded coverage preempt ∧
    (InRange (coverage.task+0x6e4) 4 a ∨ InRange (coverage.task+0x6e8) 8 a))

def RandomBuffer (coverage : KcovLayout) (preempt : BitVec 32) (a : BitVec 64) : Prop :=
  AllowedipsCoverageNeeded coverage preempt ∧ KcovStorageBytes coverage a

def RandomRecordingActive (coverage : KcovLayout) (preempt : BitVec 32) : Bool :=
  @decide (AllowedipsCoverageNeeded coverage preempt) (by
    unfold AllowedipsCoverageNeeded LookupModeRead
    infer_instance)

/-- A bounded physical stack reservation, not an instruction/draw budget.
The live range also protects the service return word. -/
def RandomStack (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec-1024) 1024
def RandomLiveStack (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec-1024) 1032

/-- Current initialized provider state, recording graph and physical call
resources. This contains no World, source result or future execution premise.
The entry theorem must additionally separate these private writes from its
own represented objects and saved caller frame. -/
structure RandomReady (privateState : RandomProvider.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (s : MachineState) : Prop where
  coverageState : AllowedipsCoverageAt coverage preempt s.data.dmem
  preemptState : load32 s.data.dmem preemptCountAddress=some preempt
  capacity : AllowedipsCoverageNeeded coverage preempt → 0<coverage.capacity.toNat
  privateCheck : RandomProvider.check privateState coverage.task.toNat
    (RandomRecordingActive coverage preempt) s.data.dmem=.ok ()
  kernelMode : s.data.system.cpl=0
  forward : s.data.system.bits[10]=false
  stackMapped : ∀ i<1024, (s.data.dmem.get? (s.data.regs.rsp.toBitVec-1024+.ofNat 64 i)).isSome=true
  privateApart : ∀ a, RandomProvider.PrivateBytes privateState a →
    ¬(RandomLiveStack s a ∨ RandomMetadata coverage preempt a ∨ RandomBuffer coverage preempt a)
  stackApart : ∀ a, RandomLiveStack s a →
    ¬(RandomMetadata coverage preempt a ∨ RandomBuffer coverage preempt a)
  bufferApart : ∀ a, RandomBuffer coverage preempt a → ¬RandomMetadata coverage preempt a

def RandomWrites (privateState : RandomProvider.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (s : MachineState) (a : BitVec 64) : Prop :=
  RandomProvider.PrivateBytes privateState a ∨ RandomStack s a ∨
    (AllowedipsCoverageNeeded coverage preempt ∧ KcovBufferBytes coverage a)

/-- Unproved physical get_random_u32 service specification for the initialized
provider, including its recording hook. It executes the same fetched ISA as
the caller and preserves physical private readiness, coverage and BH state.
It promises no particular random value. Agreement with a recorded input tape
is a separate safety hypothesis; this declaration cannot produce arbitrary
requested draws from one fixed machine state. -/
def RandomReturnContract (fetch : Int64 → Option Decoded) (privateState : RandomProvider.Config) : Prop :=
  ∀ coverage preempt s returnAddress, s.pc=.ofNat 0xffffffff81375000 →
    RandomReady privateState coverage preempt s → EntryFrame s returnAddress →
    Eventually (historyStep fetch) (fun t =>
      Returned s t.machine returnAddress ∧
      EqualOutside (RandomWrites privateState coverage preempt s) s.data.dmem t.machine.data.dmem ∧
      AllowedipsCoverageAt coverage preempt t.machine.data.dmem ∧
      load32 t.machine.data.dmem preemptCountAddress=some preempt ∧
      RandomProvider.check privateState coverage.task.toNat
        (RandomRecordingActive coverage preempt) t.machine.data.dmem=.ok () ∧
      t.machine.data.system.bits[9]=s.data.system.bits[9] ∧
      (∀ point ∈ t.history.dropLast, IndexInsertImage.Insert.fetch point.pc=none))
      ⟨s,[s]⟩

/-- Safety coupling with an external recorded-input interpretation. The
interpretation depends only on provider-private bytes, never the WireGuard
heap. Recording context and return site are fixed parameters: changing either
can change a steered result without changing private bytes. The current
readiness and entry frame are premises of the return law, not conclusions.
Its return law constrains existing actual service histories; it does
not assert termination, physical readiness, a source insertion result or R.
In particular `inputAt` is required before a draw can be prescribed. -/
structure RandomInputCoupling (fetch : Int64 → Option Decoded) (privateState : RandomProvider.Config)
    (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (inputAt : DataMem → List Leanux.HiddenRecord → Prop) : Prop where
  frame : ∀ before after records,
    (∀ a, RandomProvider.PrivateBytes privateState a → before.get? a=after.get? a) →
    inputAt before records → inputAt after records
  returned : ∀ s t history records value rest,
    s.pc=.ofNat 0xffffffff81375000 → RandomReady privateState coverage preempt s →
    EntryFrame s returnAddress → inputAt s.data.dmem records →
    Pair.Insert.draw records=.ok (value,rest) →
    ActualHistory fetch s history → history.getLast?=some t →
    Returned s t returnAddress →
    (∀ point ∈ history.dropLast, IndexInsertImage.Insert.fetch point.pc=none) →
    (t.data.regs.get (.low .rax .W32)).toNat=value ∧ inputAt t.data.dmem rest

end Binary.TrustBase
```
