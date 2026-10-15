# Companion proposal for the state split

[AGENT proposal 2026-10-15]. Split the global world into subsystem state, retain one shared task store for the file layer, seccomp and signals, and narrow leaves over existing owned records where that is cheap. The runner holds the product. This gives WireGuard isolation immediately without inventing independent copies of a task or a peer.

This accompanies the design at `task/state-split:docs/2026-10-15-design-state-split.md`, reviewed at `1cca44e7`, and addresses all six findings in the [independent review](2026-10-15-review-state-split.md). Its source baseline is `cb2348e`, the review branch's parent mirror revision. These are proposed replacements for parts of that design, not adopted standing rules or authorization to implement or merge them. The original note and its recorded decisions remain unchanged.

**The amendment to the original contract**

The recorded aim—localized worlds, narrower types where cheap, and deletion of structural frame boilerplate—remains. The literal “runner ... is the only composer” formulation needs one explicit qualification: subsystem operations may call shared task/signal services at the C's existing call sites. The runner alone assembles the full product and orchestrates operations involving independent subsystem stores. A pipe's signal call stays inside `pipeWrite`; a seccomp trap stays inside `seccompFilter`.

The other deliberate change is to keep `Task` intact for the first split. File and seccomp operations share this small state because their paths already depend on task lifecycle and signal state. We accept that their access to other fields of the shared task is not yet excluded by types. We do not accept unrestricted access to each other's object stores or to WireGuard. This limited remainder is preferable to three task maps whose existence and destruction would need synchronization machinery.

The mirror landing reports proof lag and is followed by repair of the actual landed campaign tree, as the project's standing rules allow. It does not promise a passing proof gate over the old 1,399-theorem baseline while deferring the campaign that has already replaced it. These two design amendments need acceptance before implementation; preparing this companion note does not enact them.

**State ownership and execution types**

Retain the existing `Task` record and its fields. Move the three enclosing fields out of `Kernel` together:

```lean
structure TaskWorld where
  task : Task
  child : Option Task := none
  current : TaskRef := .task
```

There is one mandatory parent and one optional child. `getTask`/`modifyTask` retain their current missing-child failure. `getCurrent` resolves `current`; `getFiles` still selects `.task`, exactly as it does today. Child creation copies the existing task and resets the existing fields in the existing order; dropping the child removes one record. There is no separate existence Boolean. The modeled signal disposition `sigsys` belongs conceptually to the signal part of this task, alongside `blocked`, `pending` and `sigpending`; it does not migrate to a seccomp-owned table.

`FSWorld` owns the 31 remaining file-layer fields of the baseline `Kernel`: file/eventfd stores and counters, pipe/inode/page stores and accounting, and epoll stores and bookkeeping. `SeccompWorld` owns `seccompFilters` and `nextFilter`. `WGWorld` owns the seven existing WG-related kernel fields, retaining the distinction between `Option WG.Device` and counters or namespace state that outlive that device. Together with the three task fields, this accounts for all 43 baseline `Kernel` fields. This is a partition of the existing representation; it does not change C ownership or invent new kernel objects.

Use the following monads, with one stored instance of each state:

```lean
abbrev AmbientM := StateT Ambient (Except Stop)
abbrev TaskM := StateT TaskWorld AmbientM
abbrev WG.M := StateT WGWorld AmbientM
abbrev FS.M := StateT FSWorld TaskM
abbrev Seccomp.M := StateT SeccompWorld TaskM

structure World where
  ambient : Ambient
  tasks : TaskWorld
  wg : WGWorld
  fs : FSWorld
  seccomp : SeccompWorld
  fixture : EnvWorld

abbrev M := StateT World (Except Stop)

def liftFS (x : FS.M α) : M α := fun w => do
  let (((a, fs), tasks), ambient) ←
    ((x.run w.fs).run w.tasks).run w.ambient
  return (a, { w with fs, tasks, ambient })
```

`liftSeccomp` has the same shape, replacing only `seccomp`, `tasks` and `ambient`. `liftTask` replaces only `tasks` and `ambient`; `liftWG` is the original note's two-layer lift. Each invocation starts from the latest product state and writes back its returned state once. Do not retain an earlier task snapshot across separate lifted operations. Keep `Except Stop` underneath all state layers: failure returns the same error without publishing a successful partial state.

Signal generation and task accessors use `TaskM`. Lean's existing `StateT` lifting lets both `FS.M` and `Seccomp.M` call them directly. File-store-only helpers can use `StateT FSWorld AmbientM`, and filter-store-only helpers can use `StateT SeccompWorld AmbientM` where cheap; lift their ambient base through `TaskM` explicitly at the caller:

```lean
def liftFSLocal (x : StateT FSWorld AmbientM α) : FS.M α := fun fs =>
  liftM (x.run fs)
```

This is a small fixed adapter. Bare `get`/`modify` refer to the local outer state; shared state access uses named task helpers or an explicit type annotation.

The resulting guarantees are precise:

| Computation | Mutable state supplied by its execution type | Structurally excluded |
| --- | --- | --- |
| `WG.M` | WG and ambient | Tasks, FS, seccomp, fixture queues |
| `TaskM` | Tasks and ambient | WG, FS object stores, filter store, fixture queues |
| `FS.M` | FS, tasks and ambient | WG, filter store, fixture queues |
| `Seccomp.M` | Seccomp, tasks and ambient | WG, FS object stores, fixture queues |
| `M` | The product | None; orchestration needs the product |

These guarantees concern state updates, not success: ambient records can still make a file operation fail. Nor does `FS.M` prove preservation of the task's seccomp fields. Keep any needed statements about those shared fields until their actual callee types exclude the fields. WireGuard acquires no task capability through its ambient monad.

**Placement of the remaining state**

At `cb2348e`, the 47 `World` fields other than `k` move as follows. This inventory is a review aid for the cutover, not a new checking system. Reconcile it once against the actual post-B3 baseline before coding.

| Destination | Existing fields |
| --- | --- |
| `Ambient` | `env`, `timing`, `envCalls`, `steps`, `extraOut`, `hidden`, `hiddenPlaceholders`, `placeholderCount`, `suspended`, `unitPeers`, `pendingWork`, `netRxSections`, `netRxSection`, `steerValues`, `armRecords`, `fired`, `allocArmed`, `allocSteered` |
| `WGWorld` | `lastUnderLoad`; routing: `addrs4`, `addrs6`, `defaultRoute4`, `defaultRoute6`, `defaultRoute4Accessed`, `ipv4Gen`, `ipv6Gen`; network runtime: `sent`, `netRxRaised`, `queuedThisCall`, `timerUnits`, `jiffiesLast`, `dstCacheRecords`; fixture inputs used by WG: `portBound`, `fixtureNetDevices` |
| `FSWorld` | `userOut`, `userFds` |
| `SeccompWorld` | `translatedLen`, `emitted` |
| `EnvWorld` | `listenerV4`, `listenerV6`, `senderInbox`, `foreignCreator`, `netnsCHolders`, `napiBeforePut`, `napiAmbiguous`, `routesPending`, `routes` |

`armRecords` stays with the record protocol: both queue recording and timer recording consult it. Keep `recordQueued` and `peekQueuedUnit` over `AmbientM`; do not make them reach into WG timer state. Move `retirePeerUnits` and `retireDeviceUnits` to `WG.M`, because each retires both ambient unit identities and WG timer identities. Their operations and order stay unchanged.

`branch`, `branchCmp`, `hidden`, `skipAmbient`, `envOk` and the other genuinely ambient services use `AmbientM`. The seccomp bridge retains its local deduplication state and updates the ambient decision log at the existing point. Section-stamp updates and runner resets remain explicit operations too; the kernel helper file was never the exclusive writer. `extraOut` remains a shared observation accumulator because WG dumps and seccomp probes both use it.

`EnvWorld` contains mutable fixture queues and fixture control state, accessible to product-level environment code. It is not labeled read-only. WG socket sends append to `WGWorld.sent`; the existing delivery code later moves those datagrams to fixture queues at the same scheduling points. The function-valued fixture inputs WG actually reads remain in its world for this migration; separating immutable configuration into a reader is unnecessary here.

Keep routing as a concrete `Net.Routing` subrecord inside `WGWorld`, with functions independent of `WG.Device`. `routeLookup` is a stateful routing operation because it marks the accessed default route. A peer's `dstCache` remains in that peer and consumes the routing generations explicitly. `routes` in the table above is the fixture's extra MTU-route configuration, distinct from the modeled routing tables. Lane C replaces the routing component when its implementation lands; the split itself does not change the routing algorithm.

Preserve every lifetime. Removing `device` does not reset `netIfindexNext`, global peer/keypair counters, the rate limiter or `lastUnderLoad` indiscriminately. Each keeps its current C-corresponding update and teardown rules. B3's timer representation must be moved as landed, without redesigning its scheduler in this task.

**Where product-level orchestration lives**

Keep `Runner`, syscall dispatch and the environment scheduler over `M`. Distinguish a file's location from an operation's required state: the child-probe and trap-return orchestration currently in `Seccomp/Syscalls.lean` remains over `M` even though filter execution beneath it becomes `Seccomp.M`. If import order requires moving those definitions, put the operation orchestration with syscall dispatch; do not move the C filter or signal decisions into it.

The child probe retains this sequence: parent's harness calls and fork clocks; filter-reference increment; child creation; select child; strict/probe/exit handling; child-exit environment effect; select parent; parent `wait4`; child drop; observation. Each filter operation is lifted where it already occurs. Child creation/drop uses the one task store; child exit can use the task and filter stores through the product. Trap delivery still clears the pending state after the filter's signal-generation path, before the same subsequent return handling.

For WG workers, lift a complete monomorphic worker body where possible. The scheduler keeps product state for delivery, suspended activations and fixture effects; it invokes `liftWG` at the existing boundaries. Do not move callbacks or record consumers across a lift merely to reduce the number of adapters. Helpers with a computation argument need that argument's type reviewed explicitly—changing the return type alone does not migrate a scheduler callback.

**Narrowing inside WireGuard without splitting owners apart**

Drop the requirement to manufacture eight parallel stores and convert exactly 59 functions. Preserve `Device`, `Peer`, `Keypair` and their identity-keyed stores. Narrow existing value computations first, then a small number of stateful operations whose inputs and updates already form one owned component.

| Candidate | Proposed treatment in this stream |
| --- | --- |
| Ring operations | Retain the existing explicit `PtrRing` arguments/results. Add no monadic wrapper merely to obtain a group name. |
| Routing lookup | Use `StateT Net.Routing AmbientM` when it needs logging or a state update; lift into WG by replacing only `routing`. |
| Index bucket/filtering | Pass the actual `List IndexEntry` to the pure calculation. Preserve the existing missing-device check at the caller's first device access. |
| Index insert/remove/replace | Try a stateful index-table leaf where the entire transitive body needs only that table and ambient records. Keep the single table in its existing device owner; use one explicit extraction/writeback adapter. |
| Allowed-IPs node-only leaves | Candidate for a trie component preserving node identity and dangling-node failures. Operations maintaining peer-owned lists retain `WG.M` unless a concrete combined input is demonstrably cheap. |
| `indexLookup` | Retain `WG.M`: it obtains a strong peer reference and updates the owner's embedded peer word. A keys-only signature is false. |
| `armTimer` and `delTimer` | Retain `WG.M` initially: the former consumes records before reaching the peer update, and both update peer-owned fields. Keep pure timer-field calculations explicit. |
| Entry points, release paths, mixed cookie/peer operations | Retain `WG.M` unless a specific smaller type follows directly from their actual calls. |

For example, a total routing lift has this shape:

```lean
def liftRouting (x : StateT Net.Routing AmbientM α) : WG.M α := fun w => do
  let (a, routing) ← x.run w.routing
  return (a, { w with routing })
```

For a component behind `Option Device` or a peer lookup, the access may fail. Extraction must occur at the original access point, and writeback must replace only the selected fields of that same owner. A narrowed leaf cannot accept a callback that secretly mutates the rest of WG. Do not extract every potential input eagerly: `armTimer` currently consumes and validates arm records before `getPeer`; moving the lookup to entry changes which error is returned on malformed state/records. Likewise, an allowed-IPs operation may reject arguments before touching a device.

No owner word is copied into two stores, and no timer-only peer map is introduced. If a proposed group needs several maps with equal domains, duplicated lifetime markers, or new footprint invariants, keep the operation over `WG.M` and report that narrowing as deferred. This is the user's cheap-narrowing qualification applied concretely. In particular, narrower types are not permission to restructure the mirror to make a campaign proof close.

The existing probe remains a candidate finder. If used, fix shorthand-update recognition and default-parameter classification, distinguish reads from touched fields, and report unresolved calls. Do not use a lexical call graph to certify absence of dependencies. For each selected leaf, follow its small transitive call set manually and compile the proposed signature. The resulting finite list replaces the 59-leaf promise; it is not a new acceptance gate or static-analysis project.

**Proof retrofit and the claims that remain**

Define local execution contracts over the actual state tuple. A WG action runs as `WGWorld → Ambient → Except Stop ((α × WGWorld) × Ambient)`; an FS action additionally takes `TaskWorld` and returns its updated value. Quantify over ambient inputs even when the predicate observes only a WG snapshot. Preserve the distinction between successful-return properties, existence of a successful return, and properties covering exact errors.

Delete each per-function structural frame when its replacement follows from the new execution type and the generic lift fact. For example, lifted FS computations preserve `wg`, so their individual WG-snapshot frames disappear. The lift fact says exactly what can change: FS, tasks and ambient. It does not claim that the task's seccomp fields remain unchanged. Within-WG facts and shared-task facts that are not structural remain, repaired by retyping where necessary.

Keep the observer for a local action local, with its ambient input. Keep the logged syscall/environment/runner observers over the product. Their erasure still preserves complete observations and exact failures, including record exhaustion and indexed runner errors. Generalize the existing small combinators and prove the necessary lift/observer bridge once in the proof tree; do not retain a copy of the old executable world or create old/new executable equivalence lemmas.

Deletion is justified by the guarantee supplied by the new type, not by a theorem ceasing to compile. Retype terminal results and preserve their premises and observable content. If a terminal claim cannot be retained, report it as lag or a finding rather than deleting it to turn the gate green. The binary track uses the new WG state directly for its state relation, with execution inputs represented explicitly in its execution interface; do not infer the adequacy theorem solely from this packaging change.

**Implementation order and realistic completion claims**

1. Pin the actual baseline after B3 and campaign 1 have landed, honoring their existing order. Reconcile fields and campaign revisions once. The type-mechanics spike can precede this, but production conversion starts from that baseline. Campaign 2 stays at its checkpoint; lane C consumes the routing interface before its C1 landing as previously agreed.
2. Prepare the complete coarse cutover in one task worktree: worlds, accessors, ambient/task services, all subsystem signatures, initialization, product orchestration and output projections. Definitions of unused new types may be committed first if useful. Replacing `World` cannot be a compiling types-only commit. Do the connected migration before committing that replacement; no temporary old-world compatibility layer is needed.
3. Build and run the fast tier, then the affected suites. Fix representation mistakes within the authorized scope; report any apparent semantic defect separately. Measure model build/elaboration separately from runtime after the actual lifts exist. The shared-task prototype below confirms only type mechanics.
4. At the mirror claim point, run the existing full differential check, controls and sentinels against the approved oracle. Present the concrete mirror diff and actual proof lag for signoff. A proof repair is not an additional mirror gate. Keep main unchanged until the user signs off.
5. Retype the landed campaign-1 tree as one follow-on proof job against the split. Do not count the old main tree as a separate smaller job. Resume campaign 2 on that interface and avoid duplicating repairs to shared proof files. A proof-tree integration gets its own proof gate and signoff, with result pins/current-or-lagging status updated honestly.
6. Land successful cheap WG narrowing as separately reviewable changes on the split tree, with scoped validation and explicit proof lag. This work may be developed alongside the coarse migration, but it must not hold the coarse boundary hostage to an unvalidated eight-group representation. Coordinate any signature changes with the resumed proof work.

For a provisional staffing allowance, reserve 0.5–1 working day for reconciliation and representative conversions, 4–7 for the connected coarse cutover, and 1–2 for validation and correction: **5.5–10 days of implementation effort for the coarse mirror split**. Reserve a further 1–3 days for selected cheap narrowing. These are [AGENT] planning judgments, not measured durations or a promised calendar deadline; compiler behavior and the actual post-B3 baseline may change them. Re-estimate after the first complete build and replay measurements.

Budget proof work separately against the then-pinned campaign trees. As an initial allowance, campaign 1 is 5–10 days and campaign 2's additional work 2–5, with shared repairs counted once. The review's snapshots contain 7,076 and 2,870 theorems respectively; lexical frame counts are not deletion forecasts. If the desired product is a mirror landing with every proof current, add the landed-tree retrofit to that critical path explicitly. The recommended sequence above instead follows the standing policy of a mirror landing with reported lag and subsequent proof integration.

Validation preserves the existing trust surface. Use the repository's build, five-module unit-test command, affected suites, full check, controls, sentinels, kernel identity check and separate proof gate at their established claim points, all through `capped`. For behavior preservation, replay the same recorded inputs on the pinned baseline and candidate, including exact outputs/errors; temporary captures are deleted afterward. Do not demand identical record totals from two independently scheduled live kernel runs as if they were the same execution. Investigate differences in coverage, verdicts or records rather than normalizing them away or retrying a scheduling-dependent failure.

Stop and report if a selected local action actually needs an excluded store, if narrowing changes failure/record order, if a real C path requires new semantics, or if a representative converted path shows a material unexplained build/runtime regression. A leaf that proves too expensive to narrow stays at its honest wider type. Missing type annotations and ordinary signature repair are implementation work, not reasons to invent a broader global world.

**What has been checked for this companion**

An isolated Lean 4.35 check compiled the shared `TaskM` stack, the store-only helper adapter, and both product lifts. It exercised an FS action followed by a seccomp action, verified that the second sees the first's task update, preserved WG and unrelated task fields, checked ambient event order, and propagated a missing-child failure. A one-off inventory check found all 47 non-`k` World fields assigned exactly once in the table above. These checks validate type mechanics and inventory completeness, not the production migration, all call dependencies, or its cost. No executable mirror or proof tree was edited, and the existing proof lag remains.

The following self-contained fragment reproduces the type-mechanics check. Its scalar fields stand in for the existing records; it is not a replacement mirror. Save it to `.tmp/SharedTaskSpike.lean` in a task worktree and run `capped -- scripts/in-bundle lean .tmp/SharedTaskSpike.lean`, then remove that temporary file.

```lean
import Std

namespace SharedTaskSpike
structure Ambient where
  log : List Nat := []
structure Task where
  pending : Nat := 0
  files : Nat := 9
  filterMode : Nat := 0
structure TaskWorld where
  task : Task := {}
  child : Option Task := none
  current : Bool := false
structure FSWorld where
  writes : Nat := 0
structure SeccompWorld where
  calls : Nat := 0
structure World where
  ambient : Ambient := {}
  tasks : TaskWorld := {}
  fs : FSWorld := {}
  seccomp : SeccompWorld := {}
  wg : Nat := 77
abbrev AmbientM := StateT Ambient (Except String)
abbrev TaskM := StateT TaskWorld AmbientM
abbrev FSM := StateT FSWorld TaskM
abbrev SeccompM := StateT SeccompWorld TaskM
abbrev M := StateT World (Except String)
def liftFSLocal (x : StateT FSWorld AmbientM α) : FSM α := fun fs =>
  liftM (x.run fs)
def record (n : Nat) : AmbientM Unit :=
  modify fun s => { s with log := s.log ++ [n] }
def signal : TaskM Unit := do
  record 2
  modify fun s => { s with task := { s.task with pending := s.task.pending + 1 } }
def pipe : FSM Unit := do
  record 1
  liftFSLocal (modify fun s => { s with writes := s.writes + 1 })
  signal
  record 3
def filter : SeccompM Nat := do
  let t ← (get : TaskM TaskWorld)
  record 4
  modify fun s => { s with calls := s.calls + 1 }
  signal
  return t.task.pending
def liftFS (x : FSM α) : M α := fun w => do
  let (((a, fs), tasks), ambient) ← ((x.run w.fs).run w.tasks).run w.ambient
  return (a, { w with fs, tasks, ambient })
def liftSeccomp (x : SeccompM α) : M α := fun w => do
  let (((a, seccomp), tasks), ambient) ← ((x.run w.seccomp).run w.tasks).run w.ambient
  return (a, { w with seccomp, tasks, ambient })
def combined : M Nat := do
  liftFS pipe
  liftSeccomp filter
#guard match combined.run {} with
  | .error _ => false
  | .ok (before,w) => before == 1 && w.tasks.task.pending == 2 &&
      w.tasks.task.files == 9 && w.tasks.task.filterMode == 0 &&
      w.fs.writes == 1 && w.seccomp.calls == 1 && w.wg == 77 &&
      w.ambient.log == [1,2,3,4,2]
def child : TaskM Task := do
  match (← get).child with
  | some t => return t
  | none => throw "missing child"
def fails : FSM Unit := do
  signal
  let _ ← child
  record 99
#guard match (liftFS fails).run {} with
  | .error e => e == "missing child"
  | .ok _ => false
end SharedTaskSpike
```
