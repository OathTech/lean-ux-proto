# Independent review of the state split design

Review and recommendations: [AGENT 2026-10-15]. The localized-world direction is useful, and the proposed nested `StateT` and runner lift work in Lean 4.35. The design nevertheless needs revision before implementation: its stopping condition is already met by existing signal calls, its measurements do not establish the claimed footprints, and its schedule counts the wrong proof tree at the landing.

Reviewed note and probe: `task/state-split` at `1cca44e7c03b4681c01d782dc16b3e430f0d36b6`, including the last four decisions. Executable code and project rules: `main` at `cb2348e2175326f67392cae27d2132f9676897e7`; the probe was also rerun on the note's `de62c9d`. Campaign snapshots: `proofs/campaign` at `8f9b8a25cb18a9013a739107796cd41225ff6243` and `proofs/campaign-2` at `b579df9cdb5f0f4980e1e5cdb039a08932569cce`. Branch content was read through Git; no existing task worktree was entered. References below use those revisions. C references are to the main checkout's pristine `.deps/linux` source.

**1. High — The task and signal boundary already requires composition inside mirror functions.**

Sections 2, 3 and 8 place lifecycle state in a sibling world, put `sigsys` and `current` in seccomp, type `pipeWrite` over `FS.M`, and say there are no cross-component calls. These choices cannot all hold:

- `Leanux/FS/Pipe.lean:427,459` calls `sendSig .task SIGPIPE 0`. The signal chain reads and writes lifecycle state. `FS/FileTable.lean:152,155` also reads `Task.isKthread` and `Task.exited` while doing `fput`.
- `Leanux/Seccomp/Filter.lean:319,350` calls `forceSigSeccomp`. `Kernel/Signal.lean:317` onwards reads `blocked`, changes both `sigsys` and `blocked`, and reaches writes to `pending` and `sigpending`. `wantsSignal` also reads `Kernel.current`. Thus even the proposed lifecycle module itself needs fields allocated to seccomp.
- This follows the C: `kernel/signal.c:1328–1363` accesses both `t->sighand->action[sig-1]` and `t->blocked`, then generates the signal. A signal disposition belongs with signal state; classifying it as seccomp-owned because this slice exercises SIGSYS confuses the caller with ownership.

The environment exception does not resolve these mirror-to-mirror calls. There is also an orchestration boundary inside today's seccomp directory: `Seccomp/Syscalls.lean:149–201` calls `Env.childCreate`, `childExit` and `childDrop`; `trapReturn` uses delivery effects. Those operations cannot all move to `Seccomp.M` while their callees remain over the product. The orchestration must be identified and kept at product level explicitly.

Choose a concrete shared task/signal interface before starting. One feasible direction is a shared task state, with signal disposition and current-task identity in it, available to the file and seccomp computations through a common underlying monad; the runner owns its single instance. Another is a broader task/file/seccomp world with narrower leaf functions. Either changes the proposed sibling-monad contract and must be reconciled with the recorded runner-only composition decision. Moving signal generation to syscall entry or exit would change its position among pipe decisions and is not a representation-only solution.

Preserve today's addressing rule: `Kernel/Defs.lean:1758–1762` uses `.task` for file access, not `Kernel.current`. `Env.childCreate:965–974` explicitly says no modeled child path touches files. If the three task tables are retained, define joint creation/removal and fail-noisy lookup for missing rows; the old mandatory parent and single `Option Task` encoded existence together. An independent child Boolean and three maps do not encode that consistency.

Under section 8.1's own rule, the implementation should stop **now**, at these known dependencies, rather than after a day of changing types.

**2. High — The access probe reproduces its numbers but does not justify the dependency and narrowing claims.**

At `de62c9d` the probe reproduces the displayed matrix totals and this histogram exactly:

```text
monadic definitions: 238
groups -> definitions: 0:46, 1:16, 2:43, 3:41, 4:24, 5:6, 6:23, 7:21, 8:18
```

The raw output additionally reports an FS/Peer read and write, omitted from the note's table; that is consistent with its acknowledged field-name collisions. At `cb2348e`, `World` has 48 fields following removal of `floodExact`; Env's World total becomes 29/21 and its Device total 22/3. The function histogram is unchanged. These are reproducible textual statistics, not sound read/write footprints:

- `with_fields` recognizes `name :=`, but misses shorthand updates. For example, `WG/Device.lean:256,423` updates the measured fields `ifindex` and `mtu` using `{ d with ifindex }` and `{ d with mtu, ... }`; the parser misses those writes. Calling it on `{ w with netRxSection }` returns `[]`. Whole-record construction and replacement also occur; `setPeer` accepts an arbitrary `Peer`, including its timer fields.
- The summary printed as `reads` actually counts the union of reads and writes (`state-split-access.py:274–277`). It is not a read count.
- Function classification splits at the first `:=` (`:181–183`). `armTimer` has `(jc? : Option UInt64 := none)` before its return type, so the probe classifies this monadic timer operation as non-monadic and discards its directly observed timer accesses.
- Calls are every matching identifier, without namespace resolution (`:179,186–194`). `setPeer` acquires an `allowedips` dependency through the token `insert` in `d.peers.insert`, which is mistaken for the monadic trie insertion function. Pure callees' own accesses are cleared, and calls outside `Leanux/WG` are not followed. `delTimer` is reported with `allowedips config peers`, with no `timers`; `peerPut` is reported without timers although its call to `retirePeerUnits` removes timer identities in `Kernel/Defs.lean:2059–2063`.

The matrix is useful for finding candidate owners. It cannot establish absence of cross-subsystem access, and the 59-leaf figure is not an implementation inventory. The prose also calls 53 definitions “five or six” groups in section 4; its own histogram gives 29 (53 includes the 24 four-group definitions).

Correct the small parser errors if the probe is retained, label the output as lexical candidates, and manually follow the proposed leaves through accessors, pure helpers and kernel services. A compiler-checked sample of each intended signature is more useful here than building an elaborate static-analysis gate.

**3. High — The eight WireGuard groups do not yet have a state representation or sufficient signatures.**

Section 2 retains `dev : Option WG.Device`; section 4 instead promises each group as a subrecord of `WGWorld`. The groups cut through the same device and through each stored peer. The note does not say how a group is extracted and written back, how absent devices/peers are represented, or how a two-group computation is lifted. One lift per individual group does not supply the combined state of the 43 claimed two-group functions.

The motivating `indexLookup : StateT KeyTables AmbientM ...` signature is insufficient under the note's own field assignment. `WG/Peer.lean:243–268` calls `peerGetMaybeZero`, increments the peer's reference count, and stores the result back into the owner's embedded peer word. These effects span the proposed keys and peers groups. `drivers/net/wireguard/peerlookup.c:217–222` confirms that the store-back and strong reference are real C behavior, including the NULL result. The recent index-lookup repair must survive this narrowing.

Likewise `armTimer` and `delTimer` (`WG/State.lean:145–171`) update a timer inside a `Peer` in the device's peer map, not just `WGWorld.timers`' dispatch metadata. Their current `getPeer` also checks device and peer existence. The fields really are embedded in `struct wg_peer` (`drivers/net/wireguard/peer.h:37–67`), alongside keys, queues and statistics.

Spell out one representative narrowed state and its extraction/update operations before estimating the whole set: index lookup with peer acquisition, timer arm/delete, and an allowed-IPs operation are enough to expose the choices. Prefer grouping fields inside their existing C-shaped owners and passing the required records explicitly where cheap. Do not silently duplicate owner words or turn one peer store into several independently populated stores. Keep a function over `WG.M` where narrowing needs a larger representation redesign; the user's “where ... cheaply” qualification allows that.

Routing inside the coarse `WGWorld` is workable for today's only user, provided `Net.Routing` remains its own component and its API does not depend on `WG.Device`. The relevant boundary is concrete: `routeLookup` (`Kernel/Defs.lean:1705`) mutates `defaultRoute4Accessed`, while `dstCacheGet`/`dstCacheSet` (`WG/Socket.lean:166,180`) mutate the peer's endpoint cache. A send needs both, with the routing-generation relationship intact. Nesting those components in one world is a packaging choice, not evidence that namespace routing is owned by `wg_device`. Device removal must also retain the existing lifetimes of `netIfindexNext`, global counters and `lastUnderLoad`; they are not device-reset state merely because they reside in `WGWorld`.

**4. Medium — Ambient services and the performance experiment need a more precise boundary.**

The proposed `AmbientM`, `WG.M` and `liftWG` are valid Lean 4.35 constructions. A small isolated spike compiled implicit calls from `WG.M` to an ambient logger, checked log ordering and unchanged unrelated state, checked propagation of a failure after logging, and proved the generic lift's unrelated-field preservation. Its final run took 0.37 seconds; this says nothing about the full mirror's elaboration or throughput. A separate expected-failure spike calling `TaskM Unit` from `FS.M Unit` produced `Type mismatch ... TaskM Unit ... expected ... FSM Unit`: the standard ambient lift does not supply sibling-world access.

Some services currently grouped under `Kernel/Defs.lean` need reassignment rather than wholesale migration to `AmbientM`. `recordQueued` and `peekQueuedUnit` read `armRecords` (`:1996,2017`), which the proposal moves into WG timers; `retirePeerUnits` and `retireDeviceUnits` change both ambient identities and WG timer identities (`:2059–2074`). These can be WG operations using ambient helpers, but that assignment must be explicit. Also, `steps` and section stamps are not written only by the named kernel primitives: see `Seccomp/Bridge.lean:67`, `Env/Batch.lean:39,41`, and runner resets. The listeners described as read-only `NetFixture` facts are mutable delivery queues.

Keeping Env over the product is appropriate. Measure the actual worker/scheduler boundary after conversion, including group lifts inside loops, and keep build/elaboration time separate from model-replay runtime. Section 8.2 proposes measuring the final cost in step 1, before the subsystem and group migrations occur. That measurement cannot validate the later lift placement or justify a few-percent runtime expectation. The local toolchain's `Init/Control/State.lean` documents the extra reference introduced by get/set-style updates versus `modifyGet`; runtime cost also depends on how the eventual extraction and writeback retain shared records.

**5. Medium — Delete structural frames, but retain ambient parameters and product-level execution claims during the retrofit.**

There is substantial real deletion available. For example, campaign 1's `Proofs/Framing/FS.lean:17` proves `allocFile_sameWGKernel`, and `Proofs/WG/Keypairs/Frames/FS.lean:19` transports the same fact to a snapshot. Once file operations cannot access WG state, their per-function preservation proofs can be replaced by the generic lift property. This supports the user's deletion direction.

However a `WG.M α` computation has type

```text
WGWorld → Ambient → Except Stop ((α × WGWorld) × Ambient)
```

Local execution contracts therefore need both input states and both successful output states, even when their predicates project only WG fields. Simply substituting `WGWorld` for `World` in a theorem about `action.run w = .ok (a,w')` does not give a well-typed contract. This matters for contracts that inspect consumed records, order, and exact errors, not just their proof scripts.

Evidence: campaign 1's `WG/KeyLifetime/Statements.lean` begins with `original_age_test` and `original_age_branch`, which relate exact clock consumption and decision logs. Campaign 2 already distinguishes `Ensures`, `Returns` and `Observes` in `WG/Campaign2/Bridge.lean:74` onwards, quantifying concrete executions while using a WG-plus-ambient observation. Preserve its success/existence/error distinctions during retyping.

The logged runner also remains a computation over the product. Main's `Proofs/Logged/Runner.lean:13–122` reconstructs full trace execution, including file outputs, SIGPIPE, record exhaustion and exact indexed failures; `executeTraceLogged_erases` preserves complete JSON and errors. Its state cannot be reduced to WG alone. The environment and syscall observers need the same distinction between local and product execution as the executable code.

Define the local contract shape, product contract shape, and the small generic lift/ghost-erasure bridge first. Then delete per-function structural frames and repair uses. Do not interpret “a proof whose statement is gone is deleted” as permission to remove terminal guarantees or error-preservation claims. File/identifier counts are candidate deletion counts, not demonstrated savings. No old-world compatibility wrapper or old/new executable equivalence campaign is needed to make this distinction.

**6. High — The staging and ten-day estimate are internally inconsistent with the required campaign order.**

Step 1 says the product replaces `World` in a types-only commit and all modules still build over `M`. Existing code immediately projects `w.k`, `w.hidden`, etc.; those fields disappear. Changing the monad alias does not rewrite those expressions. Without compatibility wrappers, the first replacement commit must include the affected accesses and initialization/composition code, or step 1 must be only an unused-types/spike commit. Steps 2–5 are consequently not independent compiling conversions as written.

More decisively, the user decision has campaign 1 land before the split. At that point main's proof tree is campaign 1's tree, not the 1,399-theorem tree budgeted in step 8. Requiring the proof gate and all register rows current at split landing makes campaign 1's retrofit part of that landing's critical path. Deferring it to the separately costed step 10 while passing the complete proof gate is impossible. The project's standing rules permit mirror work to land with reported proof lag; if that is the intended resolution, say so instead of promising a green proof gate. This review does not choose a different campaign order on the user's behalf.

Counts from the pinned snapshots, counting tracked `.lean` files under `Leanux/Proofs/` and named theorem declarations after stripping comments:

| Snapshot | Proof files | Theorems | Theorems in paths containing Frames, Framing or Logged |
| --- | ---: | ---: | ---: |
| main `cb2348e` | 48 | 1,399 | 1,228 |
| campaign 1 `8f9b8a25` | 456 | 7,076 | 2,836 |
| campaign 2 `b579df9c` | 365 | 2,870 | 1,490 |

Campaign growth makes these different from the note's unpinned campaign counts; it is not evidence that those historical theorem totals were fabricated. Main's 1,399/1,228 totals reproduce, but its claimed 103 proof files do not. Campaign 2 currently adds 317 proof files containing 1,471 theorems relative to the set of main proof paths, before counting modifications of existing files. Its work can no longer be estimated as just 700 additional theorems. Main's register already reports lag from earlier mirror changes, so even that smaller baseline is not a clean, currently passing retrofit starting point.

The ten days are not a defensible completion estimate yet. Re-estimate after settling shared task access, compiling representative group signatures, and choosing the actual proof landing baseline. Separate the coarse subsystem migration from optional cheap narrowing and from proof repair. Budget full-project compile and scoped replay measurements after the real lifts exist; use the existing validation gates, without adding a new audit framework.

**Verdict: redesign.**

Retain the coarse WG boundary, separate routing component, nested ambient monad, and deletion of structural frame boilerplate. Revise the task/signal composition contract, define representative within-WG projections and updates, and correct the retrofit/staging plan before implementation. These are changes to the design's claimed executable boundaries, not details that can safely be left to compiler errors. The immediate stop risk is certain for the written sibling-world design; Lean's basic lifting mechanism is not the blocker.

Validation was limited to this read-only review: rerunning the access probe at both pinned mirror revisions, recounting proof declarations via `git show`, inspecting the cited C and Lean paths, and the isolated Lean 4.35 experiments. No model or proof-tree gate was run, and no proof currency is claimed. Main's documented proof lag remains in effect.

To reproduce the access measurement in a disposable directory containing the selected revision's `Leanux` tree, run the pinned probe with that directory as `ROOT`. For example, from a task worktree at the chosen mirror revision:

```sh
capped -- python3 -B -c 'import pathlib,subprocess,sys; p="scripts/probes/state-split-access.py"; s=subprocess.check_output(["git","show","1cca44e7:"+p],text=True); exec(compile(s,p,"exec"),{"__name__":"__main__","__file__":str(pathlib.Path(p).resolve())})' --functions
```

Omit `--functions` for the matrix. Proof counts can be reproduced by enumerating `git ls-tree -r --name-only <pinned-ref> Leanux/Proofs/`, reading each `.lean` file with `git show`, stripping comments, and counting `^\s*(?:(?:private|protected)\s+)?theorem\s+`. The matrix/parser counterexamples and exact Lean state types above are the substantive conclusions; temporary measurements and experiment files are not retained.

To reproduce the successful Lean check, save this fragment as `.tmp/MonadSpike.lean` in a disposable task worktree and run `capped -- scripts/in-bundle lean .tmp/MonadSpike.lean`:

```lean
import Std

structure Ambient where
  log : List Nat := []
  deriving Repr, BEq
structure WGWorld where
  value : Nat := 0
  deriving Repr, BEq
structure World where
  ambient : Ambient := {}
  wg : WGWorld := {}
  fs : Nat := 7
  deriving Repr, BEq
abbrev AmbientM := StateT Ambient (Except String)
abbrev WGM := StateT WGWorld AmbientM
abbrev M := StateT World (Except String)
def record (n : Nat) : AmbientM Unit :=
  modify fun a => { a with log := a.log ++ [n] }
def worker : WGM Nat := do
  record 1
  modify fun w => { w with value := w.value + 1 }
  record 2
  return (← get).value
def liftWG (x : WGM α) : M α := fun w => do
  let ((a, wg), ambient) ← (x.run w.wg).run w.ambient
  return (a, { w with wg, ambient })
#guard match (liftWG worker).run {} with
  | .ok (n,w) => n == 1 && w.wg.value == 1 && w.ambient.log == [1,2] && w.fs == 7
  | .error _ => false
def failWorker : WGM Unit := do
  record 1
  throw "stop"
#guard match (liftWG failWorker).run {} with
  | .error e => e == "stop"
  | .ok _ => false
def localContract (a : WGM α) : Prop :=
  ∀ s ambient x s' ambient', (a.run s).run ambient = .ok ((x,s'),ambient') → True
example (x : WGM α) (w : World) (a : α) (w' : World)
    (h : (liftWG x).run w = .ok (a,w')) : w'.fs = w.fs := by
  simp only [liftWG, StateT.run] at h
  cases hx : (x.run w.wg).run w.ambient with
  | error e =>
    simp only [StateT.run] at hx
    rw [hx] at h
    cases h
  | ok out =>
    rcases out with ⟨⟨a',wg⟩,ambient⟩
    simp [StateT.run] at hx
    simp [hx] at h
    cases h
    rfl
```

For the expected sibling-lift failure, append the following and rerun; the final definition must fail with a type mismatch.

```lean
abbrev FSM := StateT Nat AmbientM
abbrev TaskM := StateT Bool AmbientM
def signal : TaskM Unit := set true
def pipeWrite : FSM Unit := do
  signal
```
