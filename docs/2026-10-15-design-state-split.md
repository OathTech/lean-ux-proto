# Design: the state split, per-subsystem worlds and narrowed function types — 2026-10-15 [AGENT, fork of the coordinator]

The stream that follows B3. The mirror's one global `World`, which every
module reads and writes through a monad whose type says "may change
anything", becomes a product of per-subsystem worlds, and each module's
functions are typed over the sub-state they access. Nothing in the
executable changes: the same code runs over tighter types, and the
compiler is the retrofit tool for the proof tree.

**Decisions [USER 2026-10-15]**, recorded in `docs/decisions.md` with
their words: subsystems operate over localized world types; functions are
narrowed at the type level to the data they access where that is cheap;
no compatibility wrappers and no equivalence lemmas ("it's just throwing
out fields. Just delete fields and see if anything breaks"); campaign 1
(Codex#2) finishes R3 and R4 and lands, its retrofit one job afterwards;
campaign 2 (Codex#1) stops at its checkpoint and resumes on the split
mirror; the binary adequacy grind (Codex#3) continues with `R` over the
WireGuard world literally; the split starts when B3 is on `main` and lands
before lane C's C1, whose new module retypes then.

**The reasoning [USER 2026-10-15]**, carried here because it decides the
shape. There are two kinds of framing. Structural framing is enforced by
the types and is free: in a program without side effects, a function that
is not passed a piece of state cannot affect it, so the frame is the type.
Non-localizable framing needs footprint invariants, and is to be kept only
where an effect genuinely cannot be localized. The ideal is to strip the
types at every point down to the accessible fields and get the footprints
from referential transparency. The whole-of-Linux state is a hard question
and is not decided here. The immediate fix removes the "one massive global
state where everything gets modified without any type-level guarantee that
things aren't being modified", which should remove most of the pointless
frame lemmas: campaign 1's tree has 6,186 theorems, about 2,800 of them in
`Frames`, `Framing` and `Logged` files, and 441 terminal results.

## 1. The measured access matrix

`scripts/probes/state-split-access.py` (read-only, syntactic: a write is a
field named in a `{ x with f := ... }` update, the mirror's only way to
change state; a read is a `.f` projection; a name held by two structures
is attributed to both and flagged) over `main` de62c9d.

The state, field by field:

| Structure | Fields | Owner in the split |
| --- | ---: | --- |
| `World` | 49 | 14 ambient (the record stream, the decision log, the dispatch bookkeeping, the outputs), 20 WireGuard environment (routing, the fixture's network facts, NET_RX, timers), 1 `k`, the rest runner-only |
| `Kernel` | 43 | 7 WireGuard (`wg`, the two netlink sockets, the two counters, `netIfindexNext`, `ratelimiter`), 28 file layer (files, inodes, pipes, pages, the user, the epoll tables), 4 seccomp (`seccompFilters`, `nextFilter`, `child`, `current`), `task` shared |
| `Task` | 13 | 4 file layer (`files`, `rlimitNofile`, `taskWorks`, `inEventfd`), 5 seccomp (`seccomp`, `noNewPrivs`, `capSysAdmin`, `sigsys`, `sigpending`), 4 signal and lifecycle (`blocked`, `pending`, `exited`, `isKthread`) |
| `WG.Device` | 52 | WireGuard |
| `WG.Peer` | 47 | WireGuard |

Which module touches which structure (reads/writes, of the fields):

| Module | `World` | `Kernel` | `Task` | `Device` | `Peer` |
| --- | --- | --- | --- | --- | --- |
| `Leanux/WG` | 15 / 6 | 9 / 8 | 0 / 0 | 52 / 51 | 47 / 43 |
| `Leanux/FS` | 3 / 2 | 29 / 22 | 6 / 3 | 0 / 0 | 0 / 0 |
| `Leanux/Seccomp` | 7 / 5 | 5 / 4 | 5 / 5 | 0 / 0 | 0 / 0 |
| `Leanux/Kernel` (the accessors, signals) | 22 / 11 | 12 / 10 | 7 / 5 | 4 / 0 | 7 / 0 |
| `Leanux/Env` | 31 / 22 | 7 / 2 | 6 / 5 | 23 / 6 | 5 / 1 |
| `Runner`, `Syscalls`, `Main` | 28 / 12 | 4 / 2 | 4 / 1 | 5 / 0 | 1 / 0 |

The facts the split rests on:

- **No cross-subsystem access.** No file in `Leanux/WG` names a file-layer
  or seccomp definition, and no file in `Leanux/FS` or `Leanux/Seccomp`
  names a WireGuard one (`grep` over the three namespaces). The only
  `Kernel` fields WireGuard touches are its own seven; the file layer and
  seccomp touch none of them. The two apparent exceptions in the matrix
  (`Kernel.child` read and `Kernel.current` written from `Leanux/WG`) are
  the probe's name collisions: a local `let current` and the `.child`
  constructor of an allowed-IPs parent reference.
- **The `World` fields WireGuard reads are environment, not kernel
  state:** `sent`, `hidden`, `timerUnits`, `netRxRaised`,
  `queuedThisCall`, `jiffiesLast`, `armRecords`, `dstCacheRecords`,
  `addrs4/6`, `ipv4Gen/ipv6Gen`, `portBound`, `fixtureNetDevices`,
  `lastUnderLoad`. They are the routing environment (lane C is making it a
  module), the record stream, the dispatch bookkeeping and the fixture's
  network facts. None is file-layer or seccomp state.
- **The shared piece is `Task`,** read and written by the file layer
  (`files`, `taskWorks`, `inEventfd`, `rlimitNofile`) and by seccomp
  (`seccomp`, `noNewPrivs`, `capSysAdmin`, `sigsys`), with the signal and
  lifecycle fields (`blocked`, `pending`, `sigpending`, `exited`) written
  by `Kernel/Signal.lean` and the environment. The C's `task_struct` holds
  all of these; the split keeps the id-keyed shape and splits the record.
- **The ambient effects every module has:** the record stream
  (`World.hidden`, consumed in order by `hidden`), the decision log
  (`World.steps`, appended by `branch`, `branchCmp`, `report`), the NET_RX
  section counter the log stamps, and the stop (`Except Stop`). These are
  written through `Leanux/Kernel/Defs.lean`'s primitives only.
- **Seccomp already has the narrowed form.** Stream U's checker,
  translation and engine (`Classic.lean`, `Translate.lean`, `Engine.lean`)
  are written over a typeclass `SeccompM m` (`Decisions.lean:340`: the
  decision log and the record kinds it needs, nothing else) with one
  instance over `M` in `Bridge.lean`. It is the precedent for the shape in
  section 3.
- **Within WireGuard** (`--functions`, over 238 monadic definitions, the
  footprint closed over the module's own call graph, syntactically): 46
  touch no field group (ambient only: the queue records, the decision
  log), 16 touch one of the eight groups of section 4, 43 two, 41 three,
  24 four, 29 five or six, 39 seven or eight. The entry points (the
  workers, the syscall handlers, the timer callbacks, the send and receive
  paths, `wgSetDevice`, `peerRemove`) reach most of the device through
  their callees, as the C does; the leaves (the allowed-IPs trie, the
  rings and queues, the index table, the cookie and rate-limiter
  functions, the timer arm and delete) are the ones that narrow cheaply.

The proof trees, for the retrofit's size (`git archive` of each branch,
counted the same way):

| Tree | Files | Theorems | In frame files | Statements naming `World` | Naming `Kernel` or `.k` | Mentioning file-layer definitions |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `main` | 103 | 1,399 | 1,228 | — | — | 448 |
| `proofs/campaign` (campaign 1) | 425 | 6,184 | 2,813 | 601 | 361 | about 920 |
| `proofs/campaign-2` (campaign 2) | 167 | 2,114 | 1,271 | 163 | 401 | 456 |

Campaign 2's tree is `main`'s tree plus about 700 of its own; `main`'s
tree is itself mostly frame layer (the window proof's `Logged` and
`Framing` layers), of which the file-layer part (the pipe, eventfd and
epoll frames, 448 theorems) is cross-subsystem from WireGuard's point of
view. The counts by mirror definition mentioned are syntactic and
over-count seccomp (its definition names collide with ordinary words);
the file-layer count is the robust one.

## 2. The per-subsystem worlds

Drawn from the matrix and from the C's ownership tree (`struct wg_device`
owns its peers, index table and queues; `struct net` the routing tables
and sockets; `struct task_struct` its files table, its seccomp state and
its signal state; the file layer its inodes, pipes and epoll objects).

```lean
/-- WireGuard: the device, the netlink sockets, the counters, the rate
    limiter, and the routing environment until a second user appears. -/
structure WGWorld where
  dev : Option WG.Device := none        -- Kernel.wg
  nlSock7 : WG.NlSock := {}             -- Kernel.nlSock7
  nlSock8 : WG.NlSock := {}             -- Kernel.nlSock8
  peerCounter : Nat := 0                -- Kernel.peerCounter
  keypairCounter : Nat := 0             -- Kernel.keypairCounter
  netIfindexNext : Nat := 4             -- Kernel.netIfindexNext
  ratelimiter : Ratelimiter := {}       -- Kernel.ratelimiter
  lastUnderLoad : Option Int64 := none  -- World.lastUnderLoad (receive.c's static)
  routing : Net.Routing := {}           -- World.addrs4/6, defaultRoute4/6, ipv4Gen/6Gen, routes,
                                        -- routesPending, defaultRoute4Accessed (lane C's module)
  net : NetFixture := {}                -- World.portBound, fixtureNetDevices, listenerV4/6 (read-only facts)
  timers : TimerState := {}             -- World.timerUnits, jiffiesLast, armRecords, dstCacheRecords (B3's wheel)
  tx : TxState := {}                    -- World.sent, netRxRaised, queuedThisCall, napiBeforePut, napiAmbiguous

/-- The file layer: files, inodes, pipes, pages, eventfd, epoll, the user
    accounting, and the per-task file state keyed by task. -/
structure FSWorld where
  files : TreeMap FileId File           -- Kernel.files .. Kernel.anonInodeInodeErr (9 fields)
  ...                                   -- Kernel.inodes .. Kernel.pipeUserPagesHard (15 fields)
  ...                                   -- Kernel.eps .. Kernel.epqEpi (13 fields)
  tasks : TreeMap TaskRef FSTask        -- Task.files, rlimitNofile, taskWorks, inEventfd, per task
  userOut : Option ByteArray := none    -- World.userOut, userFds (the read's output)
  userFds : Option (Nat × Nat) := none

/-- seccomp: the filters, the per-task seccomp state keyed by task, the
    sandboxed child's existence and the current task. -/
structure SeccompWorld where
  filters : TreeMap FilterId SeccompFilter   -- Kernel.seccompFilters
  nextFilter : FilterId := 0                  -- Kernel.nextFilter
  tasks : TreeMap TaskRef SeccompTask         -- Task.seccomp, noNewPrivs, capSysAdmin, sigsys, per task
  child : Bool := false                       -- Kernel.child's existence (its contents are the two task tables)
  current : TaskRef := .task                  -- Kernel.current
  translatedLen : Option Nat := none          -- World.translatedLen (the kind-309 length)
  emitted : Std.HashSet String := {}          -- World.emitted (the decision log's seccomp keys)

/-- The signal and lifecycle part of the task, written by Kernel/Signal.lean
    and the environment's child-exit path. -/
structure TaskLifecycle where
  blocked : SigSet := 0
  pending : SigSet := 0
  sigpending : Bool := false
  exited : Bool := false
  isKthread : Bool := false

/-- What every module has: the record stream consumed in order, the
    decision log, the NET_RX section stamp, the dispatch bookkeeping, the
    steering state, the environment's answers and the outputs. -/
structure Ambient where
  hidden : Option (List HiddenRecord) := none
  hiddenPlaceholders : Bool := false
  placeholderCount : Nat := 0
  steps : Array Step := #[]
  netRxSection : Nat := 0
  netRxSections : Nat := 0
  suspended : List Activation := []
  unitPeers : List (Nat × Nat × Nat) := []
  pendingWork : List Nat := []
  fired : Array String := #[]
  steerValues : List (String × Option (List UInt8)) := []
  allocArmed : List String := []
  allocSteered : List String := []
  env : EnvSite → Nat → Bool
  envCalls : List (EnvSite × Nat) := []
  timing : Timing
  extraOut : List (String × Lean.Json) := []
  foreignCreator : Bool := false
  netnsCHolders : List Nat := []
  senderInbox : List InboxDatagram := []

/-- The product the runner holds. -/
structure World where
  ambient : Ambient
  wg : WGWorld
  fs : FSWorld
  seccomp : SeccompWorld
  task : TreeMap TaskRef TaskLifecycle
```

Where each existing field goes, and why, in the cases that need a word:

- `Kernel.task` and `Kernel.child` (two `Task` records) become three
  id-keyed tables, one per owner: the file layer's part of a task, the
  seccomp part, the signal and lifecycle part. The C has one `task_struct`;
  the split keeps the task's identity (`TaskRef`) and splits the record by
  the subsystem that writes each field, which the matrix shows is clean
  (no field is written by two subsystems). `Kernel.current` goes to
  seccomp, its only writer; the file layer reads the current task's files
  through its own table under the same `TaskRef`.
- `World.hidden`, `steps`, `netRxSection(s)` are ambient: the primitives
  `hidden`, `branch`, `report`, `noteNetRxStart` are the only writers and
  every module calls them.
- The dispatch bookkeeping (`suspended`, `unitPeers`, `pendingWork`,
  `fired`, `timerUnits`) is the environment's scheduler state. `timerUnits`
  and `jiffiesLast` are WireGuard's today (its timers are the only timers)
  and go with B3's wheel into `WGWorld.timers`; the rest is ambient, read
  by the scheduler in `Env/Batch.lean` and written by the dispatch
  primitives.
- The routing environment (`addrs4/6`, the default routes, the
  generations, `routes`) is WireGuard's until a second subsystem routes;
  lane C's module replaces these fields with the trie and `rt_cache_flush`'s
  generation, inside `WGWorld.routing`, and moves out to its own world when
  a second user appears.
- `World.sent`, `senderInbox`, `listenerV4/6`: the fixture's datagram
  transport, written by the WireGuard socket layer and the environment's
  delivery; `sent` and the NET_RX raise are WireGuard's transmit state,
  the inbox and listeners the environment's.
- `World.userOut`, `userFds` are the file layer's read output and the
  pipe's descriptors; `extraOut`, `translatedLen`, `emitted` are seccomp's
  outputs and the kind-309 length; each goes to its writer.
- `World.floodExact` is deleted by B4 (landed in the batch).

Not decided here, deliberately: the whole-of-Linux state (the per-subsystem
worlds are the leaves of the C's ownership tree, which composes them
whatever the eventual shape is); the frame generator for the
within-subsystem remainder (section 4 measures how much remains); lenses
or effect classes for cross-component calls (there are none today; lane
C's routing module is called by WireGuard and lives inside `WGWorld`).

## 3. The monad structure, concretely

The cheapest shape in Lean, and the one the seccomp module already uses:
each module's functions are written over its own state in a `StateT` on
the ambient monad, and the runner lifts them into the product.

```lean
/-- The ambient monad: the record stream, the decision log, the dispatch
    bookkeeping and the stop. Every module's monad is a StateT over it. -/
abbrev AmbientM := StateT Ambient (Except Stop)

abbrev WG.M := StateT WGWorld AmbientM
abbrev FS.M := StateT FSWorld AmbientM
abbrev Seccomp.M := StateT SeccompWorld AmbientM

/-- The runner's monad over the product; the lifts are the only place a
    subsystem's state meets another's. -/
abbrev M := StateT World (Except Stop)

def liftWG (x : WG.M α) : M α := fun w => do
  let ((a, wg), ambient) ← (x.run w.wg).run w.ambient
  return (a, { w with wg, ambient })
-- liftFS, liftSeccomp alike; liftTask for the lifecycle table.
```

The ambient primitives (`hidden`, `branch`, `branchCmp`, `report`,
`noteNetRxStart`, `skipAmbient`, `envOk`, `invariant`, `unsupported`) move
from `M` to `AmbientM` and are reached from every module's monad through
the `MonadLift` instance `StateT` gives; nothing in the module code
changes at their call sites.

Signatures before and after:

```lean
-- Leanux/WG/Peer.lean, before
def indexLookup (kinds : List IndexKind) (index : Nat) : M (Option (IndexOwner × PeerId))
-- after
def indexLookup (kinds : List IndexKind) (index : Nat) : WG.M (Option (IndexOwner × PeerId))
-- narrowed further (section 4): over the device's key tables only
def indexLookup (kinds : List IndexKind) (index : Nat) : StateT KeyTables AmbientM (Option (IndexOwner × PeerId))

-- Leanux/FS/Pipe.lean, before and after
def pipeWrite (iocb : Kiocb) (src : IovIter) : M Int
def pipeWrite (iocb : Kiocb) (src : IovIter) : FS.M Int

-- Leanux/Seccomp/Filter.lean, before and after
def secureComputing {E : Type} [BpfEngine E] (e : E) (nr : Int) (sd : SeccompData) : M FilterOutcome
def secureComputing {E : Type} [BpfEngine E] (e : E) (nr : Int) (sd : SeccompData) : Seccomp.M FilterOutcome
```

The accessors follow the types: `getDev`, `modifyDev`, `getPeer`,
`setKeypair` and the rest of `Leanux/WG/State.lean` are over `WG.M`
(`modifyDev f := modify fun s => { s with dev := s.dev.map f }`); the
file layer's `getFile`, `getPipe`, `modifyFiles`, `modifyFdt` over `FS.M`;
seccomp's `getFilter`, `modifySeccomp` over `Seccomp.M`; `getTask` and
`modifyTask` split into the three per-owner tables (each subsystem has its
own `modifyTask` over its own task record). `getK` and `modifyK` disappear:
their 15 uses in `Leanux/WG` are the seven WireGuard fields, and the file
layer's 22 writes through them are its own fields.

The runner and the syscall dispatch (`Leanux/Syscalls.lean:231`,
`dispatch : Syscall → M Int`) stay over the product and lift per arm:
`| .pipe2 flags => liftFS (sysPipe2 flags)`, `| .wgSet attrs =>
netlinkRequest (liftWG (WG.wgSetDevice attrs))`. The environment model
(`Leanux/Env.lean`, `Env/Batch.lean`, `Env/Stack.lean`, `Env/IpStack.lean`)
is genuinely cross-cutting: it runs the WireGuard workers and timers,
delivers datagrams, drives the scheduler, and handles the child's exit; it
stays over `M` and calls into WireGuard through `liftWG`. Its 53 uses of
the WireGuard accessors become 53 lifts, or one lift around each worker
body (`runWorker w (liftWG body)`), which is the same number of edits as
B3 made there.

`Kernel/Signal.lean` (34 definitions over the signal fields) becomes the
lifecycle table's module; `Kernel/Decision.lean` and `Refcount.lean` are
data and unchanged.

## 4. Narrowing within WireGuard

Eight field groups, from the matrix's `Device` and `Peer` fields and
`WGWorld`'s own (the probe's `WG_GROUPS`): `config` (the device's
identity, sockets, MTU, port, fwmark, the static identity), `peers` (the
tables and a peer's identity, endpoint, reference count),
`allowedips` (the trie), `keys` (keypairs, the index table, the handshake
state), `queues` (the rings, the work queues, the skb stores, a peer's
staged and per-peer queues), `timers`, `cookies` (the cookie checker, the
MAC keys, the rate limiter, the under-load clock), `stats`.

What narrows cheaply, measured: the 16 single-group and 43 two-group
definitions, which are the leaves: the allowed-IPs trie's operations
(`allowedips`, with `peers` for the owner), the rings and the per-peer
queue operations (`queues`), the index table and keypair slot operations
(`keys`, with `peers` for the owner word), the cookie checker and the rate
limiter (`cookies`), `armTimer`, `delTimer` and the timer state (`timers`),
the counters (`stats`). Each gets a `StateT <group> AmbientM` type, with the
group a sub-record of `WGWorld` and a lift from the group into `WG.M`
(`liftKeys`), one per group. Those are the 59 definitions whose frames
against the other seven groups then come from the type.

What keeps the `WG.M` type: the entry points and the paths through them
(the 39 definitions touching seven or eight groups, the 53 touching five or
six): the receive and send paths, the handshake create and consume
functions, the workers, the timer callbacks, `wgSetDevice`, `peerRemove`.
These touch most of the device because the C does, and a narrower type
would be a lie or a footprint invariant. No footprint invariants are
written in this stream: within WireGuard, the frames between the groups
that the campaigns' results need stay as they are, for the frame
generator or a later narrowing to retire.

The probe's `--functions` output is the list to work from; its groups are
syntactic and will move a few fields during the build (the note's
estimate allows for it).

## 5. The compile-driven retrofit of the proof tree

No wrappers, no equivalence lemmas. The world types change, the mirror is
rebuilt, the proof tree is rebuilt, and each failure is one of three
kinds:

- **A statement over `World` whose function now takes a local world**
  (campaign 1: 601 statements name `World`, 361 name `Kernel` or `.k`;
  campaign 2: 163 and 401): retyped. A result's projection
  (`Snapshot` of the keypairs, `WGKernelView`) is already WireGuard-only
  and becomes a projection of `WGWorld`; the statement is the same
  proposition over the smaller state and its proof is the same proof.
- **A frame lemma that is now unstatable**, because the function's type
  no longer includes the field (every file-layer frame against a
  WireGuard function, every WireGuard frame against a file-layer function,
  the seccomp band: on campaign 1 about 920 theorems mention file-layer
  definitions, on `main` 448): deleted, with the uses that needed it
  replaced by nothing (the type) or by the one lift lemma per subsystem
  ("a lifted `WG.M` computation changes only `wg` and `ambient`"), proved
  once in `Leanux/Proofs/Framing/Lift.lean`.
- **A frame lemma that is still statable** (within WireGuard, between the
  groups a result observes and the function's group; the `Logged`
  shadow semantics that tracks a function's effects in order): kept, and
  repaired where its proof unfolded through an accessor whose definition
  moved (the `frame_same` tactic's `using` lists name the accessors).

Nothing is re-proved: a proof that typechecks after retyping is done; a
proof whose statement is gone is deleted. The rule for the campaigns'
retrofit tasks is "delete before repair": a frame that the types or the
lift lemma now give is removed even if its old proof would still compile.

The `Logged` layer is the one place needing judgement. It re-defines the
mirror's functions with a log of their effects and proves erasure to the
originals; the erasure theorems are real content (they are what lets a
whole-run result talk about effects in order) and are kept, retyped over
the local worlds; the parts of it that exist only to track that a function
did not touch another subsystem's state go with the frames.

The counts above are the upper bounds of each kind; the build reports the
real ones.

## 6. Effects elsewhere

- **The binary adequacy track** (`binary/`): `R` is a relation over
  `WGWorld` by the type, which is the minimal `R` of the amended charter
  (section 1, 2026-10-15) by construction rather than by discipline.
  Codex#3's `Representation.lean` and `MirrorHistory.lean` name mirror
  types and retype at its next merge; its parked components for task,
  seccomp and file state are outside `WGWorld` and stay parked.
- **Lane C** (`Leanux/Net/Fib/`, mid-build): its routing state is
  `WGWorld.routing`; its functions are typed over the routing group and
  lifted into `WG.M` at the send and receive paths' calls, which is the
  within-WireGuard narrowing of section 4 applied to a new module. It
  retypes when the split lands, before its own landing.
- **The differential check:** nothing. The executable is the same program
  over the same trace format with the same records consumed in the same
  order; the runner's outputs are unchanged. The claim is that the fast
  tier (the build and the unit tests, including the model-replay tests)
  and the full check at the claim point show identical counts to the
  landing before: the same number of traces, operations, agreements,
  obligations and distinct rows. A difference in any count is a defect of
  the split, never a finding about the kernel.
- **The campaigns' regime:** a named prerequisite, pause-and-wait, for
  campaign 2 and the binary track; campaign 1 lands first and retrofits
  after.

## 7. Order of work and estimate

| Step | What | Days |
| --- | ---: | ---: |
| 1 | The world types, `Ambient`, the ambient primitives over `AmbientM`, the lifts; the model builds with every module still over `M` through a temporary `M := StateT World` that is the product (one commit, the types only) | 1 |
| 2 | `Leanux/Seccomp` over `Seccomp.M` (the smallest, 43 monadic definitions, and the bridge already exists) | 0.5 |
| 3 | `Leanux/FS` over `FS.M` (202 monadic definitions, 3,869 lines; `Kernel/Signal.lean` to the lifecycle table) | 1.5 |
| 4 | `Leanux/WG` over `WG.M` (239 monadic definitions, 5,875 lines; the accessors in `State.lean`) | 1.5 |
| 5 | The environment and the runner over the product with the lifts (`Env.lean` 1,036 lines, `Env/*` 774, `Runner.lean` 1,136, `Syscalls.lean` 397) | 1.5 |
| 6 | The within-WireGuard groups and the 59 narrowed leaves (section 4) | 1.5 |
| 7 | Build, the five-module unit tests, the `wireguard`, `pipes`, `epoll` and `seccomp` suites during the task; the full check, the controls and the sentinels at the claim point, with the identical-counts claim of section 6 | 1 |
| 8 | `main`'s proof tree retrofitted by the deletion rule (1,399 theorems, 448 file-layer frames deleted, the rest retyped), so the register's rows and the proof gate hold at the landing | 1.5 |
| | **The stream** | **10** |
| 9 | Campaign 2's retrofit (its own 700 theorems over the retyped `main` tree), by Codex#1 on resumption | 1 to 2 |
| 10 | Campaign 1's retrofit after it lands (6,184 theorems: about 920 file-layer frames deleted, 601 statements retyped, the `Logged` layer re-judged), by Codex#2 or a fork | 4 to 6 |

About 1.0 WU for the stream at the plan's rate, plus the two retrofits.
Steps 2 to 4 are independent of each other once step 1 is in and can run
as three forks; steps 5 and 6 follow them.

## 8. Risks

1. **Stopping risk: a module that genuinely needs two worlds.** The matrix
   says there is none today: no WireGuard function names file-layer or
   seccomp state, and the shared `Task` splits cleanly by writer. The one
   place to watch is the environment's child-exit path, which writes the
   lifecycle table and the file layer's task works in one operation; it
   stays in the runner's monad over the product, which is allowed. If a
   mirror function turns out to need two subsystems' state, the split
   stops there and reports: that function is the first cross-component
   call and needs the composition principle this note does not decide.
2. **Elaboration cost.** Each lift is a `StateT` run and re-wrap; the
   runner and the environment add one per worker body and per syscall arm,
   a few hundred in all, and the hot loops (the workers, the rings) stay
   inside one module's monad with no lift. Step 1's build measures it; a
   slowdown of the model-replay unit tests beyond a few percent is a
   finding to report before going on.
3. **The seccomp child.** `Kernel.child` is a second `Task` record whose
   file and seccomp parts the three tables hold under `TaskRef.child`; the
   probe's child-exit and wait paths read both parts, in the runner. The
   `test_model_replay` tests cover them and must stay green.
4. **The `Logged` layer** may carry more cross-subsystem content than the
   counts suggest, since its files import only proof-internal modules;
   step 8 finds out on `main`'s tree first, which is the small instance.
5. **The campaigns' carries land on the retyped tree in the middle of
   their own merges**: the rule is that campaign 1 lands before the split
   and campaign 2 pauses, so neither merges across it.

## 9. What this stream does not do

No footprint invariants; no frame generator; no lenses or effect classes
for cross-component calls; no change to the trace format, the records,
the kernel, the harness or the check rules; no change to any theorem's
proposition beyond its state type; no whole-of-Linux state design.
