# Design: the state split, per-subsystem worlds and narrowed function types — 2026-10-15, revision 2 of 2026-10-16 [AGENT, fork of the coordinator]

The stream that follows B3. The mirror's one global `World`, which every
module reads and writes through a monad whose type says "may change
anything", becomes a product of per-subsystem worlds, and each module's
functions are typed over the sub-state they access. Nothing in the
executable changes: the same code runs over tighter types, and the
compiler is the retrofit tool for the proof tree.

**Revision 2** disposes of the independent review by Codex#4
([the review](2026-10-15-review-state-split.md), verdict: redesign) and
folds in its [companion proposal](2026-10-15-state-split-companion.md)
where it holds. Section 10 lists the findings one by one; section 11
lists what this revision changes against revision 1 and which of the
changes are proposals awaiting the user. The measurements are rerun on
`main` e5afc0f (merged into this branch), where B3, the audit fixes and
lane C's first landing have added the timer wheel, the routing module and
their state.

**Decisions [USER 2026-10-15]**, recorded in `docs/decisions.md` with
their words and unchanged by this revision: subsystems operate over
localized world types; functions are narrowed at the type level to the
data they access where that is cheap; no compatibility wrappers and no
equivalence lemmas ("it's just throwing out fields. Just delete fields and
see if anything breaks"); campaign 1 (Codex#2) finishes R3 and R4 and
lands, its retrofit one job afterwards; campaign 2 (Codex#1) stops at its
checkpoint and resumes on the split mirror; the binary adequacy grind
(Codex#3) continues with `R` over the WireGuard world literally; the split
starts when B3 is on `main` and lands before lane C's C1 (C1 has since
landed; its module retypes in the split).

**The reasoning [USER 2026-10-15]**, carried because it decides the shape.
Two kinds of framing: structural, enforced by the types and free, because
in a program without side effects a function that is not passed a piece
of state cannot affect it; and non-localizable, needing footprint
invariants, to be kept only where an effect genuinely cannot be localized.
The ideal is to strip the types at every point down to the accessible
fields and get the footprints from referential transparency. The
whole-of-Linux state is a hard question not decided here. The immediate
fix removes the "one massive global state where everything gets modified
without any type-level guarantee that things aren't being modified".

## 1. The measured access matrix

`scripts/probes/state-split-access.py` prints, for each module group,
which fields of `World`, `Kernel`, `Task`, `WG.Device` and `WG.Peer` it
touches and which it writes, from the text: a write is a field named in a
`{ x with f := e }` or shorthand `{ x with f }` update (the mirror's only
way to change state), a read is a `.f` projection; a name held by two
structures is attributed to both and flagged. **Its output is a list of
lexical candidates, not a sound dependency analysis** (the review's
finding 2): it does not resolve namespaces, it does not see a whole-record
replacement (`setPeer` takes any `Peer`), and its call graph is by name.
Revision 2 repaired the four parser errors the review found (shorthand
updates, the summary's label, default arguments before the return type,
container method names taken for calls) and extended the walk to
`Leanux/Net` and the kernel helpers; the figures below are from the
repaired probe on e5afc0f.

The state (51 `World` fields, 47 `Kernel`, 13 `Task`, 52 `Device`, 52
`Peer` on e5afc0f), by module (touched / written):

| Module | `World` | `Kernel` | `Task` | `Device` | `Peer` |
| --- | --- | --- | --- | --- | --- |
| `Leanux/WG` | 16 / 7 | 11 / 10 | 0 / 0 | 52 / 51 | 52 / 48 |
| `Leanux/FS` | 3 / 2 | 29 / 22 | 6 / 3 | 0 / 0 | 0 / 0 |
| `Leanux/Seccomp` | 7 / 5 | 5 / 4 | 5 / 5 | 0 / 0 | 0 / 0 |
| `Leanux/Net` (lane C) | 6 / 3 | 2 / 2 | 0 / 0 | 0 / 0 | 0 / 0 |
| `Leanux/Kernel` (the accessors, the signals, the wheel) | 24 / 12 | 12 / 10 | 7 / 5 | 4 / 0 | 7 / 0 |
| `Leanux/Env` | 33 / 24 | 7 / 2 | 6 / 5 | 23 / 6 | 5 / 1 |
| `Runner`, `Syscalls`, `Main` | 30 / 13 | 5 / 2 | 4 / 1 | 5 / 0 | 1 / 0 |

The facts the split rests on, each checked by reading the code and not
only by the probe:

- **No access between the WireGuard, file-layer and seccomp object
  stores.** No file in `Leanux/WG` names a file-layer or seccomp
  definition, and no file in `Leanux/FS` or `Leanux/Seccomp` names a
  WireGuard one. WireGuard's `Kernel` fields are its own eleven (`wg`, the
  two netlink sockets, the two counters, `netIfindexNext`, `ratelimiter`,
  the two FIB tables, `timerClk`, `timerEnqueues`); the file layer and
  seccomp touch none of them. (The matrix's apparent WireGuard reads of
  `child` and `current` are name collisions: a local `let current` and the
  `.child` constructor of an allowed-IPs parent reference.)
- **The file layer and seccomp both reach the task's signal state, inside
  mirror functions** (the review's finding 1, confirmed on e5afc0f):
  `FS/Pipe.lean:427,459` call `sendSig .task SIGPIPE 0` from `pipeWrite`;
  `FS/FileTable.lean:152,155` read `Task.isKthread` and `Task.exited` in
  `fput`; `Seccomp/Filter.lean:319,350` call `forceSigSeccomp` from the
  filter; `Kernel/Signal.lean` reads `blocked`, writes `sigsys`, `blocked`,
  `pending` and `sigpending`, and resolves `Kernel.current`. These are the
  C's call sites (`kernel/signal.c:1328-1363` reads the action and the
  blocked set and generates the signal). Revision 1's three id-keyed task
  tables in sibling worlds would have made `pipeWrite : FS.M Int` a type
  error at its own signal call; revision 2 keeps one task store that the
  file layer, seccomp and the signal module share (section 2).
- **The `World` fields WireGuard reads are environment, not kernel
  state:** `sent`, `hidden`, `timerUnits`, `timerPassStep`, `netRxRaised`,
  `queuedThisCall`, `jiffiesLast`, `armRecords`, `dstCacheRecords`,
  `addrs4/6`, `ipv6Gen`, `portBound`, `fixtureNetDevices`,
  `lastUnderLoad`.
- **Lane C's routing module** (`Leanux/Net/Fib`, `Leanux/Net/Route.lean`,
  landed) is its own component already: `getTable`/`modifyTable` select
  `Kernel.fib4` or `fib4C` by `World.fibCreatorNs`; `routeLookup` and
  `neighbourClassify` read `addrs4`, `addrPlens4` and `neighbours` and
  write `neighbours`; nothing in it names `WG.Device`.
- **The ambient effects every module has:** the record stream
  (`World.hidden`, consumed by `hidden`), the decision log (`World.steps`,
  appended by `branch`, `branchCmp`, `report`), the NET_RX stamp, the
  stop. The kernel helper file is not their exclusive writer
  (`Seccomp/Bridge.lean:67` appends to `steps`, `Env.lean:673-675` and
  `Runner.lean:1149` reset them): those writes become explicit
  `AmbientM` operations where they are.
- **Seccomp already has the narrowed form.** Stream U's checker,
  translation and engine are written over a typeclass `SeccompM m`
  (`Decisions.lean:340`) with one instance over `M` in `Bridge.lean`.
- **The product-level orchestration inside today's seccomp directory**
  (the review's finding 1): `Seccomp/Syscalls.lean:149-201`
  (`sysSeccompProbeChild`) calls `Env.forkClocks`, `Env.childCreate`,
  `Env.childExit`, `Env.childDrop` and switches `Kernel.current`;
  `trapReturn` (`:109`) calls `Env.trapDelivered`. These stay over the
  product (section 3).

The proof trees, for the retrofit's size, at the heads on 2026-10-16
(tracked `.lean` files under `Leanux/Proofs`, named theorem declarations
after stripping line comments):

| Tree | Files | Theorems | In paths containing Frames, Framing or Logged |
| --- | ---: | ---: | ---: |
| `main` e5afc0f | 48 | 1,399 | 1,228 |
| `proofs/campaign` 00641c6 (campaign 1) | 471 | 7,405 | 2,816 |
| `proofs/campaign-2` 04b2f7c (campaign 2) | 475 | 3,225 | 1,510 |

Campaign 2's tree is `main`'s plus its own additions (317 new files and
about 1,500 theorems at the review's snapshot, growing); it can no longer
be sized as "about 700 theorems". By the user's decision campaign 1 lands
before the split, so **the proof tree the split retrofits is campaign 1's
landed tree, not `main`'s 1,399** (the review's finding 6; section 7).

## 2. The per-subsystem worlds

Drawn from the matrix and from the C's ownership tree, with one change
against revision 1 marked.

```lean
/-- The task store, shared by the file layer, seccomp and the signal
    module: one mandatory parent, one optional child, the current task.
    [Revision 2: replaces three id-keyed tables in sibling worlds; see 11.] -/
structure TaskWorld where
  task : Task                       -- Kernel.task, the record unchanged (files, rlimit, task works,
  child : Option Task := none       --   the signal set, seccomp state, sigsys, flags)
  current : TaskRef := .task        -- Kernel.current

/-- WireGuard: the device, the netlink sockets, the counters that outlive
    a device, the rate limiter, the timer wheel's state, the routing
    component until a second user appears, the fixture facts it reads and
    its transmit state. -/
structure WGWorld where
  dev : Option WG.Device := none        -- Kernel.wg
  nlSock7 : WG.NlSock := {}             -- Kernel.nlSock7
  nlSock8 : WG.NlSock := {}             -- Kernel.nlSock8
  peerCounter : Nat := 0                -- Kernel.peerCounter (outlives the device)
  keypairCounter : Nat := 0             -- Kernel.keypairCounter (outlives the device)
  netIfindexNext : Nat := 4             -- Kernel.netIfindexNext (outlives the device)
  ratelimiter : Ratelimiter := {}       -- Kernel.ratelimiter (its own refcount lifetime)
  lastUnderLoad : Option Int64 := none  -- World.lastUnderLoad (receive.c's static)
  timerClk : Option UInt64 := none      -- Kernel.timerClk, timerEnqueues (B3's wheel base)
  timerEnqueues : Nat := 0
  timers : TimerState := {}             -- World.timerUnits, jiffiesLast, timerPassStep, dstCacheRecords
  routing : Net.Routing := {}           -- Kernel.fib4, fib4C; World.addrs4, addrPlens4, addrs6, defaultRoute6,
                                        --   ipv6Gen, neighbours, fibCreatorNs (lane C's component, section 4)
  fixture : WGFixture := {}             -- World.portBound, fixtureNetDevices (function-valued inputs WG reads)
  tx : TxState := {}                    -- World.sent, netRxRaised, queuedThisCall

/-- The file layer's object stores and accounting (31 Kernel fields) and
    its outputs. -/
structure FSWorld where
  files : TreeMap FileId File ...       -- Kernel.files .. anonInodeInodeErr (9), inodes .. pipeUserPagesHard (15),
                                        --   eps .. epqEpi (13)
  userOut : Option ByteArray := none    -- World.userOut
  userFds : Option (Nat × Nat) := none  -- World.userFds

/-- seccomp's filter store and its outputs. -/
structure SeccompWorld where
  filters : TreeMap FilterId SeccompFilter   -- Kernel.seccompFilters
  nextFilter : FilterId := 0                  -- Kernel.nextFilter
  translatedLen : Option Nat := none          -- World.translatedLen
  emitted : Std.HashSet String := {}          -- World.emitted (the bridge's deduplication)

/-- The fixture's mutable transport and control state, product-level. -/
structure EnvWorld where
  listenerV4, listenerV6, senderInbox         -- delivery queues (mutable, not facts)
  foreignCreator, netnsCHolders               -- W8
  napiBeforePut, napiAmbiguous                -- W7's placement
  routesPending, routes                       -- the fixture's extra MTU routes
  lastAdvance, hiddenAhead                    -- B3's advance bound, the runner's look-ahead
  mtu                                         -- the sender's MTU (W4)

/-- What every module has: the record stream, the decision log, the
    section stamps, the dispatch bookkeeping, steering, the environment's
    answers, the shared output accumulator. -/
structure Ambient where
  hidden, hiddenPlaceholders, placeholderCount
  steps, netRxSection, netRxSections
  suspended, unitPeers, pendingWork, fired
  armRecords                                  -- read by the queue records and the timer records alike
  steerValues, allocArmed, allocSteered
  env, envCalls, timing
  extraOut                                    -- WG dumps and seccomp probes both append to it

structure World where
  ambient : Ambient
  tasks : TaskWorld
  wg : WGWorld
  fs : FSWorld
  seccomp : SeccompWorld
  fixture : EnvWorld
```

Every one of the 50 non-`k` `World` fields and the 47 `Kernel` fields on
e5afc0f is assigned exactly once above (the companion's inventory,
reconciled against this head: B3 added `timerClk`, `timerEnqueues`,
`timerPassStep`, `lastAdvance`, `hiddenAhead`; lane C added `fib4`,
`fib4C`, `addrPlens4`, `neighbours`, `fibCreatorNs`; W4's `mtu`). The
inventory is a cutover aid and is reconciled once more against the actual
baseline before coding.

Where a placement needs a word:

- **The task is one record in one store.** The matrix shows the file layer
  and seccomp writing disjoint fields of it, but the signal module writes
  the fields both of them reach through their own calls, so splitting the
  record by writer would need three maps whose creation and removal must
  agree and whose missing rows must fail noisily, where today one optional
  child encodes existence. `getTask`/`modifyTask` keep their missing-child
  failure; `getFiles` keeps selecting `.task` (`Kernel/Defs.lean:1758`),
  not `current`; child creation copies the record and resets the same
  fields in the same order (`Env.childCreate`). `sigsys` is the task's
  signal disposition and stays with `blocked`, `pending` and
  `sigpending`; it does not move to seccomp because this slice exercises
  it through SIGSYS.
- **Lifetimes are preserved.** Removing the device does not reset
  `netIfindexNext`, the two counters, the rate limiter's refcount or
  `lastUnderLoad`; each keeps its own update and teardown rule from the
  C. `retirePeerUnits` and `retireDeviceUnits` (`Kernel/Defs.lean:2105,
  2115`) write both ambient unit identities and `timerUnits`; they become
  `WG.M` operations using ambient helpers, in the same order.
- **`armRecords` stays ambient**: `recordQueued` and `peekQueuedUnit`
  (`:2038-2063`) read it for the queue records; the timer records read it
  too; it is the record protocol's flag, not a timer field.
- **The dispatch bookkeeping** (`suspended`, `unitPeers`, `pendingWork`,
  `fired`) is the scheduler's state, read in `Env/Batch.lean` and written
  by the dispatch primitives: ambient.
- **Routing is a component inside `WGWorld`** because WireGuard is its only
  user today; its functions depend on `Net.Routing` and never on
  `WG.Device`, and a peer's `dstCache` stays in the peer and consumes the
  routing generations explicitly. `routeLookup` is stateful (it marks the
  accessed default route). It moves to its own world when a second user
  appears; the split does not touch lane C's algorithm.
- **The fixture's listeners and inbox are mutable delivery queues**, not
  read-only facts (revision 1 called them facts): `EnvWorld`, product
  level. `WGWorld.fixture` holds only the two function-valued inputs
  WireGuard reads (`portBound`, `fixtureNetDevices`).
- `World.floodExact` is gone (B4 deleted it); `World.k` disappears with
  `Kernel`.

Not decided here, deliberately: the whole-of-Linux state; the frame
generator for the within-subsystem remainder; lenses or effect classes for
cross-component calls beyond the shared task services of section 3.

## 3. The monad structure, and the one exception to "the runner composes"

```lean
abbrev AmbientM := StateT Ambient (Except Stop)
abbrev TaskM    := StateT TaskWorld AmbientM        -- the shared task and signal services
abbrev WG.M     := StateT WGWorld AmbientM
abbrev FS.M     := StateT FSWorld TaskM             -- [revision 2: over TaskM, not AmbientM]
abbrev Seccomp.M := StateT SeccompWorld TaskM       -- [revision 2: over TaskM, not AmbientM]
abbrev M        := StateT World (Except Stop)       -- the runner, the environment, the orchestration

def liftWG (x : WG.M α) : M α := fun w => do
  let ((a, wg), ambient) ← (x.run w.wg).run w.ambient
  return (a, { w with wg, ambient })
def liftFS (x : FS.M α) : M α := fun w => do
  let (((a, fs), tasks), ambient) ← ((x.run w.fs).run w.tasks).run w.ambient
  return (a, { w with fs, tasks, ambient })
-- liftSeccomp alike (seccomp, tasks, ambient); liftTask (tasks, ambient).
def liftFSLocal (x : StateT FSWorld AmbientM α) : FS.M α := fun fs => liftM (x.run fs)
```

Each lift starts from the latest product state and writes its layers back
once; no task snapshot is retained across two lifted operations; `Except
Stop` stays under every state layer, so a failure returns the error and no
partial state. Lean's `StateT` lifting lets `FS.M` and `Seccomp.M` call
`TaskM` operations (the signal chain, `getTask`, `modifyTask`,
`getCurrent`) directly; a store-only helper may be `StateT FSWorld
AmbientM` and is lifted by `liftFSLocal`. Checked on this head with the
companion's fragment (`.tmp/SharedTaskSpike.lean`, Lean v4.35.0, 0.4 s):
a file operation followed by a seccomp operation sees the first's task
update, WireGuard and the task's other fields are untouched, the ambient
log is in order, a missing-child failure propagates. The original two-layer
spike (`.tmp/MonadSpike.lean`) passes too, including the proof that a
lifted `WG.M` computation preserves the other fields; the sibling-lift
fragment fails with `TaskM Unit` expected `FSM Unit`, which is the type
error revision 1's design would have met at `pipeWrite`'s signal call.

What each type structurally excludes (the companion's table, adopted):

| Computation | State it can change | Excluded by the type |
| --- | --- | --- |
| `WG.M` | WireGuard, ambient | the task store, the file layer, seccomp, the fixture queues |
| `TaskM` | the task store, ambient | WireGuard, the file-layer and filter stores, the fixture queues |
| `FS.M` | the file layer, the task store, ambient | WireGuard, the filter store, the fixture queues |
| `Seccomp.M` | seccomp, the task store, ambient | WireGuard, the file-layer stores, the fixture queues |
| `M` | the product | nothing; orchestration needs the product |

These are guarantees about state, not about success (an ambient record can
still fail a file operation), and `FS.M` does not prove that the task's
seccomp fields are unchanged: that remainder stays a stated fact where a
result needs it, until a callee's type excludes it.

**The exception, put to the user as a proposal** (section 11): the recorded
formulation "the runner holds the product and is the only composer" gains
one qualification. Subsystem operations may call the shared task and
signal services at the C's existing call sites: a pipe's SIGPIPE stays
inside `pipeWrite`, a seccomp trap's signal inside `seccompFilter`, the
`fput` task-work test inside `fput`. The runner alone assembles the full
product and orchestrates operations that touch independent stores: the
syscall dispatch (`Syscalls.lean:231`, lifting per arm), the environment
model (the workers, the scheduler, delivery, the child's exit), and the
seccomp child probe and trap return (`Seccomp/Syscalls.lean`), which stay
over `M` whatever file they live in; the filter execution beneath them is
`Seccomp.M`.

Signatures, before and after:

```lean
def indexLookup (kinds : List IndexKind) (index : Nat) : M (Option (IndexOwner × PeerId))     -- before
def indexLookup (kinds : List IndexKind) (index : Nat) : WG.M (Option (IndexOwner × PeerId))  -- after; not narrower (section 4)
def pipeWrite (iocb : Kiocb) (src : IovIter) : M Int                                            -- before
def pipeWrite (iocb : Kiocb) (src : IovIter) : FS.M Int                                         -- after (its SIGPIPE through TaskM)
def secureComputing {E} [BpfEngine E] (e : E) (nr : Int) (sd : SeccompData) : M FilterOutcome   -- before
def secureComputing {E} [BpfEngine E] (e : E) (nr : Int) (sd : SeccompData) : Seccomp.M FilterOutcome
```

The accessors follow: `Leanux/WG/State.lean` over `WG.M`; the file
layer's `getFile`, `getPipe`, `modifyFiles`, `modifyFdt` over `FS.M`;
seccomp's `getFilter`, `modifySeccomp` over `Seccomp.M`; `getTask`,
`modifyTask`, `getCurrent` and `Kernel/Signal.lean`'s 34 definitions over
`TaskM`. `getK` and `modifyK` disappear. The environment keeps the product
and lifts whole worker bodies (`runWorker w (liftWG body)`); a helper that
takes a computation argument has that argument's type reviewed, not just
its return type.

## 4. Narrowing within WireGuard: projections defined up front

Revision 1 promised eight sub-records of `WGWorld` and "59 leaves" found
by compiler errors. The review showed that the groups cut through the
same `Device` and the same stored `Peer`, that one lift per group cannot
supply a two-group function, and that the motivating `indexLookup` is not
a keys-only function: it takes a strong reference on the peer and stores
the result back into the owner's embedded word (`peerlookup.c:217-222`).
The repaired probe agrees: `indexLookup` touches `keys` and `peers`,
`armTimer` touches `peers` and `timers`, `delTimer` `peers`.

Revision 2 narrows over the owners that already exist, with one
extraction and write-back adapter per component, and keeps a function
over `WG.M` wherever narrowing would need a second store of the same
objects. The components, their fields, their adapters and the functions
each narrows (the repaired probe's one- and two-group list, 17 and 64
definitions, followed by hand through their callees; `config` in the
probe's output is the device access `getDev`/`modifyDev` itself and is
not counted as a second group):

| Component | Its state (existing owner) | Functions narrowed (measured) | Stays `WG.M` |
| --- | --- | --- | --- |
| Routing | `Net.Routing` in `WGWorld.routing` (lane C's tables, the address lists, the neighbours, the creator flag) | lane C's module as landed: `routeLookup`, `neighbourClassify`, the table operations (`StateT Net.Routing AmbientM`, lifted by `liftRouting`, which replaces only `routing`) | a send: `send4`/`send6` need the route and the peer's `dstCache` |
| Index table | `Device.indexTable` | `indexInsert`, `indexRemove`, `indexRemoveKeypair`, `indexReplaceHandshake`, `indexHashed`, `indexBucket`, `bucketHas`, `unhashEntry` (own group `keys`; the hidden index draw is ambient) | `indexLookup` (the peer get and the store-back span the owner), `peerGetMaybeZero` |
| Allowed-IPs nodes | `Device.nodes`, `Device.nextNode` | `getNode`, `freeNode`, `allocNode`, `slotGet`, `slotSet`, `connectNode`, `chooseAndConnectNode`, `nodePlacement`, `subtree`, `lookupDst`, `lookupSrc` (node identity and dangling-node failures kept) | `insert` and the removals that maintain `Peer.allowedipsList`, unless the combined input proves cheap in the build |
| Cookie checker and rate limiter | `Device.cookieSecret`, `cookieSecretBirthdate`, `cookieEncryptionKey`, `mac1Key`; `WGWorld.ratelimiter`, `lastUnderLoad` | `ratelimiterAllow`, `ratelimiterInit`, `ratelimiterUninit`, `gcEntries`, `makeCookie`, `cookieValidatePacket`, `cookieMessageCreate`, `cookieCheckerInit` (own group `cookies`) | `cookieMessageConsume` (peer-owned cookie fields plus the device's), `sendHandshakeCookie` |
| The skb stores | `Device.txSkbs`, `rxSkbs`, `nextSkb` | `newTxSkb`, `newRxSkb`, `getTxSkb`, `getRxSkb`, `setTxSkb`, `setRxSkb`, `freeTxSkb`, `freeRxSkb` | the queue operations that move an skb between a ring and a peer's queue |
| Rings | explicit `PtrRing` arguments and results as today | nothing changes: no monadic wrapper is added to obtain a group name | — |
| Device configuration | `Device`'s identity, sockets, MTU, port, fwmark | `setMtu`, `socketInit`, `socketReinit`, `socketPort`, `lookupInterface`, `netDevices`, `getNlSock`, `setNlSock`, `wgSetup`, `pubkeyHashtableAlloc` (own group `config`) | `wgSetDevice`, `setPeerCmd`, `wgUp`, `wgDown` |

Rules for each adapter: extraction happens at the original access point
(the device or peer existence check stays where it is, so a malformed
state or record returns the same error in the same order; `armTimer`
consumes and validates its records before `getPeer` and keeps that order
by staying `WG.M`); write-back replaces only the selected fields of the
same owner; no owner word is copied into two stores; no peer-keyed map is
introduced beside `Device.peers`; a narrowed leaf takes no callback that
could mutate the rest of WireGuard. If a component needs several maps with
equal domains, duplicated lifetime markers or a footprint invariant, the
operation stays `WG.M` and the narrowing is reported as deferred. This is
the user's "where this can be done cheaply" applied concretely, and it is
not permission to restructure the mirror for a proof.

What keeps `WG.M` by measurement: the entry points and the paths through
them (the probe's three-to-eight-group definitions: 112 of 241), the peer
acquisition and release (`peerGet`, `peerGetMaybeZero`, `peerPut`,
`keypairPut`), the timers (`armTimer`, `delTimer`, `placeOnWheel`, the
callbacks), the endpoint cache (`dstCacheGet/Set/Reset`), the sends, and
every function whose footprint reaches two owners.

## 5. The compile-driven retrofit of the proof tree

No wrappers, no equivalence lemmas. The world types change, the mirror is
rebuilt, the proof tree is rebuilt, and each failure is one of four kinds
(the review's finding 5 adds the fourth):

- **A statement over `World` whose function now has a local type.** It is
  retyped over the function's actual execution tuple, which for `WG.M α`
  is `WGWorld → Ambient → Except Stop ((α × WGWorld) × Ambient)` and for
  `FS.M α` also carries `TaskWorld`. Substituting `WGWorld` for `World` in
  `a.run w = .ok (x, w')` is not well typed; the local contract quantifies
  over the ambient input even when its predicate observes only a WireGuard
  snapshot. Campaign 2's `Ensures`, `Returns` and `Observes`
  (`Campaign2/Bridge.lean:74-82`) already separate success, existence and
  exact-error claims; those distinctions are preserved through the
  retyping, not collapsed.
- **A structural frame lemma** whose statement the types now make
  unstatable (a file operation against a WireGuard snapshot:
  `Framing/FS.lean`'s `allocFile_sameWGKernel` and its transport in
  `Keypairs/Frames/FS.lean`; the seccomp band; the inverse): deleted, its
  uses replaced by the one lift lemma per subsystem ("a lifted `FS.M`
  computation changes only `fs`, `tasks` and `ambient`"), proved once in
  `Leanux/Proofs/Framing/Lift.lean` (the shape is the `example` in the
  spike). The lift lemma says exactly what can change; it does not say the
  task's seccomp fields are unchanged.
- **A frame that is still statable** (within WireGuard, between the
  owners a result observes; a shared-task fact the file layer needs about
  seccomp's fields; the `Logged` erasure theorems, which are content):
  kept, retyped, repaired where its proof unfolded an accessor that moved.
- **A product-level claim**: the logged runner (`Logged/Runner.lean`)
  reconstructs whole traces with file outputs, SIGPIPE, record exhaustion
  and indexed failures, and `executeTraceLogged_erases` preserves the
  complete JSON and errors; it stays over the product, as do the syscall
  and environment observers. A local observer stays local with its
  ambient input; the small lift and observer bridge is proved once.

Deletion is justified by the guarantee the new type supplies, never by a
theorem ceasing to compile. Terminal results are retyped with their
premises and observable content intact; a terminal claim that cannot be
retained is reported as lag or as a finding, not deleted to turn the gate
green. The lexical counts of section 1 are candidate deletions, not
demonstrated savings; the build reports the real ones.

## 6. Effects elsewhere

- **The binary adequacy track:** `R` is a relation over `WGWorld` by the
  type, the minimal `R` of the amended charter by construction; the
  execution inputs (the ambient state) appear explicitly in its execution
  interface. Codex#3's `Representation.lean` and `MirrorHistory.lean`
  retype at its next merge; the adequacy theorem is not inferred from the
  packaging change.
- **Lane C:** its module is the routing component of section 4, over
  `StateT Net.Routing AmbientM`, lifted at the send and receive paths; it
  retypes in the split, which lands after C1 did.
- **The differential check and behaviour preservation.** The executable
  is the same program over the same trace format with the same records
  consumed in the same order, so the claim is behaviour preservation,
  shown two ways: the model-replay unit tests and the recorded traces
  replayed on the pinned baseline and on the candidate give identical
  outputs and errors (the replay is deterministic given the records; the
  temporary captures are deleted afterwards); and the full check, the
  controls and the sentinels run against the approved oracle at the claim
  point as for any landing. Revision 1 asked for identical record totals
  between two live kernel runs; that is not a sound test (two live runs
  are two schedules) and is withdrawn: a difference in coverage, verdicts
  or records at the claim point is investigated, not normalized.
- **The campaigns' regime:** a named prerequisite, pause-and-wait, for
  campaign 2 and the binary track; campaign 1 lands first and its landed
  tree is the retrofit baseline.

## 7. Order of work, staging and the proof-lag claim

Revision 1's step 1 ("the types only, every module still builds") was
wrong: `w.k`, `w.hidden` and the accessors disappear with the fields, so
no types-only commit compiles without a compatibility layer, which the
user excluded. The coarse cutover is one connected migration, prepared and
built in one worktree before its commit; the type-mechanics spike precedes
it and the unused new types may be committed early.

1. **Pin the baseline** after B3 and campaign 1 have landed (B3 has);
   reconcile the field inventory and the campaign revisions once. Campaign
   2 stays at its checkpoint. (0.5 to 1 day, with the representative
   conversions of step 2's first items.)
2. **The coarse cutover, connected:** the worlds, `Ambient`, `TaskWorld`,
   the ambient and task services, the accessors, every module's
   signatures (seccomp 43 monadic definitions, the file layer 202,
   WireGuard 241, the routing module 74, the kernel helpers), the
   initialization, the syscall dispatch and the environment's lifts, the
   output projections. Seccomp first (the bridge exists), then the file
   layer and WireGuard, which are independent once the services exist and
   can run as two forks, then the environment and runner. (4 to 7 days.)
3. **Build, the fast tier, the affected suites** (`wireguard`, `pipes`,
   `epoll`, `seccomp`); representation mistakes fixed in scope, an apparent
   semantic defect reported. Build and elaboration time measured
   separately from model-replay runtime, after the real lifts exist,
   including the worker and scheduler boundary. (1 to 2 days.)
4. **The mirror claim point:** the full check, the controls and the
   sentinels on the approved oracle; the concrete mirror diff and the
   actual proof lag presented for signoff. **The mirror lands with reported
   proof lag**, as the standing rule allows; a green proof gate over the
   old 1,399-theorem tree is not promised, because that tree will have been
   replaced by campaign 1's landed tree. (Revision 1 promised the gate
   green at the landing; withdrawn.)
5. **The proof-tree retrofit** of the landed campaign-1 tree as one
   follow-on job (the deletion rule of section 5), its own proof gate and
   its own signoff, the register's pins and current-or-lagging status
   updated honestly; campaign 2 resumes on that interface and shared
   repairs are counted once.
6. **The cheap WireGuard narrowing** (section 4) as separately reviewable
   changes on the split tree, with scoped validation and explicit proof
   lag; developed alongside step 2 where convenient, never holding the
   coarse boundary hostage.

The estimate, revised (the companion's, checked against the module sizes
on e5afc0f: WireGuard 6,144 lines, the file layer 3,869, seccomp 2,786,
the routing module 1,947, the environment 2,016, the runner and dispatch
1,692):

| Work | Days |
| --- | ---: |
| The coarse mirror split (steps 1 to 4) | 5.5 to 10 |
| The cheap WireGuard narrowing (step 6) | 1 to 3 |
| Campaign 1's landed tree retrofitted (step 5; 7,405 theorems today, growing until it lands) | 5 to 10 |
| Campaign 2's own additions on resumption (about 1,500 theorems today) | 2 to 5 |

These are planning allowances, not measured durations; re-estimated after
the first complete build and replay measurements. Revision 1's ten days
with a green gate is withdrawn.

## 8. Risks

1. **A local action that actually needs an excluded store.** The matrix
   and the reading of section 1 show none between the WireGuard, file-layer
   and seccomp stores; the task and signal coupling that revision 1 would
   have hit with certainty is designed in through `TaskM`. If one appears,
   the split stops at it and reports: it is a cross-component call this
   note does not provide for.
2. **Narrowing that changes failure or record order.** A narrowed leaf
   whose extraction moved an existence check or a record read would return
   a different error on a malformed state or stream; the adapter rules of
   section 4 forbid it, and the model-replay tests and the recorded-trace
   replay catch it. Such a leaf stays `WG.M`.
3. **A real C path that needs new semantics** to express at the narrower
   type: report, not build.
4. **Elaboration and runtime cost of the lifts**, measured after the real
   lifts exist (step 3), build time separately from replay time; a
   material unexplained regression on a representative path is a stop.
5. **The `Logged` layer and the product-level observers** may carry more
   cross-subsystem content than the lexical counts suggest; the landed
   campaign-1 tree is the instance that shows it, in step 5.
6. **The seccomp child:** one optional record under `TaskRef.child` in the
   shared store, created and dropped by the environment through the
   product; the `test_model_replay` tests cover the probe and wait paths
   and must stay green.

## 9. What this stream does not do

No footprint invariants; no frame generator; no lenses or effect classes
beyond the shared task services; no change to the trace format, the
records, the kernel, the harness or the check rules; no change to any
theorem's proposition beyond its state type and execution tuple; no
whole-of-Linux state design.

## 10. Review dispositions (Codex#4's review of revision 1)

1. **The task and signal boundary needs composition inside mirror
   functions (high).** Fixed. The three id-keyed task tables in sibling
   worlds are withdrawn; one shared `TaskWorld` under `TaskM`, with `FS.M`
   and `Seccomp.M` stacked on it, so `pipeWrite`'s SIGPIPE, `fput`'s task
   tests and the filter's `forceSigSeccomp` typecheck at the C's call
   sites; `sigsys` stays with the signal state; `getFiles` keeps selecting
   `.task`; child creation and drop keep one optional record. The
   orchestration in `Seccomp/Syscalls.lean` (the child probe, `trapReturn`)
   is named as product-level. Checked by the companion's fragment on this
   head (section 3). The composer exception is put to the user (section
   11), since it touches their formulation.
2. **The probe reproduces its numbers but does not justify the dependency
   and narrowing claims (high).** Fixed in part, answered in part. The four
   parser errors are repaired (shorthand `with` fields; "touched" not
   "reads"; the signature cut at the first `:=` outside brackets, so
   `armTimer` is monadic; container method names excluded from call
   edges, so `setPeer` no longer acquires `allowedips`), the walk extended
   to the routing module and the kernel helpers, and every output labelled
   as lexical candidates. The matrix remains a candidate finder, as the
   review says; the absence of cross-store access is established by
   reading (section 1's first bullet), and the 59-leaf figure is replaced
   by section 4's finite list followed by hand. The "53 five or six" slip
   is corrected (the figure was 29).
3. **The eight WireGuard groups have no state representation or
   sufficient signatures (high).** Fixed. The eight parallel sub-records
   are withdrawn; section 4 defines the components over existing owners
   with one adapter each, lists the functions each narrows, and keeps
   `indexLookup`, `armTimer`, `delTimer`, the peer acquisition and the
   sends over `WG.M`, with the reasons the review gave (the store-back and
   the strong reference; the peer-embedded timers; `armTimer`'s record
   order). Routing is a component with no dependence on `WG.Device`; the
   device-removal lifetimes are listed as preserved.
4. **Ambient services and the performance experiment need a more precise
   boundary (medium).** Fixed. `armRecords` stays ambient; `recordQueued`
   and `peekQueuedUnit` stay `AmbientM`; `retirePeerUnits` and
   `retireDeviceUnits` become `WG.M`; the non-exclusive writers of `steps`
   are named and stay explicit operations; the listeners and inbox are
   mutable queues in `EnvWorld`; the cost measurement moves to after the
   real lifts exist, build time separate from replay time.
5. **Delete structural frames but retain ambient parameters and
   product-level execution claims (medium).** Fixed. Section 5 defines the
   local contract over the actual execution tuple, keeps campaign 2's
   success, existence and exact-error distinctions, keeps the logged
   runner and the observers over the product, proves the lift and observer
   bridge once, and states that deletion is justified by the type's
   guarantee and never by a theorem ceasing to compile; the lexical counts
   are candidates, not savings.
6. **The staging and the ten-day estimate are inconsistent with the
   required campaign order (high).** Fixed. The types-only first commit is
   withdrawn (it cannot compile without wrappers); the coarse cutover is
   one connected migration; the mirror lands with reported proof lag under
   the standing rule and the landed campaign-1 tree is the retrofit
   baseline, as its own job with its own gate and signoff; the estimate is
   the companion's, with the proof work budgeted against the trees as they
   stand today (7,405 and 3,225 theorems), and the "103 files" slip is
   corrected (48). The review did not choose a campaign order on the
   user's behalf, and this revision keeps the recorded one.

Provenance: the review and the companion proposal were produced by
Codex#4 on 2026-10-15 (`task/review-state-split`, 7b70875 and 64352f9);
revision 2 is by the coordinator's fork.

## 11. What revision 2 changes against revision 1, and what is put to the user

Unchanged: the user's four recorded decisions and their reasoning; the
coarse WireGuard boundary; routing as its own component inside `WGWorld`;
the nested ambient monad and the runner's lifts; the deletion of the
structural frame layer; no wrappers and no equivalence lemmas; the
campaigns' order.

Changed, as the coordinator's details corrected:
1. The task store is one shared `TaskWorld` (task, child, current) under
   `TaskM`; the three id-keyed tables in sibling worlds, and the separate
   lifecycle world, are withdrawn.
2. `FS.M` and `Seccomp.M` are stacked on `TaskM`, not on `AmbientM`;
   `sigsys` and `current` are task state, not seccomp's.
3. The within-WireGuard narrowing is a finite list of components over
   existing owners with one adapter each (section 4), not eight parallel
   stores and 59 leaves found by compiler errors; `indexLookup`,
   `armTimer`, `delTimer` stay `WG.M`.
4. `armRecords` stays ambient; `retirePeerUnits`/`retireDeviceUnits` are
   WireGuard operations; the fixture's queues are a mutable `EnvWorld`.
5. No types-only first commit; the coarse cutover is one connected
   migration.
6. The mirror lands with reported proof lag; the retrofit baseline is the
   landed campaign-1 tree; the proof-tree integration has its own gate and
   signoff.
7. Behaviour preservation is shown by replaying the same recorded inputs
   on baseline and candidate, not by identical totals of two live runs.
8. The estimate is 5.5 to 10 days for the coarse split, 1 to 3 for the
   narrowing, 5 to 10 and 2 to 5 for the two proof retrofits.
9. The probe is repaired, extended and labelled as lexical candidates.
10. The stop risk is restated: a local action needing an excluded store,
    narrowing that changes failure or record order, a C path needing new
    semantics, a material lift cost; the task coupling is no longer one.

**Put to the user** (recorded as [AGENT proposal, from Codex#4's review] in
`docs/decisions.md`, pending):
- The exception to "the runner is the only composer": subsystem operations
  may call the shared task and signal services at the C's existing call
  sites; the runner alone assembles the product and orchestrates across
  independent stores.
- The mirror landing with reported proof lag and the landed campaign-1
  tree as the retrofit baseline, rather than a green proof gate at the
  landing.

## 12. Phase 1 as built, and the brief for phase 2 (2026-10-16)

Phase 1 is on `task/state-split` (three commits after revision 2 and the
user's decisions): the ambient layer, the shared task store, and seccomp
converted end to end. It builds, the fast tier passes, and the executable
is the same program (section 6's preservation check, the recorded inputs of
the seccomp suites replayed through the e5afc0f binary and the phase-1
binary, identical). What the two phase-2 forks inherit:

- **The shape.** `AmbientM := StateT Ambient (Except Stop)`;
  `TaskM := StateT TaskWorld AmbientM`; `Seccomp.M := StateT SeccompWorld
  TaskM`; the runner's `M := StateT World (Except Stop)` with
  `liftAmbient`, `liftTask`, `liftSeccomp` and a `MonadLift` instance for
  each (the `AmbientM` one at high priority, so the unconverted modules'
  primitive calls lift directly). `World` is `{ ambient, tasks, seccomp,
  k, ...the fields not yet moved }`; `Kernel` holds the file-layer and
  WireGuard fields only.
- **The primitives are polymorphic.** `branch`, `branchCmp`, `hidden`, the
  cut and allocation consumers, the dispatch-order reads, `envOk`,
  `unsupported`, `invariant`, `budgetExhausted`, the refcount helpers:
  `[Monad m] [MonadLiftT AmbientM m]`, `@[inline]` wrappers over
  `AmbientM.<name>`. The task services `getTask`, `modifyTask`,
  `getCurrent`, `getFiles`, `modifyFiles`, `modifyFdt` are
  `[MonadLiftT TaskM m]`. Reads and writes of the moved state go through
  `getAmbient`/`modifyAmbient` and `getTasks`/`modifyTasks`; a direct
  `(← get).hidden` no longer typechecks, which is how the compiler finds
  every site.
- **The namespace trick.** `abbrev Seccomp.M` lives in `Leanux.Kernel.Defs`;
  inside `namespace Leanux.Seccomp` the bare name `M` resolves to it, so a
  module's signatures move as one. The same works for `FS.M` and `WG.M`.
  A function that must stay over the product writes `_root_.Leanux.M`.
- **The runner lifts explicitly** at the syscall dispatch's match arms
  (`liftSeccomp (Seccomp.sysSeccompProbeChild ..)`), because a match arm is
  not a `do` element and gets no automatic lift; inside `do` blocks a
  `TaskM` or `AmbientM` call auto-lifts through `MonadLiftT`.
- **The checks.** `lake build Leanux leanux-model`; the five-module unit
  line; the subsystem's suites on s5; and the preservation script
  (`.tmp/preserve.py` in the phase-1 worktree, ephemeral: for each chunk of
  a check run it replays `inputs.jsonl` through the baseline binary from a
  detached worktree at e5afc0f and the candidate binary and compares
  stdout, stderr and exit code, and the run's own `model.stdout`).
- **Measured cost.** Clean build and the model-replay tests before and
  after phase 1 are in the phase-1 report; the lifts are inlined and the
  replay tests did not move.

**Fork FS** (`FSWorld`, section 2): the 31 file-layer `Kernel` fields plus
`userOut`, `userFds`; `abbrev FS.M := StateT FSWorld TaskM`; the stores'
accessors in `Kernel/Defs.lean` (`getFile` .. `setFdtCloexec`) move to the
file layer over `FS.M` (the task's file table stays in `TaskM`); the
syscalls `pipe2`, `read`, `write`, `close`, `dup`, `dup3`, `fcntl`,
`eventfd2`, `epoll_create1`, `epoll_ctl`, `epoll_wait` and the task-work
run are lifted with `liftFS` at the dispatch; `pipeWrite`'s `sendSig` and
`fput`'s task test auto-lift through `TaskM`. Validation: the fast tier,
the `pipes`, `pipes-generated`, `epoll` and `epoll-generated` suites on s5,
the preservation script over those runs.

**Fork WG** (`WGWorld`, section 2, with the routing component of section 4):
the WireGuard `Kernel` fields (`wg`, the two netlink sockets, the two
counters, `netIfindexNext`, `ratelimiter`, `fib4`, `fib4C`, `timerClk`,
`timerEnqueues`) and the WireGuard environment fields of `World` (`sent`,
`netRxRaised`, `queuedThisCall`, `timerUnits`, `jiffiesLast`,
`timerPassStep`, `dstCacheRecords`, `lastUnderLoad`, the routing fields
`addrs4`, `addrPlens4`, `addrs6`, `defaultRoute6`, `ipv6Gen`,
`neighbours`, `fibCreatorNs`, the fixture inputs `portBound`,
`fixtureNetDevices`); `abbrev WG.M := StateT WGWorld AmbientM`; lane C's
module over `StateT Net.Routing AmbientM` inside `WGWorld.routing` with
`liftRouting`; `retirePeerUnits`, `retireDeviceUnits`, `workerIter` and
`workerLoop` over `WG.M`; the environment stays over the product and lifts
whole worker bodies (`runWorker w (liftWG body)`) and the WireGuard
syscalls at the dispatch; what remains of `World` after it is `EnvWorld`
(the listeners and inbox, the foreign-creator fields, the NAPI placement,
`routesPending`, `routes`, `lastAdvance`, `hiddenAhead`, `mtu`), and `k`
disappears. The adapter rules of section 4 bind every narrowing a fork
attempts inside WireGuard; the component list there is the finite list.
Validation: the fast tier, the `wireguard`, `wireguard-generated` and
`w7-tier` suites on s5 (the D3 traces included), the preservation script.

The two forks edit `Kernel/Defs.lean`'s `Kernel` and `World` on disjoint
fields; FS lands first on this branch and WG rebases onto it, so the
`Kernel` structure is deleted by the WG fork. Phase 3 is the proof tree:
`main`'s tree retyped by deletion and retyping (what phase 1 breaks is in
its report), then the landed campaign-1 tree as its own job.

## 13. Phase 2, the file layer, as built (2026-10-16)

On `task/split-fs` from 909c174, one mirror commit (a5d4c6d). `FSWorld`
holds the 31 file-layer `Kernel` fields with their docstrings and defaults
and the two user-memory outputs (`userOut`, `userFds`) that were `World`'s;
`FS.M := StateT FSWorld TaskM`; `liftFS` runs a file-layer computation on
`World.fs`, `World.tasks` and `World.ambient` and writes the three back
once, with a `MonadLift FS.M M` instance. The stores' accessors (`getFile`
.. `setFdtCloexec`, the bounds-checked descriptor-table reads) moved from
`Kernel/Defs.lean` to `Leanux/FS/Stores.lean` over `FS.M`, unchanged but
for the monad; the three file-layer modules that imported `Kernel.Defs`
import it instead.

One departure from section 12's brief: the file layer's modules live in
`namespace Leanux`, not `Leanux.FS`, so the namespace trick does not apply
and the signatures name `FS.M` explicitly (174 of them, a mechanical
retyping of every `M` in `Leanux/FS`; the file has no other use of the
name). Renaming the modules into `Leanux.FS` would have moved every
definition's name, which the proof tree and the dispatch use; the type is
what the split needs, not the namespace. `getK`/`modifyK` in the file layer
became `get`/`modify` over `FSWorld`, whose field names are the former
`Kernel`'s, so the lambdas did not change.

The runner: the dispatch lifts the eleven file-layer system calls with
`liftFS`; `taskWorkRun` is `FS.M` (its task reads through `TaskM`, its
`fputFinal` the file layer's); `netnsClose`'s four closes and task-work
runs, the `wg_advance` arm's `fdget`/`fdput` and `rtnetlinkRequest`'s
temporary descriptor auto-lift inside their `do` blocks, `rtnetlinkRequest`
reading and writing `World.fs.nextFile` directly as it did `Kernel`'s; the
per-call reset clears `World.fs.userOut`/`userFds`. `Runner.initialFS`
builds the stores `initialKernel` held (the fixture's files over the
reserved descriptors, `nrFiles`, `maxFiles`, the pipe sysctls, `root_user`,
the epoll fixture facts); `initialKernel` keeps `wg`, `netIfindexNext` and
`ratelimiter`. The environment model touches no file-layer state (its
child creation copies the task record, `TaskM`, as phase 1 left it).

`Kernel` after this phase, for the WireGuard fork to dissolve: `wg`,
`nlSock7`, `nlSock8`, `peerCounter`, `keypairCounter`, `netIfindexNext`,
`fib4`, `fib4C`, `ratelimiter`, `timerClk`, `timerEnqueues`. `World` after
it: `ambient`, `tasks`, `seccomp`, `k`, `fs`, and the environment and
WireGuard fields the WireGuard fork moves.

Checks: `lake build Leanux leanux-model` green; the five-module unit line
131 OK (1 skipped); on the s5 pair at 16 slots, `pipes` and
`pipes-generated` 224 traces, 5509 operations, 224 agreements, and `epoll`
and `epoll-generated` 247 traces, 6162 operations, 247 agreements, no
splits, no retries; the preservation script over both runs' chunk inputs
(the e5afc0f binary against this one): 9 of 9 and 9 of 9 chunks identical
in stdout, stderr and exit code, and equal to the runs' recorded output.
Clean build 73.6 s wall / 181 s user against phase 1's 74 s / 185 s; the 27
model-replay tests 1.14 s against 1.11 s: no cost. Beyond the brief, the
other subsystems' suites on the same tree, since the shared paths changed
(`rtnetlinkRequest`, the per-call reset, the dispatch): `seccomp` and
`seccomp-generated` 267 traces, 267 agreements; `wireguard`,
`wireguard-generated`, `w7-tier` and `routing` 488 traces, 488 agreements,
no retries; the preservation script over both: 288 of 288 and 154 of 154
chunks identical.

What this phase breaks in `main`'s proof tree (not edited; by grep): 7
sites in 3 files project `World.userOut`/`userFds`; 5 sites in 2 files
read a file-layer `Kernel` field; 9 files name a file-layer function whose
type is now `FS.M` (`Keypairs/Frames/{Pipe,FS,Kernel,EventpollCalls,
FSBase,Wait,PipeRead}.lean`, `Logged/Syscalls.lean`,
`Keypairs/Evolution/Syscalls.lean`), retyped or deleted in phase 3.
