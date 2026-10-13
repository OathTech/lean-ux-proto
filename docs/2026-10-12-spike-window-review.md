# Independent review of the window-proof spike (`spike/window` at ed069ba)

[AGENT, independent review 2026-10-12]. Reviewed against
[the charter](2026-10-12-charter-window-proof.md), the spike's report
(`docs/2026-10-xx-spike-window.md` on the branch) and the code under
`Leanux/Spikes/`, with every claim rebuilt or re-derived here. Nothing on the
spike branch was edited. The user decides whether proofs land on `main`; this
review is the evidence for that decision and recommends nothing on the rule.

## Verdict

The claim holds as stated by the spike: S1, S2 and S3 are theorems over the
unchanged mirror at fb2c29c (which is also the mirror on `main` 5b07c8e; the
six commits since the pin touch no file under `Leanux/`), with no admission,
no added axiom and no unsafe or native shortcut, and the eight terminal
statements depend only on `propext`, `Classical.choice` and `Quot.sound`.
The wording deltas keep the charter's meaning: S1 is the no-replay statement
over lifetime identities, which is the only correct reading once a
device-local slot can be reused; S2 is the C's rule, read against
`receive.c:295-331` line by line; S3 permits allocation and deletion, which
the receive path legitimately performs. One presentation gap: the charter's
receive-path clause of S3 ("only the keypair the packet names changes") is
proved, but under the name `syscallLogged_evolves`, not in the exported `S3`.
The result is tied to the pinned mirror: the representation batch on
`task/int-r` changes 29 definitions the spike references, in 17 of its 45
files, so landing it means maintaining it.

## 1. The mirror is unchanged

`git diff --stat fb2c29c..ed069ba -- . ':!Leanux/Spikes'`:

```
 docs/2026-10-xx-spike-window.md | 563 ++++++++++++++++++++++++++++++++++++++++
 lakefile.toml                   |   6 +-
```

The lakefile change adds a `WindowSpike` library rooted at
`Leanux.Spikes.Axioms` and makes it a default target; `moreLeanArgs`, the
`Leanux` library and the executable are untouched. No test file changed, so
the "76 unit tests" are the Python fast tier running on unchanged code; I did
not re-run them, since they say nothing about the theorems. Thirty commits,
all on 2026-10-12, each a proved checkpoint as the charter asked.

## 2. The build

From an empty `.lake` in the spike worktree, `capped -- scripts/in-bundle lake build`:

| Jobs | Wall | Peak resident | Exit |
| --- | --- | --- | --- |
| 92 | 3 min 00 s | 2.49 GB | 0 |

487 warnings: 486 are the `mvcgen` tactic's "experimental and still under
development" notice, three per use site in the spike, and one is the mirror's
own `String.mk` deprecation at `Leanux/Env.lean:622`, present on `main` too.
Twenty-two spike files raise `maxHeartbeats` (200,000 to 2,000,000); that is
elaboration budget, not a soundness concern, but it marks the proofs that
will be slowest to repair.

## 3. Admissions and axioms

Grep of `Leanux/Spikes/*.lean` for `sorry`, `admit`, `axiom`, `native_decide`,
`unsafe`, `implemented_by`, `extern`, `partial`, `opaque`: no hit outside a
comment ("Keep Erases opaque" in `RxPoll.lean:56`, prose). `decide` appears
four times, each on `0 < 128`. `maxRecDepth` is never set.

`Leanux/Spikes/Axioms.lean` is 1,275 lines: imports and 1,180 `#print axioms`
commands, nothing else. That is what "1,180 axiom audits" counts. Those
commands only print; a `sorryAx` would not fail the build, so the check is
reading the output. The build log here contains 1,172 lines "depends on
axioms" and 8 "does not depend on any axioms", 1,180 in all, distributed:

```
    894 [propext, Classical.choice, Quot.sound]
     26 [propext, Quot.sound]
     15 [propext]
    237 [propext,                 (wrapped onto a second line; same set)
```

No line mentions `sorryAx`. Independently, from a scratch file importing only
`Leanux.Spikes.Statements`:

```
'Leanux.Spikes.S1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.S3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.S3_nonreceive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.S3_validator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.S3_surviving' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.Window.S2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.Window.S2_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.Window.S2_update' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 4. The statements against the charter

### S1

Charter: for every trace and record stream the runner accepts
(`Leanux.Runner.executeTrace`), in the execution's sequence of accepted data
packets no two share (keypair, counter).

Proved (`Statements.lean:14`):

```
S1 : ∀ (trace : Runner.Trace) (placeholders : Bool) (json : Json),
  Runner.executeTrace trace placeholders = .ok json →
    ∃ history, (Ghost.executeTraceLogged trace placeholders).run [] = .ok (json, history) ∧
      history.Nodup
```

with `History := List AcceptedEvent`, `AcceptedEvent := {keypair : Nat
(the lifetime identity, Keypair.internalId), nonce : Nat}`
(`Ghost.lean:9-15`). `Nodup` on that list is exactly "no two events share
(lifetime, nonce)". The record stream is inside `Trace` (`trace.hidden`,
`trace.steer`, the arm and dst-cache records), and `placeholders` covers the
placeholder mode, so the quantification is the charter's.

What the history contains, and why it is complete:

- `counterLogged` runs the real `counterValidate` and appends one event iff it
  returned true (`counterLogged_run`, `Ghost.lean:147`). The event is recorded
  at the validator, so it is a superset of delivered packets (a packet can be
  dropped after its counter is consumed, `RxData.lean:354-361`); `Nodup` of
  the superset implies `Nodup` of the delivered subsequence. Stronger than the
  wording, not weaker.
- `executeTraceLogged` is a copy of `executeTrace` with `syscallLogged` in
  place of `syscall`, and `executeTraceLogged_erases` proves the copy returns
  the same JSON or the same indexed failure for every input
  (`GhostRunner.lean:88`). Erasure alone would also accept an observer that
  logs nothing. Completeness comes from `syscallLogged_evolves`
  (`EvolutionSyscalls.lean:124`): every successful logged syscall from a state
  satisfying `Inv` produces an `Evolution` witness whose final history is the
  actual history. `Evolution` (`Lifetimes.lean:241`) has only `ordinary` steps
  (erase a slot, empty the map, allocate a fresh lifetime) and `validate`
  steps at a named slot that append `logResult`. An accepted packet sets a bit
  that was clear, so it changes a surviving cell's counter under the same
  stamp, which no `ordinary` step can express; it must be a `validate` step,
  whose event is in the witness's history, which equals the actual one. So an
  unlogged acceptance anywhere in the runner would have made
  `syscallLogged_evolves` unprovable. I confirmed separately that the pinned
  mirror has one `counterValidate` call site (`RxData.lean:354`, inside
  `rxPoll`) and that `rxPollLogged` substitutes it there.
- The initial state satisfies `Inv`: `initialKernel` creates the device with
  no keypairs (`Runner.lean:721`), `keypairCounter` 0, history `[]`
  (`inv_empty`).

Refinement, lifetime identity: `KeypairId` is a device-local map key that
device deletion and recreation can reuse; `internalId` comes from the kernel's
`keypairCounter`, which survives (`Keypair.lean:53-57`). Stating S1 over
`KeypairId` would be false for a reason that is not a replay. The refinement
preserves the meaning; it is the correct reading of "keypair".

### S2

Charter: `counterValidate kp theirs` returns true exactly when
`counter_validate` would (the four conditions), and on true the resulting
`ReplayCounter` is the C's update.

Proved (`Refinement.lean:199`):

```
Window.S2 : ∀ (w : World) (d : WG.Device) (kp : KeypairId) (k : Keypair) (nonce : Nat),
  w.k.wg = some d → d.keypairs.get? kp = some k → k.receivingCounter.backtrack.size = 128 →
    ∃ w', (counterValidate kp nonce).run w = .ok ((step k.receivingCounter nonce).1, w') ∧
      counterAt w' kp = some (step k.receivingCounter nonce).2
```

plus `S2_acceptance` (true iff `eligible` and the bit, read after the
advancing clears, is clear) and `S2_update` (the state after a true result is
`update`). `step`, `eligible`, `prepared`, `clear`, `update`, `slot`, `bit`
are 40 lines of `Window.lean`; I read them against `receive.c:295-331`:

| C | `Window.lean` |
| --- | --- |
| `counter->counter >= REJECT_AFTER_MESSAGES + 1 \|\| their_counter >= REJECT_AFTER_MESSAGES` → reject | `eligible` clauses 1 and 2 |
| `++their_counter` | `n := nonce + 1` throughout |
| `COUNTER_WINDOW_SIZE + their_counter < counter->counter` → reject | `c.counter ≤ 8128 + (nonce + 1)` (8128 = 8192 − 64) |
| `if their_counter > counter->counter`: clear words `(i + index_current) & 127` for `i` in `1..top`, `top = min(index − index_current, 128)`; counter := their_counter | `prepared`: `clear` over `List.range' 1 (min (n/64 − c.counter/64) 128)`; `update.counter = max c.counter n` |
| `!test_and_set_bit(their_counter & 63, &backtrack[index & 127])` | `fresh` reads `(prepared c n)[slot n].testBit (bit n)`; `update` sets it unconditionally, as the C does on both outcomes |

`counterValidate_execution` (`Refinement.lean:103`) proves the mirror's run
equals `cExecution`, a transcription of the mirror's body including its branch
records, and `cExecution_refines_step` projects that onto `step`. The link
from mirror to pure model is exact equality of runs, not a simulation
relation, so nothing is lost in between.

Refinements: the counter is one-based (the C increments before comparing),
the lower edge is inclusive (`<` in the C's reject test), the bit is tested
after the clears, and the "shift" is circular word clearing. All four are
what the C does; the charter's wording was looser, not different. The
`size = 128` premise states the C's array shape, which the mirror's
`Array Nat` does not enforce; the runner proof discharges it at every
reachable state (`Inv.shaped`), and every keypair is created with the
128-word default (`Keypair.lean:57`, `Types.lean:112`). Not trivially
satisfiable, not a bug exclusion.

### S3

Charter: every operation other than the data-receive path leaves every
keypair's `receivingCounter` unchanged; on the data-receive path only the
keypair the packet names changes.

Proved (`Statements.lean:76`):

```
S3 : (∀ call, NoReceiveCall call → OrdinaryAction (Leanux.syscall call)) ∧
     (∀ query nonce w w' history ok, Inv (snapshot w) history →
        (counterValidate query nonce).run w = .ok (ok, w') →
        (snapshot w').frontier = (snapshot w).frontier ∧
        ∀ other, other ≠ query → (snapshot w').slots other = (snapshot w).slots other)
```

`NoReceiveCall` excludes exactly `wgInject`, `wgFlood`, `wgBatch`
(`EvolutionSyscalls.lean:49`). `OrdinaryAction a` says every successful run
of `a` relates the before and after snapshots by `Ordinary`, whose
constructors are reflexivity, erase one slot, empty the map, allocate a fresh
lifetime at the next stamp, and composition. `Ordinary.old_slot` then gives
`S3_nonreceive`: a cell present after the call with a stamp at or below the
old frontier was present before, at the same slot, with the same counter.
A surviving keypair cannot have changed; a modification that kept the stamp
is unrepresentable, and one that changed the stamp is an allocation by
definition. `S3_surviving` restates it as `old.counter = new.counter`.

Two gaps between the charter's wording and the exported theorem:

- The runner also runs `skipAmbient` after each syscall
  (`Runner.lean:826`). It touches only `w.hidden` and `w.pendingStops`
  (`Kernel/Defs.lean:1263-1274`), never `w.k`, so the snapshot is unchanged;
  the S1 chain carries a contract for it, S3 as exported does not mention it.
- The receive-path clause. The exported second conjunct is about one
  `counterValidate` call, not about a receive syscall as a whole. The
  whole-syscall statement is `syscallLogged_evolves` (an `Evolution` witness:
  only `ordinary` steps and `validate` at the named slot), transferred to the
  original syscall by `syscallLogged_erases`. That is the charter's clause,
  allowing deletion (key confirmation in `consumeDataDone` retires an older
  keypair) and allocation. The report's table describes S3's receive clause
  as "per validator event", which undersells what was proved.

Refinement, allocation and deletion: the charter's "unchanged" is false of
the mirror for a legitimate reason (`wgDown`, `wgDelete`, netns teardown,
key rotation all remove keypairs; handshakes create them). Permitting
lifecycle effects while forbidding any change to a surviving window keeps the
meaning.

## 5. The trusted base

What carries the meaning, all stated over the mirror's own types
(`World`, `Device`, `Keypair`, `ReplayCounter`, `counterValidate`,
`executeTrace`, `syscall`, the `TreeMap` of keypairs and `keypairCounter`):

| Definition | File | Lines | Role |
| --- | --- | --- | --- |
| `slot`, `bit`, `clear`, `prepared`, `eligible`, `fresh`, `update`, `step`, `Remembers`, `accepted` | `Window.lean` | ~45 | the C's rule, by hand; checked above |
| `record`, `clearRecords`, `cExecution`, `counterAt`, `store` | `Refinement.lean` | ~45 | the mirror's validator body as a function; tied to the real one by `counterValidate_execution` |
| `AcceptedEvent`, `History`, `Erases`, `emit`, `counterLogged` | `Ghost.lean` | ~30 | what an event is; what "erases" means |
| `Cell`, `Snapshot`, `cell`, `snapshot`, `put`/`empty`/`fresh`, `Inv`, `validate`, `logResult`, `Ordinary`, `Evolution` | `Lifetimes.lean` | ~80 | the projection of `w.k.wg` and `keypairCounter`; the invariant; the step relations |
| `OrdinaryAction`, `SameSnapshot` | `Ordinary.lean` | ~8 | framing over successful runs |
| `Evolves` | `EvolutionRules.lean` | 4 | the observer contract |
| `NoReceiveCall` | `EvolutionSyscalls.lean` | 3 | the receive classification |
| `Hoare`, `Protected` | `Framing.lean` | ~20 | the operational Hoare predicate |

About 235 lines of definitions. Everything else is proof. Two kinds of
proof-side copy exist and are each checked against the original by a
theorem: observers (`rxPollLogged`, `syscallLogged`, `dispatchLogged`,
`executeTraceLogged`) by erasure, and the allocation helper by
`allocationOutcome_eq : allocationOutcome s = hiddenAlloc s := rfl`
(`Allocation.lean:63`), a definitional check. The one copy that is a
re-encoding rather than a copy is `step`, the C's rule, which is the point of
S2 and is reviewed in section 4.

`snapshot` covers one device (`w.k.wg : Option Device`), which is the
mirror's shape; a keypair held in a worker's closure and written back would
show as a surviving-cell change and would have blocked the ordinary framing,
which closed for every worker.

## 6. Rule Zero

No counterexample was found, and none was searched for separately: the
search was the proofs themselves. S1 is proved over the mirror's actual
validator and update, so a replay the mirror admitted would have blocked
`Inv.validate` or `accepted_nodup`; S2 is exact equality with a line-by-line
reading of the C. No statement is proved under a named premise that excludes
a trigger; the only premises are the array shape (section 4) and `Inv` at
reachable states, which the runner proof establishes. So "no counterexample"
is evidence for S1-S3 over the mirror, not absence of search, within what
S1-S3 say. What the spike does not say: anything about the C beyond the
mirror's fidelity to it, which is the differential check's claim and was
explicitly out of the charter's scope; and anything about properties the
charter did not pose (key lifetimes, the next challenge). The two boundary
nuances (one-based counter, inclusive lower edge) are the C's and RFC 6479's,
not disagreements with intent.

## 7. Rebase cost onto the current mirror

`main`'s `Leanux/` equals the pin. The representation batch on `task/int-r`
(26 commits, 19 files, +1,556/−666 under `Leanux/`) changes 116 definitions,
of which 29 are referenced by the spike:

```
dispatch deliverInner txWorker queuedWork enqueuePerPeerTx encryptWorker
createDataDone runWorker runCryptWorkers discardFloodRecords decryptWorker
condResched wgGetDevice SWITCH_DEPTH schedule MAX_QUEUED_PACKETS initialKernel
handshakeReceiveWorker enqueuePerPeerRx runDecryptWorker runDecryptAt
napiSoftirq napiIrqExit getPeerDump getAllowedips enqueuePerDeviceAndPeerRx
enqueuePerDeviceAndPeer dumpSize createData
```

Unchanged on `task/int-r`: `counterValidate`, `ReplayCounter`, `Keypair`,
`internalId`, `keypairCounter`, `keypairCreate`, `syscall`'s shape. So the
core (`Window`, `Refinement`, `Ghost`, `Lifetimes`, `Ordinary`,
`OrdinaryHot`, `MirrorCalls`, `FramingWP`, the pipe and filesystem framing,
28 of 45 files, ~6,500 lines including the 1,275-line axiom list) survives
untouched; `LifetimeMirror` is touched only by `initialKernel`'s new
parameter.

Affected, by number of changed names referenced: `GhostScheduler` (13 names,
170 lines), `GhostWorkers` (10, 164), `FrameEnvWorkers` (10, 131),
`GhostOperations` (7, 176), `FrameWGMore` (7, 416), `EvolutionScheduler`
(4, 117), `FrameWGTransitions` (3, 366), then `GhostRunner`, `FrameEnvLeaves`,
`FrameEnv`, `EvolutionSyscalls`, `EvolutionOperations` (2 each), and
`RxPoll`, `LifetimeMirror`, `GhostSyscalls`, `FrameKernel`, `Allocation`
(1 each): 17 files, ~2,850 lines. Three of the changes are structural rather
than renames:

1. The worker loops. `decryptWorker`'s fuel-bounded `for` becomes
   `decryptStep`/`decryptIter` under `workerIter` and the scheduler loop
   (`workerLoop`, suspended activations); the same for the other workers.
   The spike's fuel inductions in `GhostScheduler` and `EvolutionScheduler`
   need a new induction principle over the scheduler loop, and the ordinary
   contracts for `runWorker`/`runCryptWorkers`/`condResched` are rewritten.
2. The packet store. `rxPoll` and the enqueue functions take packet ids
   (`getRxSkb`, `setRxSkb`, `freeRxSkb`) and the decrypt queue is a
   `PtrRing` with cursors; `rxPollLogged` is re-copied and its erasure
   re-proved (mechanical if the control flow is the same), and the
   `Device` record gains fields the snapshot ignores (no change to
   `snapshot` needed, since it projects only the keypair map).
3. New syscalls and the stepped dump: `wgGetStart`/`wgGetRecv`,
   `initialKernel`'s `stepped` parameter, and +491 lines in
   `NetlinkDump.lean` need new ordinary contracts and the `executeTraceLogged`
   copy re-synced.

Estimate: 4 to 8 agent-hours in the spike's own multi-agent setup, of which
more than half is item 1, since the scheduler loop replaces the pattern the
hardest proofs relied on; the rest is re-copying and re-running the framing
tactics. The spike produced its 9,400 lines in about four elapsed hours with
three subagents, so one working day of that setup is the ceiling if the loop
needs a new invariant; a human doing the same would need days. This cost
recurs with every mirror change that touches a framed function, which the
representation batch shows is most of them.

## 8. The decision, framed

Landing the proofs on `main` would need:

- a tree exempt from the no-theorems rule (`Leanux/Spikes/` or a renamed
  proofs library), which changes a standing rule in `AGENTS.md` and
  `docs/2026-09-29-way-forward.md`; the user's call;
- a gate for it on the trust surface: the build plus an axiom check that
  fails on any axiom beyond the three or on `sorryAx` for the terminal
  statements (`#print axioms` alone does not fail), about 3 minutes and
  2.5 GB on top of the fast tier, so it would become the slowest part of the
  per-commit tier;
- a maintenance rule: either every mirror change repairs the proofs before
  merge (the representation batch would owe ~2,850 lines of repair now,
  section 7), or the proofs are pinned to a mirror commit and allowed to lag,
  in which case the gate protects nothing on `main`'s mirror and the result
  is a reference, not a property of the current mirror;
- the altitude review's ruling on the report's six mirror-shape findings,
  which would cut future repair cost but each touch the mirror's shape.

Keeping it on the branch costs nothing, keeps a valid result for the mirror
as it is on `main` today, and loses that validity the moment the
representation batch lands. The charter's value was twofold, the theorem and
the findings list; the findings list is realised either way, and the proof
architecture is reusable as a pattern for the key-lifetime challenge whether
or not this instance is maintained.

## Reproduce

```sh
cd .worktrees/spike-window
capped -- scripts/in-bundle lake build                       # 92 jobs
git diff --stat fb2c29c..ed069ba -- . ':!Leanux/Spikes'       # docs and lakefile only
grep -c 'depends on axioms\|does not depend on any axioms' <build log>   # 1180
grep -c sorryAx <build log>                                   # 0
```

Scratch axiom check: a file importing `Leanux.Spikes.Statements` with
`#print axioms` on the eight statements of section 3, run with
`capped -- scripts/in-bundle lake env lean <file>`.

---

# Part 2: the port to the representation batch (`spike/window-r` at b09f065)

[AGENT, independent review 2026-10-13]. Codex#2 carried the spike onto
`main` ef7c535 (the representation batch) as one commit, b09f065, at
01:10 UTC. The user relayed its claims; none was taken on trust. Everything
below was rebuilt or re-derived in `.worktrees/spike-window-r` (nothing
committed there) and compared against part 1.

## Verdict

It lands clean as a proof artifact: the mirror is byte-identical to ef7c535,
the build passes from an empty `.lake` under `capped`, no admission or unsafe
construct exists, and all ten terminal statements depend only on `propext`,
`Classical.choice` and `Quot.sound`. The eight statements of part 1 have the
same signatures; two new exports, `S3_syscall` and `S3_syscall_ambient`, state
the charter's whole-syscall S3 directly over the original action and close the
presentation gap part 1 reported. One corollary narrowed honestly: the list of
syscalls proved receive-free shrank from "all but three" to "all but nine",
because the new mirror runs the scheduler inside send and timer waits, as the
kernel does; the spike shows this with an executable witness rather than
hiding it behind a premise. The theorems are still what the charter wanted,
and the whole-syscall form is closer to its wording than the first spike was.
One correction to part 1: the spike's internal reviewer is right that my
completeness argument via `Evolves` was too strong; completeness rests on
source-call coverage, which I re-verified on the new mirror (section 3).
Before landing, the lakefile's default-target change should be reversed
(section 6), and the spike's internal review file should be renamed or
folded into the report so that it is not mistaken for this one.

## 1. The mirror is unchanged

`git diff --stat ef7c535..b09f065 -- . ':!Leanux/Spikes'`:

```
 docs/2026-10-13-spike-window-r-review.md    | 167 +++   (the spike's internal subagent review)
 docs/2026-10-13-window-proof-conventions.md |  62 +++
 docs/2026-10-xx-spike-window.md             | 260 +++
 lakefile.toml                               |   6 +-    (same six lines as part 1)
```

Nothing under `Leanux/` outside `Leanux/Spikes/`; no Python, test or
harness file. ef7c535 is an ancestor of b09f065 (one commit, 2,467 insertions
and 1,736 deletions across 29 spike files, plus the new
`PortCounterexample.lean`, 46 files in all, 10,112 lines).

## 2. Build and axioms

From an empty `.lake`, `capped -- scripts/in-bundle lake build`:

| | Part 1 (ed069ba) | Part 2 (b09f065) |
| --- | --- | --- |
| Jobs | 92 | 94 |
| Wall | 3 min 00 s | 3 min 19 s |
| Peak resident | 2.49 GB | 3.11 GB |
| Exit | 0 | 0 |

Per-module times summed from the log: 24 spike modules 34 s, 44 mirror
modules 41 s; the slowest spike modules are `GhostRunner` (8.4 s),
`EvolutionSyscalls` (4.9 s) and `GhostScheduler` (2.4 s), all at the tail of
the dependency chain. 505 warnings: 500 `mvcgen` notices, the mirror's own
`String.mk` deprecation (`Env.lean:621`) and a copy of it in
`GhostOperations.lean:166` (a copied original body), and three unused
`simp` arguments (`RxPoll.lean:85`, `FrameEnvLeaves.lean:115`). Cosmetic.

Grep of `Leanux/Spikes/*.lean` for `sorry`, `admit`, `axiom`,
`native_decide`, `unsafe`, `implemented_by`, `extern`, `partial`, `opaque`,
`maxRecDepth`: no hit outside the one prose comment. `decide` only on
`0 < 128`. 25 files raise `maxHeartbeats`.

`Axioms.lean` now holds 1,240 `#print axioms` commands, no duplicates. The
build log has 1,232 "depends on axioms" and 8 "does not depend on any
axioms" lines, 1,240 in all, none with `sorryAx`:

```
    938 [propext, Classical.choice, Quot.sound]
     26 [propext, Quot.sound]
     15 [propext]
    253 [propext,                 (wrapped; same set)
```

What 1,240 counts: comparing the two print lists by name, 1,141 names are
retained from part 1's 1,180, 39 removed, 99 added, exactly the spike's
accounting. The removed names are the six old worker and scheduler erasure
pairs (`encryptWorkerLogged`, `txWorkerLogged`, `decryptWorkerLogged`,
`condReschedLogged`, `runDecryptAtLogged`, `runDecryptWorkerLogged`), the
ordinary contracts for `afterAdvance`, `afterXmit`, `encryptWorker`,
`idleTimers`, `observe`, `runCryptWorkers`, `runTimers`, `txWorker`,
`queuedWork`, `runSendWorkers` and `condResched` (no longer true on the new
mirror, see section 3), and the two `dumpSize` contracts. The added names are
the Step/Iter/Loop and activation observers, the packet-store and stepped-dump
snapshot contracts, and the five new statements. The source has 1,215
`theorem`s and 1,314 top-level declarations; the prints cover every theorem
and the `_spec` definitions.

From a scratch file importing `Statements` and `PortCounterexample`:

```
'Leanux.Spikes.S1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.S3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.S3_nonreceive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.S3_validator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.S3_surviving' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.Window.S2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.Window.S2_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.Window.S2_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.S3_syscall' depends on axioms: [propext, Classical.choice, Quot.sound]
'Leanux.Spikes.S3_syscall_ambient' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The "85 unit tests" are the Python fast tier on unchanged code; not re-run.

## 3. The statements against part 1

The core is byte-identical: `Window`, `Refinement`, `Ghost`, `Lifetimes`,
`Ordinary`, `OrdinaryHot`, `MirrorCalls`, `Framing`, `FramingWP`,
`EvolutionRules` have no diff against ed069ba (`LifetimeMirror` changed two
lines for `initialKernel`'s new parameter). So `step`, `snapshot`, `Inv`,
`Ordinary`, `Evolution`, `Erases` and `Evolves` mean what part 1 reviewed.

The eight signatures. `S1`, `S3_nonreceive`, `S3_validator`, `S3_surviving`,
`S3`, `Window.S2`, `S2_acceptance`, `S2_update`: textually identical to part
1 (the only diff in `Statements.lean` before the additions is `S1`'s
docstring, "every committed true original validator return"). One definition
they depend on changed:

```lean
-- part 1                                         -- part 2
def NoReceiveCall : Syscall → Prop                def NoReceiveCall : Syscall → Prop
  | .wgInject .. | .wgFlood .. | .wgBatch ..        | .wgInject .. | .wgFlood .. | .wgBatch .. | .wgObserve
      => False                                       | .wgSet .. | .wgUp | .wgXmit .. | .wgAdvance .. => False
  | _ => True                                       | _ => True
```

plus a new `NoReceiveDispatch` excluding only `wgInject`, `wgFlood`,
`wgBatch`, `wgObserve` (the four dispatch bodies that reach the poll). So
`S3`'s first conjunct and `S3_nonreceive`/`S3_surviving` now cover fewer
syscalls. That is the narrowing; whether it is honest is the next item.

**The scheduler-dependent classification refinement.** In the spike's terms:
the old theorem asserted `OrdinaryAction (syscall call)` for every call other
than the three injectors, from every starting World; at ef7c535,
`runSendWorkers` and the timer waits run the general scheduler (`schedule`),
and an encrypt worker's poll runs NET_RX, so that assertion is false for five
more constructors, and the classification is replaced by the conservative
list above with a checked witness. Plainly: on the old mirror, received
packets were only processed inside the three operations that inject them. The
new mirror models what the kernel actually does while the guest waits inside
`wg_set`, `wg_up`, `wg_xmit`, `wg_advance` and the observation: queued
kernel work runs, including the decrypt worker and the NAPI poll that
validates counters. So "the data-receive path" is no longer confined to three
syscalls, and a per-syscall "nothing changes" claim for those five would be
false. I re-derived the reach map from the source at ef7c535: the only
validator call is `RxData.lean:362` inside `rxPoll`; `rxPoll` is reached from
`napiSoftirq` and `pollScheduledInline`; `napiSoftirq` from `napiIrqExit`,
the encrypt and decrypt iteration callbacks, and `schedule`; `schedule` from
`runCryptWorkers`, `runSendWorkers`, `afterBatch` and `nestedResched`;
`runSendWorkers` from `afterXmit`, `runTimersPlaceholder`, `afterBatch` and
the syscall tails of `wgSet`, `wgInject`, `wgUp`; `runTimers` from
`afterAdvance` and `idleTimers`; `idleTimers` from `observe` and the tails of
`wgSet`, `wgUp`, `wgXmit`, `wgBatch`. The bodies of `wgSet` (netlink only),
`wgUp` (`Env.wgUp`), `wgXmit` and `wgAdvance` (`Env.advance`) and the whole
of `netnsCleanup` reach none of these, and the WG-level `txStep`,
`receiveStep` and `condResched` (a record peek returning a Bool) cannot
reach `Env`. The excluded set is therefore exactly the constructors with a
path to the scheduler or the poll, and `NoReceiveDispatch` exactly the bodies
with one. This is a legitimate refinement and the minimal one without a World
premise; a finer one ("ordinary when the decrypt queue is empty") would add a
quiescence condition the charter's S3 does not have, which the spike declined
([AGENT 2026-10-13] in its report). The kernel does the same: a task waiting
in `wg_set` has kworkers running `wg_packet_decrypt_worker` and
`wg_packet_rx_poll` under it.

**The new whole-syscall exports.** `S3_syscall`: for every syscall and every
successful run from a state satisfying `Inv`, the logged copy produces the
same result and World with a history, and `Evolution (snapshot w) history
(snapshot w') history'` holds, i.e. every change to a keypair's window in the
whole operation, including the return-to-user work, is an ordinary lifecycle
step or a `validate` at the keypair the packet names. `S3_syscall_ambient`
adds the runner's `skipAmbient` after it, which part 1 noted was unframed in
the exported S3. These are the charter's receive-path clause over the
original action; part 1 found it only under `syscallLogged_evolves`. Signature
checked (`#check` output in the scratch run). Their `Inv` premise is the
reachable-state invariant, discharged at every call by the S1 chain.

**The committed-event interpretation.** In the spike's terms: the new
`Env.Activation.consistent` runs an activation on a copy of the World to test
whether the records are consistent with resuming it, discards that World, and
returns a Bool; such a trial can run the validator; the history records only
committed validator returns, so the probe is lifted unchanged and only
`Activation.run` is observed. I read `Activation.consistent` at
`Env/Batch.lean:197-201`: it is `match (Activation.run a).run (← get) with
| .ok _ => return true | .error (.hidden _) => return false | .error e =>
throw e`, a pure evaluation of the run on the current state that never writes
it back. Plainly: the environment model decides which suspended activation
the records resume by rehearsing each on a scratch copy; a packet "accepted"
in a rehearsal leaves no trace in the mirror's state, so it is not an
acceptance, and counting it would make the history wrong, not the theorem
stronger. The qualifier is about the mirror's bookkeeping (the elimination
among suspended activations is an environment mechanism, not kernel
behaviour); the kernel runs exactly one of them. `S1`'s statement is
unchanged; only its reading is sharpened. Legitimate refinement, no
weakening. One thing worth knowing: the trial also consumes hidden records on
the copy, which the real run then consumes again; that is the point of the
probe and is why `activationConsistent_sameSnapshot` is trivial.

**The single-writer process violation.** This is not a proof assumption. The
charter's section 6 requires one writer at a time in the worktree; Codex#2
let subagents edit disjoint files concurrently for part of the port, recorded
it as a deviation, and returned to serial handoffs. It touches no statement;
the directive's framing of it as a proof's single-writer assumption on the
new mirror does not apply. Plainly: two helpers typed at once for a while,
against the rules of the exercise; nothing in the result depends on it.

**A correction to part 1.** Part 1 argued that `syscallLogged_evolves` makes
event completeness a theorem, because an unlogged acceptance would change a
surviving cell under the same stamp, which no `ordinary` step can express.
The spike's internal reviewer (its R3) points out the loophole: an unlogged
acceptance followed by deletion of that lifetime inside the same `Evolves`
obligation leaves an ordinary final snapshot and an unchanged history. That is
correct; the argument holds only when the validated lifetime survives to the
end of the obligation. Completeness therefore rests on source-call coverage:
`counterLogged_run` proves the exact append at the validator, and every path
from `syscall` to `rxPoll` must go through logged copies. On the new mirror I
checked that map (above) against the observers: `rxPollLogged` substitutes the
one call; `napiSoftirqLogged`, `pollScheduledInlineLogged`,
`encryptStep/IterLogged`, `decryptStep/IterLogged`, `activationRunLogged`,
`dispatchActivationLogged`, `scheduleLogged`, `nestedReschedLogged`,
`workerIter/LoopLogged`, `runCryptWorkersLogged`, `runSendWorkersLogged`,
`afterXmitLogged`, `afterAdvanceLogged`, `idleTimersLogged`,
`runTimers(Placeholder)Logged`, `observeLogged`, `afterBatchLogged`,
`batchLogged`, `floodLogged`, `injectLogged` exist with erasure theorems, and
`syscallLogged`'s tail (`GhostSyscalls.lean:62-72`) uses the logged
versions for exactly the constructors whose tails reach the scheduler. The
originals the observers lift unlogged are `condResched`, `txStep`,
`receiveStep`, `netnsCleanup` and `dispatch` for the `NoReceiveDispatch`
constructors, none of which can reach the poll. Coverage holds; it is a
reviewed fact, not a theorem, and the conventions note's item 5 says so.

## 4. The checked counterexample

`PortCounterexample.lean` (38 lines) builds a World by hand: one device, one
peer with a current keypair of lifetime 1 and a zero replay counter, two
packets in the packet store (a ready keepalive with nonce 0, and an
uncrypted one), the decrypt ring holding the second, the peer's NAPI
scheduled, placeholder mode. Two `#guard`s check that the keypair starts with
counter 0 and that the original `Leanux.syscall (.wgAdvance 0)` returns 0
and leaves lifetime 1 with counter 1 and first bitmap word 2 (bit 1 set, the
one-based nonce 0). I re-evaluated `result` in the scratch run:
`some (0, 1, 1, 1, 2)`. The `#guard`s run in the required build because
`Axioms.lean` imports the file (job 55 of 94 in the log).

What it is: a counterexample to part 1's `NoReceiveCall`-based theorem
(`∀ call, NoReceiveCall call → OrdinaryAction (syscall call)`) evaluated over
the new mirror, from an arbitrary World, not from an accepted trace. What it
is not: a replay, a duplicate acceptance, or a counterexample to S1, S2 or the
charter's S3 as worded, since the charter says "other than the data-receive
path" and `wgAdvance` here runs the receive path (timer wait, scheduler,
decrypt activation, poll). So it is not a Rule Zero event: it reveals no
mirror defect and no kernel misbehaviour. The kernel path it exercises is
real: the advance's wait runs the due timers, the scheduler runs the queued
decrypt work, `wg_packet_rx_poll` validates the keepalive's counter. The
witness was constructed to justify the classification change, and section 3
says why that change is the minimal one. Rule Zero's search remains the
proofs themselves, as in part 1; no statement is proved under a
trigger-excluding premise.

## 5. The conventions note

`docs/2026-10-13-window-proof-conventions.md` ranks five conventions, each
with `ef7c535` file and line references and an altitude label. Against the
thin-layer rule and the future-proof-paths conventions AGENTS.md adopts
(3(a) secret zeroing sites, 3(b) crypto behind three files, 3(d) no new
`partial` or `!`, 3(e) environment via parameters or oracles, B7 the channel
note):

1. State property theorems over a small projection; keep allocation,
   deletion and field updates as named helpers with stable boundaries.
   Concrete, costs nothing, and is how the mirror is already written
   (`keypairCreate`, the packet store's `getRxSkb`/`setRxSkb`/`freeRxSkb`).
   No conflict.
2. Give callbacks explicit effect contracts; compose workers over arbitrary
   callbacks. Proof-side; the mirror already passes callbacks (3(e)). The
   remark that `workerIter`/Step with finite activation loops served the
   proof better than recursive fuel is evidence for the representation batch's
   design, not a request. No conflict.
3. Expose a committed observation boundary. The note is careful: history
   fields or proof-specific branches in the production mirror would not
   preserve altitude; keep history in a proof-side observer or an
   instrumentation cut. As stated it does not conflict. The one concrete
   proposal inside it, "a single optional observer at the actual validator
   result", would if implemented as a parameter of `counterValidate` or
   `rxPoll`: that is proof instrumentation in the C's control flow, which the
   thin-layer rule excludes. The altitude-preserving form is part 1's finding
   2 (the runner's observation output carrying acceptance events) or the
   deferred event log of future-proof-paths 3(c), whose "one mirror site per
   event" convention this already follows; whether a ghost `World.events` is
   acceptable is that note's open user decision U1.
4. Frame resumable operations locally; state contracts over every successful
   initial World rather than a fixture. Proof-side discipline over helpers
   the mirror already has (`NetlinkDump` chunk/start/receive, activation
   iteration). No conflict.
5. Export end-to-end relations; keep a short source-call map of validator
   calls, committed callers and discarded probes; treat the constructor list
   as a derived corollary. Proof-side. This is the right lesson from R3 and
   section 3.

Cheap for the mirror authors: items 1, 2 and 4 ask them to keep doing what
the representation batch did; items 3 and 5 are for proof authors. Nothing
asks for proof-shaped restructuring of the C's control flow; item 3's inner
proposal is the only thing that could become that, and the note itself
conditions it.

## 6. Landing mechanics

The branch's `lakefile.toml` adds `WindowSpike` to `defaultTargets`, so
`lake build`, and with it the fast gate, builds the proofs. Measured cost of
the whole build: 3 min 19 s wall and 3.11 GB peak against 3 min 00 s and
2.49 GB with the first spike, with the spike's 24 modules summing to 34 s of
module time against the mirror's 41 s and sitting at the end of the
dependency chain (I did not build the mirror alone for a clean wall baseline;
from the module times the proofs add roughly a third to a half of the
wall time and 0.6 GB of peak).

Under the maintenance rule the user leans to (the proof tree may lag a named
mirror commit, with repair as a follow-on), the proofs must not be a default
target: a lagging tree would fail every mirror commit's fast gate for a reason
unrelated to the mirror, and the only ways out would be to repair under
pressure or to disable the target, which is gate cruft. Make `WindowSpike` a
separate library target (keep the `[[lean_lib]]`, drop it from
`defaultTargets`) with its own command, `capped -- scripts/in-bundle lake
build WindowSpike`, and its own gate: the build plus a check that every
`#print axioms` output names only the three axioms and no `sorryAx` (a
twenty-line script over the build log; `#print axioms` alone cannot fail).
Run it at the proof tree's own claim points and whenever the tree is repaired
to a new mirror commit, and record the mirror commit the tree is proved
against in the report's pin. The `Leanux` library does not import anything
under `Spikes`, so the mirror's gate is unaffected either way; a check that
this stays true (no `import Leanux.Spikes` outside `Leanux/Spikes/`) belongs
in the same script.

## 7. Effort against the estimate

From the timestamps: `main` reached ef7c535 at 00:31:42 UTC; the branch was
created at 00:32:07; the single commit is at 01:10:32. Elapsed: 38 minutes.
The spike's report says the first passing build, audit and unit run was at
01:02 (30 minutes) and the final review done by about 01:08. Three subagents
plus the coordinator, so at most about two and a half agent-hours, against
part 1's estimate of four to eight. The estimate was high by two to three
times, for one reason: I expected the scheduler loop to need a new induction
principle, and it did not; the activation loops are finite and the existing
`workerIter`/Step composition rules and erasure combinators covered them
("No fuel induction, ring occupancy invariant or extra trace premise is
needed", which the removed and added print lists bear out). Where the time
went, from the diff: `GhostOperations` (+343 lines, the send/timer waits now
observed), `GhostWorkers` (264), `GhostScheduler` (254), `FrameWGMore`
(+271, the stepped-dump helpers, which exhausted the first 800,000-heartbeat
attempt before shared-continuation composition closed them),
`EvolutionScheduler` (126), `FrameEnvWorkers` (124), `EvolutionOperations`
(99), `FrameEnv` (96), `FrameWGBase` (+70, the packet store); the
`PortCounterexample` and the classification change; and the regenerated
`Axioms.lean`. Part 1's prediction of where the cost would fall was right;
its size was not.

## 8. Reproduce

```sh
cd .worktrees/spike-window-r
capped -- scripts/in-bundle lake build                        # 94 jobs; the #guard runs at job 55
git diff --stat ef7c535..b09f065 -- . ':!Leanux/Spikes'        # three docs and the lakefile
grep -c 'depends on axioms\|does not depend on any axioms' <build log>   # 1240
grep -c sorryAx <build log>                                    # 0
```

Scratch axiom check: a file importing `Leanux.Spikes.Statements` and
`Leanux.Spikes.PortCounterexample` with `#print axioms` on the ten names of
section 2 and `#eval Leanux.Spikes.PortCounterexample.result`, run with
`capped -- scripts/in-bundle lake env lean <file>`.
