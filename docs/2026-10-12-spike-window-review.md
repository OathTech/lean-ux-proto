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
