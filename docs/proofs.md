# Proofs about the mirrors

`Leanux/Proofs/` is the repository's proof tree: every theorem about the
executable mirrors lives there and nowhere else. Proofs are a validation
channel for the models beside the differential check, under Rule Zero: the
mirror is never edited to let a proof close; a proof that cannot close is a
report against the mirror, settled by the check. The standing rule and the
gate are in [AGENTS.md](../AGENTS.md); this file is the map of the tree and
the register of its results.

## Layers

The tree is laid out by layer and by result. Shared layers sit at the top,
subject-specific layers under the subject, and each result in its own
directory whose `Statements.lean` is the gated surface.

- `Leanux/Proofs.lean`: the root. It imports every result's `Statements`
  module and the checked counterexamples; `lake build LeanuxProofs` builds
  exactly this closure, outside the mirror's default build.
- `Leanux/Proofs/Framing/`: generic operational framing over the mirror's
  state and monad. `Basic` says which state an action leaves unchanged, with
  the lifetime distinction a reused keypair slot needs; `WP` is the
  weakest-precondition form; `Allocation` names the mirror's private
  allocation helpers for proofs.
- `Leanux/Proofs/Logged/`: logged copies of mirror functions with erasure
  theorems (erasing the log gives back the original run, state, result and
  failure), from the validator (`Basic`, `RxPoll`) through the workers, the
  scheduler, the environment operations and the syscalls to the runner
  (`Runner`). The erasure core (`Outer`, `Tools`) is independent of what is
  logged; today the log carries validator-acceptance events.
- `Leanux/Proofs/WG/CounterWindow/`: the receive counter window as a pure
  model of `counter_validate` (`Model`), its refinement to the mirror's
  `counterValidate` (`Refinement`, the S2 theorems), and replay freedom for
  finite sequences of validator calls (`MirrorCalls`).
- `Leanux/Proofs/WG/Keypairs/`: the keypair store projected with allocation
  lifetimes (`Lifetimes`, `LifetimeMirror`), the ordinary steps that may
  allocate or delete a slot but never alter a surviving window (`Ordinary`,
  `OrdinaryHot`, `OrdinaryRules`, `SnapshotRules`); `Frames/` holds the
  per-function frame contracts over that projection for the kernel helpers,
  WireGuard, pipes, the filesystem syscalls and the environment; `Evolution/`
  carries the acceptance-history invariant through the observers, the
  scheduler, the operations, the runner and the syscalls.
- `Leanux/Proofs/WG/ReplayWindow/`: the first result (below).

The dependency order is CounterWindow, Logged, Framing, Keypairs,
ReplayWindow. The conventions that keep proof work cheap are in
[the future-proof-paths note](2026-10-06-future-proof-paths.md) and
[the window-proof conventions](2026-10-13-window-proof-conventions.md).

## Results

| Result | Statements | Directory | Charter | Review | Mirror commit | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Receive counter window: replay freedom (S1, S2, S3) | S1: every accepted execution has its exact acceptance history, and no two events share an allocation lifetime and a wire counter. S2: `counterValidate` returns exactly what receive.c's rule returns and leaves exactly its replay state. S3: every non-receive syscall and every validator call leave every other keypair's window unchanged, per call and for whole syscalls including the runner's ambient step. | `Leanux/Proofs/WG/ReplayWindow/` (`Statements.lean`, 15 terminal declarations; `Counterexamples.lean`) | [charter](2026-10-12-charter-window-proof.md) | [independent review, two parts](2026-10-12-spike-window-review.md); the spike's [report](2026-10-13-spike-window.md) and [self-review](2026-10-13-spike-window-self-review.md) | ef7c535 | lagging since 6f1f84c (the epoll landing): the tree builds over main's mirror except `Evolution/Syscalls.lean`, where the three epoll system calls (`sysEpollCreate1`, `sysEpollCtl`, `sysEpollWait`) need frame contracts for the rest of `Leanux/FS/Eventpoll.lean` (the create, ctl and wait paths, `ep_item_poll` through `vfs_poll`, the loop and reverse-path checks); the repair is a follow-on |

The gate for every row: `capped -- scripts/in-bundle scripts/proof-gate`
(the build, the axioms of every terminal statement, the forbidden tokens,
the imports and the default targets).

## Adding a result

1. Make a directory under the subject, `Leanux/Proofs/<Subject>/<Result>/`,
   with a `Statements.lean` that holds every terminal statement, each with a
   docstring saying in plain words what it claims. Material another result
   could use goes in a layer, not in the result.
2. Import the `Statements` module from `Leanux/Proofs.lean`; the gate fails
   until it does.
3. Run the gate. Add the row above with the charter, the review, the mirror
   commit the result holds over, and the status.
4. The mirror stays as it is. If the proof needs the mirror to be different,
   that is a finding, reported with the path and what the kernel does there.

## Lag and repair

A row names the mirror commit its result holds over. A mirror change may
land while the result lags: the integration record says so, the row's status
becomes "lagging since <commit>", and the repair is a follow-on task on the
proof tree, not a condition on the mirror change. Every claim point reports
the lag.

The tree was restructured from `Leanux/Spikes/` on 2026-10-13; the dated
documents above keep the historical names in their prose.
