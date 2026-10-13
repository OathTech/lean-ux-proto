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
  allocation helpers for proofs. `Projection` composes and factors arbitrary
  equality views; `WGKernel` selects the seven dedicated WireGuard kernel
  fields, and `FSFileRefs` proves six original file-reference helpers once
  for the keypair, peer and packet projections. These are immediate-return
  frames, not preservation of queued work or later scheduler effects.
- `Leanux/Proofs/Logged/`: logged copies of mirror functions with erasure
  theorems (erasing the log gives back the original run, state, result and
  failure), from the validator (`Basic`, `RxPoll`) through the workers, the
  scheduler, the environment operations and the syscalls to the runner
  (`Runner`). The erasure core (`Outer`, `Tools`) is independent of what is
  logged. Validator observations carry acceptance events; `Checkpoints` observes
  arbitrary projections at committed operation boundaries, with exact erasure
  to the original runner and an exact singleton-append theorem.
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
- `Leanux/Proofs/WG/AntiReplay/`: campaign R1, uniqueness and the inclusive
  lower edge; reusable arithmetic is in `CounterWindow/Bounds`, and ordered
  acceptance-history bounds in `Keypairs/Evolution/Bounds`.
- `Leanux/Proofs/WG/Lifetimes/`: generic allocation frontiers, old-identity
  provenance and removal (`Store`), with projection contracts and composition
  over actual original helper executions (`Actions`). `WG/Packets/Primitives`
  covers the eight skb-store helpers within one device epoch;
  `WG/Peers/Primitives` covers getter/setter identity and reference helpers;
  `Peers/Frames` carries live identities through initialization, and
  `Peers/Allocation` gives exact original peer creation and finite-sequence
  allocation/reference contracts.
- `Leanux/Proofs/WG/LifetimeSafety/`: campaign R2 in progress: keypair store
  absence/freshness at original operation endpoints (`Keypairs/Identity`),
  peer/packet helper-family contracts, and a checked stale dump-cursor finding.
  Full caller/lifecycle and all-internal-access safety remain unproved.
- `Leanux/Proofs/WG/AllowedIps/`: width-parametric prefix arithmetic (`Prefix`)
  and exact original-helper execution equations (`ArithmeticMirror`); `Tree`
  proves longest-prefix lookup, canonical-prefix uniqueness and depth bounds
  from local structural validity. `WG/CryptokeyRouting/` exports these checked
  components of campaign R3; original node-store traversal, mutation/history
  and packet-path refinements remain in progress.

The dependency order is CounterWindow, Logged, Framing, Keypairs,
ReplayWindow. The conventions that keep proof work cheap are in
[the future-proof-paths note](2026-10-06-future-proof-paths.md) and
[the window-proof conventions](2026-10-13-window-proof-conventions.md).

## Results

| Result | Statements | Directory | Charter | Review | Mirror commit | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Receive counter window: replay freedom (S1, S2, S3) | S1: every accepted execution has its exact acceptance history, and no two events share an allocation lifetime and a wire counter. S2: `counterValidate` returns exactly what receive.c's rule returns and leaves exactly its replay state. S3: every non-receive syscall and every validator call leave every other keypair's window unchanged, per call and for whole syscalls including the runner's ambient step. | `Leanux/Proofs/WG/ReplayWindow/` (`Statements.lean`, 15 terminal declarations; `Counterexamples.lean`) | [charter](2026-10-12-charter-window-proof.md) | [independent review, two parts](2026-10-12-spike-window-review.md); the spike's [report](2026-10-13-spike-window.md) and [self-review](2026-10-13-spike-window-self-review.md) | c85e86b | current (R1 gate rechecked the unchanged result; earlier epoll carry from ef7c535 to 6f1f84c remains as reviewed) |
| R1: anti-replay uniqueness and inclusive floor | No wire counter is accepted twice in one allocation lifetime; every accepted counter is at or above the inclusive lower edge, for pure runs, original validator calls and accepted runner histories. Equality at the charter's floor is intentionally permitted, with a concrete recorded replay. | `Leanux/Proofs/WG/AntiReplay/` (`Statements.lean`, 9 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r1--anti-replay-uniqueness-and-the-inclusive-floor) | c85e86b | current |
| R2 components: store identities; stale dump-cursor finding | Successful original operations do not reintroduce absent, previously allocated keypair identities; reuse of an empty slot is fresh. Original peer allocation/reference helper sequences preserve old-identity provenance, with exact fresh creation; the eight packet primitives preserve lifetimes within one device epoch, and a freed slot cannot be read afterward. Exact runner checkpoints reproduce a retained dump cursor releasing a replacement peer. Full caller/lifecycle and internal-access safety remain unproved. | `Leanux/Proofs/WG/LifetimeSafety/` (`Statements.lean`, 28 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r2--lifetime-identity-and-retained-references-in-progress) | c85e86b | current component; R2 in progress |
| R3 components: prefix arithmetic and pure-tree lookup | Original IPv4/IPv6 prefix helpers agree with leading-bit arithmetic, including exact branch-record effects. A locally valid pure tree returns the longest matching owned prefix, has unique canonical prefixes and fits the traversal depth bound. Original node-store traversal, mutation/history and packet-path refinements remain unproved. | `Leanux/Proofs/WG/CryptokeyRouting/` (`Statements.lean`, 6 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r3--cryptokey-routing-in-progress) | c85e86b | current component; R3 in progress |

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
