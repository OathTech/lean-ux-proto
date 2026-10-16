# WireGuard: the parallel plan to the model-layer apex

A sequencing plan for the WireGuard work after the pre-release review, with
every lane started as early as its inputs allow and proof carries accepted
as a running cost. Lowest time to delivery is the objective; the gates are
the claim point (one integration at a time), the carry per landing for each
running proof campaign, and a design-and-audit round before each extension.

Provenance: [USER 2026-10-14] parallelise more than the first plan did, even
at some proof-integration overhead, running the representation fixes in
parallel with phase 0 and fixing up after. The plan assumes proof fix-up is a
cost we bear. Code-to-mirror proofs beyond the binary-level scoping probe are
out of this plan by the same decision. The apex table the plan works toward is
the one put to the user on 2026-10-14 (the model layer's reachable rows).

## 1. The rules the plan runs under

- Every lane is one agent in one worktree on one branch from `main`; the
  coordinator integrates; nothing lands without the user's signoff on the
  concrete change.
- A representation change lands as soon as its claim point is green. No
  batching for the proofs' sake: each running campaign carries at the next
  natural point after a paste, under the lag-and-repair rule. Two campaigns
  running at once never merge each other; each merges `main`.
- One integration per day at most: a claim point is about an hour at eight
  slots and the coordinator serialises them. Two ready streams share an
  integration when their files are disjoint.
- A design note and an independent audit precede every extension; a
  settling pass on the oracle follows every mirror change; an independent
  review follows every landed proof result. These have paid for themselves
  every time and are not the overhead to cut.
- The register (`docs/proofs.md`), the tray and the decisions file are
  current at every landing.
- Oracle changes stay record-only unless a case is put to the user; a
  rebuild is one per integration, carrying every new hook.

## 2. The lanes, all started now

| Lane | Content | Inputs it needs | Estimate |
| --- | --- | --- | --- |
| A. Proof campaign 1 (Codex#2, running) | R2 whole-run closure, R3 removal and packet paths, R4 conservation; carries after each landing | none new | 1 to 2 weeks to land, plus carries |
| B1. Handshake ring | `handshake_queue.ring` as the `PtrRing` the crypt queues use (audit items I1/F10) | none | design 0.5 d, audit 0.5 d, build 2 d |
| B2. W13, a second device | `Kernel.wg` as a map keyed by ifindex, receive demultiplexing by socket, two NAPIs in one softirq, the second-device fixture, the corpus both ways | none; a receiving-socket record if the NET_RX records do not place the demux (record-only) | design 1 d, audit 0.5 d, build 4 d |
| B3. Timer wheel | `kernel/time/timer.c`'s wheel as a mirror of its own, so firing order is semantics and the kind-310/311 reads become derived; the environment line redrawn | a design note the user reads, since it moves the environment line | design 1.5 d, audit 0.5 d, build 4 d |
| B4. Load and the rate limiter | under-load as a recorded input at its kernel source; the rate limiter's periodic GC and its entry-allocation record (record-only) | none | design 0.5 d, audit 0.5 d, build 2 d |
| C. FIB trie | `net/ipv4/fib_trie.c` as a new mirror module with its own corpus, record-only hooks if any, frames only for the proofs | the scout's ranking; a design with audit | design 1 d, audit 0.5 d, build 6 d |
| D. Proof campaign 2 (a second Codex) | the handshake and configuration group: Noise state-machine invariants (three keypair slots, IK transitions), index-table uniqueness, endpoint roaming only on authenticated packets, get-after-set and replace-peers semantics, termination and progress under stated fairness | the toolchain bump landed (today) | 2 to 3 weeks, plus carries |
| E. Proof campaign 3 (a third Codex, later) | the data-path group: sender-side counters, delivery conservation if A leaves it, the drop-arm characterisation, resource bounds, key lifetime over the timer wheel, the end-to-end routing composition | A's R4 conservation; B4 for resource bounds; B3 for key lifetime; C for the composition (prerequisite regime per result) | starts when A lands; 3 weeks |
| F. Binary-level scoping (running) | the Kraken probe on one function | none | 3 days |
| G. Background | module audits of the remaining WireGuard modules (Send, Peer, Socket, Timers, AllowedIps, State), the overnight generated-trace soak, the tray, release checks | idle box time | continuous |

Lanes B1 to B4 and C start today with their design notes; their audits run
tomorrow; their builds start the day after. The audits in G start today as
well, since they take no box time.

## 3. The schedule

Day 0 (today): the toolchain bump lands; the scoping probe runs; design
notes for B1 to B4 and C start; two module audits start; campaign 2's
charter is written.

Days 1 to 2: the five design audits; campaign 2 starts on the bumped
`main`; builds of B1 and B4 start (the smallest); A carries the toolchain
bump at its natural point.

Days 3 to 5: B1 and B4 land (one integration each, or one shared if their
files are disjoint); pastes to A and D; builds of B2, B3 and C under way.

Days 6 to 10: B2 and B3 land; pastes; C's build continues; A lands R2 to
R4 with reviews when they close, which may be inside this window.

Days 11 to 14: C lands; campaign 3 starts on the landed base (every
prerequisite in by then); D continues.

Weeks 3 to 5: D lands with reviews; E works through its list and lands
result by result; the release checks run on the revision after D.

Critical path: C (the FIB mirror, about eight days from design to landing)
then E's routing composition (about five days), with B3 then E's key
lifetime a parallel chain of similar length. Delivery of the apex table's
reachable rows: about five weeks from day 0, against roughly eight weeks
for the sequential plan.

## 4. The cost we bear, estimated

- Carries: each landing of B or C costs each running campaign a carry. With
  about six landings and two campaigns, twelve carries at one to eight
  hours each, which is two to four agent-days in all. B3's carry is the
  largest, since the timer frames change shape; B1's is the next, since the
  handshake ring's frames change type.
- Merge conflicts at integration: `Leanux/Kernel/Defs.lean`, `Env.lean`,
  `correspondence/kcov.json`, `docs/decisions.md` are touched by most lanes.
  The coordinator resolves them keeping both sides, as today; the
  three-way kcov.json merge is routine.
- Claim-point serialisation: five to six integrations in two weeks is
  inside the one-per-day budget, with slack for a red run.
- Two campaigns on one tree: disjoint module groups keep the shared
  `Framing` and `Logged` layers rarely touched; when both need a layer
  change, the coordinator lands one first and the other carries.

## 5. The risks, and what bounds them

- B3 may redraw the environment line further than a week's build allows:
  the design note is timeboxed, and if the wheel cannot be mirrored at the
  thin layer without the records, the lane stops at the note and E's key
  lifetime stays record-based.
- B2 may need a receiving-socket record: record-only, class-approved, one
  rebuild with the integration.
- C's corpus needs routing-table state the harness does not yet configure:
  the design says what the guest must add, and that is harness work inside
  the lane.
- Two campaigns may both reshape a shared layer: the merge protocol above,
  and the coordinator's call on order.
- The box: eight guest slots and the Lean builds of three campaigns and five
  streams. Claim points run one at a time; Lean builds are light; the
  spike's earlier load of thirty was two Lean builds plus a campaign's
  axiom census, not the guests.

## 6. What is deliberately out

Code-to-mirror proofs beyond the scoping probe; SMP; the protocol-security
refinement; cryptographic verification of the kernel's assembly; a second
configuration. Each is named in the apex table as a boundary.

## 7. With a dedicated box

[USER 2026-10-14] More resources may be assumed, for example the repository
moving to a third box where it runs uncontended. What that changes, and what
it does not:

- The claim point is the one gate that is box-bound. On an uncontended
  32-core host the slot count goes to about 24 (each TCG guest is one
  thread at 256 MiB), a claim point drops from an hour to about twenty
  minutes, and two integrations can run at once since the slot pool is
  shared by the lock files rather than by a queue. The one-per-day cadence
  becomes two or three, which is what lets B1 to B4 and C land as each is
  ready instead of waiting their turn.
- The load-induced reds go away: the inconclusive order-dependent
  sentinels, the timer-in-batch and crypt-ahead schedules, the tier trace
  under seven guests, every one of which cost a rerun or a diagnosis this
  week, came from contention with other projects' Lean builds. Fewer reruns
  is worth more than the faster claim point.
- If the host allows nested virtualisation, the kvm-probe branch's KVM
  acceleration of the guest is the next multiplier, and the KVM config
  case (high-resolution timers, the D3 re-validation) becomes worth
  settling early rather than later.
- The critical path does not shorten much: C then E's composition is
  agent-limited (design, audit, build, settle, prove), not box-limited.
  Delivery moves from about five weeks to about four; the variance moves
  more than the mean.
- The move costs about a day: a fresh clone, `restore-toolchains.py` and
  `stage-resources.py` from the downloads cache, the kernel pair rebuilt
  from the committed patches (identities must reproduce), Kraken cloned,
  and the running campaigns' worktrees carried as branches, not as
  directories. The main checkout here becomes read-only history until
  then, so there is one `main`.
