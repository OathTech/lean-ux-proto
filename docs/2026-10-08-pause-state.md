# Pause state, 2026-10-08 [AGENT, coordinator]

The project is paused while it moves to a new machine (user request,
2026-10-08). This note records:
- what is on `main`;
- what sits on branches, with its status;
- what to resume, and in what order;
- how to move the work across.

The setup procedure for the new machine is in
[SETUP-new-machine.md](SETUP-new-machine.md).

## 1. What is on `main`

`main` contains everything signed off up to D3:
- the FS and eventfd slice;
- WireGuard stages A–C, D1 and D2;
- the choice stream: hidden inputs, steering and dispatch sections;
- P (pipes stage 1);
- the wgc base (QEMU_SLOTS=3);
- the base2 load-robustness fixes;
- E-A (cookie consumption, MAC2, XChaCha20-Poly1305);
- **D3**: timers and virtual time advance.

The D3 merge (`84a56fd`) was approved by the user on 2026-10-07: "yes
approved on both", covering the merge plus kernel and boot parameter.

The approved oracle kernel:
- patch `kernel/patches/choice-stream.patch`, sha256 `3b0f2026…`;
- identity `8744fcc4…`;
- boot parameter `clocksource=refined-jiffies`;
- config unchanged.

The validated state on main:
- full check 1611/1611 across 7 suites;
- WireGuard mutants: 68 rejected, 1 survivor (B2-M3), 1 equivalent (H-M8), 0 without a verdict;
- pipes mutants 18/18.

The evidence summaries are in `docs/2026-10-05-d3-timers.md`, sections 16–17.

The pause branch (`task/pause`) adds documentation only:
- the WireGuard census;
- the future-proof-paths note;
- the five revised workstream designs;
- this note;
- the setup guide;
- the AGENTS.md pointer to the future-proof-paths conventions.

## 2. Work on branches, not on `main`

Merging any of these needs the user's signoff on the concrete changes
(AGENTS.md).

| Branch | Tip | Contents | Status |
|---|---|---|---|
| `task/int-dl` | `ccd2200` (validated), `9828d95`, then 3 more | L (device lifecycle) on D3 | **`ccd2200` validated**: 1631/1631, 24/24 claimed mutants, L-M10 not claimed. `9828d95` is the rekey-bound margin fix (generator cost model, no give-up chain) plus L's two D3-dependent traces. It is not validated, because its follow-up agent was stopped after two days. `e6fd196`, `8bc345a` and `8cfb314` are **unrequested** side changes. One of them changes when the guest flushes records. Treat them as proposals: review them, or park them on `task/int-dl-out`. |
| `task/int-da` | `5903cc3` | A (allocation failures, A1+A2) on D3, plus 3 pipe allocation sites | **Validated**: 1642/1642 both disarmed and default, 26/26 mutants, controls pass. It needs a **new oracle kernel**: identity `c79e3e0c…`, patch `4274afa3…`. That is A plus D3's race fix plus `KCOV_DISPATCH_MAX` 32, which is record-only and approved in principle. There is also a control kernel, `044b46e5…`. Not combined with L yet. |
| `task/e-b` | `2c5f492` | E (DoS: under-load via queue depth, cookie replies, ratelimiter) | Validated on its own base: 124/124 WireGuard suite, mutants E-M7..E-M11. **Not integrated.** Its guest has a stale opcode layout (flood=15, L=16-18); map it to the table on main: 15–17 L, 18 `wg_flood`, 19 `wg_advance`. |

The designs (merged on `task/pause`) are audited and revised; each has a
v2 or v3 audit-response section.

| Design | Doc |
|---|---|
| W1+W2 netlink completeness and multi-message dumps | `docs/2026-10-06-w1-w2-netlink.md` |
| W3+W12 peer removal with queued work; multi-peer timers | `docs/2026-10-06-w3-w12.md` |
| W4+W7 transmit shapes and bulk queues (trimmed to the WireGuard boundary) | `docs/2026-10-06-w4-w7-transmit-bulk.md` |
| W5+W6 receive shapes (trimmed to the WireGuard boundary) | `docs/2026-10-06-w5-w6-receive.md` |
| W8+W9 netns exit and socket routing | `docs/2026-10-06-w8-w9-netns-routing.md` |

### Other branches

The other `task/*` branches are earlier stages, already integrated in
other forms:
- `a-alloc`, `a-k`, `a1`, `a2` (all in `int-da`);
- `e-dos` (in `e-b`);
- `l-g`, `l-life`, `l-m` (in `int-dl`);
- `p2-int`;
- `steering`, `steer-step2`, `hidden-inputs`;
- `wg-stage-c`;
- `int-dl-fix` and `int-dl-out` (side worktrees of the stopped agent);
- the three `wg-stage-*-wip-backup` branches.

Keep them until the stack above lands, then prune them.

## 3. Decisions in force

These are recorded with provenance in [the decisions register](decisions.md)
and in the design docs.

### User decisions, 2026-10-05 to 10-08

**Goal and scope**
- The goal is complete single-CPU WireGuard coverage: 100 % of what is
  "reasonable". Exclude something only for a profound reason, and record
  the reason.
- Stop at the **WireGuard boundary** "unless this breaks important
  things". The IP stack is modeled only where WireGuard's code paths or
  observables depend on it.

**Kernel changes**
- Oracle kernel changes that only *record* or *steer* are approved in
  principle, with per-merge signoff.
- Behaviour or config changes (`CONFIG_PACKET`, boot parameters) each
  need their own case.

**Checker and conventions**
- T1 is approved: per-NET_RX-section operand agreement for bulk traces
  (two mirror runs, plus an independence check). It is built in W4+W7.
- The future-proof-paths conventions are recorded in the note, with a
  pointer in AGENTS.md (added on `task/pause`).

**Ways of working**
- Agents are time-boxed.
- Mutant runs are scoped to the touched files, on reduced corpora. The
  full set runs once, at milestones. A full WireGuard mutant pass takes
  18 h or more on a contended host.
- Agents make no unrequested harness changes during validation.

### Coordinator decisions [AGENT]

- MTU 0 and poll-budget exhaustion are in scope.
- `ip_error`, suspend and the ICMPv4 identifier capture are deferred.
- Link flags in W8b are dropped.
- tstats is provisional.
- W13 (second device) comes last.
- The three approved sysctls are held back: nothing kept by the boundary
  rule needs them.

## 4. Resume order on the new machine

1. Set up per [SETUP-new-machine.md](SETUP-new-machine.md). Rebuild the
   D3 oracle kernel and check that its identity is `8744fcc4…`. Run the
   unit tests and one full check to confirm 1611/1611 on the new
   hardware. Re-measure the trace-time margin: the give-up class ran
   within 1.6 % of the 4.5 s bound on the old, contended host.
2. **Land L.** Take `ccd2200` plus `9828d95`, run one full check and the
   L and D3 mutants only, then get signoff. Review the three unrequested
   commits separately.
3. **Land A** on L.
   - Build the combined kernel; the one-off build sequence lives on
     `task/int-da` in `scripts/build-kernel` and
     `kernel/patches/gen-choice-stream.py`.
   - Run a full check, disarmed and default.
   - Run the A mutants, then get signoff, which includes kernel
     `c79e3e0c…`.
4. **Land E** on L+A: renumber the opcodes, run a full check and the E
   mutants, then get signoff.
5. Integration housekeeping:
   - the future-proof-paths audit items (fail-open kdf defaults →
     `invariant`; fuel the two `partial def`s; a bounds-checked
     `AipNode.bitAt`);
   - the P review follow-ups (`docs/2026-10-05-p-pipes.md` §15).
6. **Interface commit.** Split `Env.lean`
   (`Env/IpStack.lean`, `Env/Batch.lean`), assign file ownership, and
   keep the shared opcode and record-kind tables:
   - opcodes 20–21 for W2, 22–24 for W8/W9;
   - record kind 306 for the dst-cache jiffies.
7. **Implementation streams**, in parallel, each from its revised design:
   - W1+W2;
   - W4+W7;
   - W5+W6;
   - W8+W9, which includes W9's dst-cache record kernel change;
   - W3+W12, with W3 after L;
   - then W10/W11 leftovers.
8. W13 last. Then a final census, and a list of exclusions with their
   reasons.

## 5. Moving the work across

`main` on this machine is ahead of `origin/main`, and no `task/*` branch
is on the remote. Moving them needs one of:
- a **push** to `origin`, which needs the user's explicit approval at
  the point of the push; or
- a **git bundle**, copied by the user (no remote involved).

The evidence directories (`.artifacts/runs/evidence/`, and
`.worktrees/*/.artifacts/runs/evidence/`) are untracked. Copy them if
the integration records are to be kept: about 300 MB in total.

Kernels, toolchains and `.deps` are rebuilt or re-fetched on the new
machine, per the setup guide, rather than copied.
