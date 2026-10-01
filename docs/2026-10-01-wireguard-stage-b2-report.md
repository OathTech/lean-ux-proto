# WireGuard stage B2 (receive path up to Noise) — report, 2026-10-01

Status: **awaiting user signoff** for `main`. Branch `task/wg-stage-b2`.
Design and the user's decisions: [next-plan, stage B2](2026-09-29-next-plan.md).

## 1. What B2 delivers

**The instrument** [USER: approved as a finer-grained instrument, and the
patched kernel as the single oracle]:
- `kernel/patches/wireguard-kcov-remote.patch` wraps two call sites in
  `kcov_remote_start_common(skb_get_kcov_handle(skb))` / `kcov_remote_stop()`:
  - `wg_receive`'s call of `wg_packet_receive` (softirq);
  - the handshake receive worker's call of `wg_receive_handshake_packet`.

  It also adds two `#include` lines, each replacing a blank line, so every
  line number is preserved.
- The build: the patched configuration is identical to the approved
  networking kernel apart from the version string. Only `wg_receive`,
  `wg_packet_handshake_receive_worker` and the version banner differ in the
  binary. It is applied strictly and by hash (`scripts/apply-kernel-patch.py`),
  to a copy of the locked source, and recorded in
  `kernel/identity-x86_64-net-rcov.txt`.
- The guest:
  - A parent process enables `KCOV_REMOTE_ENABLE`, then forks the trace
    process. That process inherits the common handle, and so do the skbs it
    allocates.
  - Per-task coverage stays enabled for the whole trace, because
    `KCOV_DISABLE` clears the inherited handle; each operation resets it.
  - Each operation's coverage row is the task PCs followed by the remote ones.
  - A remote comparison stream was built, then removed: it paid nothing.

**The mirror** (`Leanux/WG/Receive.lean`, `Leanux/WG/Blake2s.lean`):
- `wg_receive`;
- `prepare_skb_header` and `validate_header_len`;
- handshake queueing, with the queue as device state and `handshake_queue.last_cpu`;
- the receive worker, which the environment runs;
- `wg_cookie_validate_packet`, with MAC1 computed by a BLAKE2s reference
  checked against build-time vectors, under the device's MAC1 key;
- the cookie and data index lookups, and the drops.

A valid MAC1 enters Noise (stage C) and is `unsupported`. 46 new decisions;
the table has 479, and 322 of them have KCOV witnesses.

## 2. Evidence

The final check ran on commit `b87df92` (clean tree), on the patched kernel
(`vmlinux` sha256 `70a134be…`, identity `2594fdff…`). It covered every suite:
- handwritten, critic and wireguard (37 traces, 8 of them B2);
- 1,000 generated FD traces;
- 200 generated WireGuard traces, a third of them receive traces.

| Check | Result |
|---|---|
| Behavior | 1,310 / 1,310 traces agree (38,900 operations) |
| Control flow over task and remote coverage: witnesses, unreported decisions, unlisted functions, reached functions, order | all agree |
| Operands | 320,450 pairs match |

The FD and earlier WireGuard evidence is re-established on the new single
oracle and the new guest. 591 outcomes are unobservable, and 156 decisions
have no witnessed side (`decision_coverage`).

**Mutants** (all 14, on the patched kernel):

| Mutant | Kind | Result |
|---|---|---|
| W1–W5, B1-M1–M5 | stages A and B1 | all rejected, by the same checks as before |
| B2-M1: the 4-byte pull is dropped | the bug the check found | rejected: outcome not witnessed (3 traces) |
| B2-M2: `last_cpu` never wraps | state across packets | rejected: opposite outcome covered (5 traces) |
| B2-M4: a 91-byte response is accepted | parsing | rejected: outcome not witnessed |
| B2-M3: the length is tested before the type | order inside `validate_header_len` | **survives** |

B2-M3 survives because `validate_header_len`'s decisions own no KCOV point in
this build, and its comparisons are hoisted or folded (section 3). It
documents a real gap, not a check failure.

**What paid for itself** (AGENTS.md: checks must pay for themselves):
- **Remote coverage** found a mirror bug: a message shorter than its 4-byte
  header fails `pskb_may_pull` before `validate_header_len`.
- **The operand check** caught a race the rules missed. A transmit to a peer
  whose handshake work is pending reads a reference count that the worker
  changes. Any reference-count access on such a peer is now outside the
  domain.
- **Removed because they did not pay:**
  - comparisons on `validate_header_len`: GCC hoists the length tests to line
    30 and skips type tests it can already decide;
  - the remote comparison stream: no remote decision is a declared comparison
    yet.

**Review.** An independent Fable structural review found no wrong decision or
outcome on the modeled paths, and confirmed BLAKE2s and the MAC1 arithmetic.
Its findings, all fixed:
- MAC1's witness (true side only: GCC skips the false side's `else if`);
- the 16-byte `sizeof(struct message_data)`;
- a pending-worker guard on `wg_inject`;
- B2 decisions no longer repeatable;
- the handshake queue as device state, run by the environment.

## 3. Gaps (accepted, [USER] "so long as we'll fix it later")

- **Silent drops.** Nearly every outcome here is a drop, so assurance is
  control flow over the remote stream; the only observation is `sendto`'s
  return.
- **MAC1 is only half-checked.** Its "invalid" side has no witness, so a mirror
  that wrongly computed "valid" would stop (`unsupported`) and never be
  compared. Its "valid" side is witnessed (line 134), so a mirror that wrongly
  computed "invalid" would be caught. There are no valid-MAC1 messages in the
  domain until stage C.
- **`validate_header_len` is unobservable**, decision by decision, in this build.
- **One check runs outside the remote section:** `wg_receive`'s `!sk` test.
- **Timing.** The receive worker is awaited by the same 0.4 s wait as B1.

## 4. Next

Stage C: the Noise handshake as the responder. A valid initiation, crafted by
the harness from a known peer key, produces an observable handshake response.
That makes the receive path observable and closes the gaps above.
