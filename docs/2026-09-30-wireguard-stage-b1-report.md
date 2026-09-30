# WireGuard stage B1 (transmit and routing) — report, 2026-09-30

Status: **merged** to `main` with user signoff on 2026-09-30 (integration
record in `.artifacts/runs/evidence/wg-stage-b1/`).
Design: [next-plan, stage B1](2026-09-29-next-plan.md). Decisions are marked
[USER] or [AGENT].

## 1. Why B1, and what it delivers

[AGENT] Stage B was split into two parts, and the transmit part (B1) went
first:
- **Receive path** (B2, the original stage B). It runs in softirq and on
  workqueues, so it needs the U2 remote-coverage kernel. Without stage C's
  Noise crypto, almost every packet past parsing is dropped silently.
- **Transmit path** (B1). It runs in the sender's process context, so current
  KCOV covers it. Its outcomes are observable: `ENOKEY`, `EDESTADDRREQ`,
  `tx_errors`, `tx_dropped`, emitted handshake initiations, and `tx_bytes`.
  It also covers the routing through the allowed-IPs trie that stage A
  deferred.

**Harness.**
- The network fixture has `lo` up. Descriptors 4 and 5 are UDP listeners on
  127.0.0.1 and ::1 at port 51999, and descriptor 6 is a dual-stack UDP
  sender.
- Three new operations:
  - `wg_up` brings the device up with `ioctl(SIOCSIFFLAGS)`, then adds an
    address and a default route on `wg0` for each family.
  - `wg_xmit` sends a UDP datagram to a destination.
  - `wg_observe` waits for the handshake workers, then reports what the
    listeners received and `wg0`'s transmit counters.

**Mirror** (`Leanux/WG/Device.lean`, `Send.lean`, plus changes elsewhere):
- `find_node`, `lookup` and `lookup_dst`;
- `wg_open` and `wg_xmit`;
- staging, keepalive and handshake queueing in `send.c`;
- `keypair_get`;
- `tx_errors`, `tx_dropped` (including the purge when a peer is released) and
  `tx_bytes`.

There are 39 new decisions; the table now has 433, and 298 of them have KCOV
witnesses.

**The handshake worker** runs in a kworker, outside per-task KCOV. It is a
contract, applied at `wg_observe`, and the structural review confirmed it
against `wg_noise_handshake_create_initiation` and
`wg_socket_send_skb_to_peer`:
- An initiation is sent iff three things hold: the device has an identity,
  the precomputed static-static is nonzero, and the peer has an endpoint.
- A sent initiation adds 148 bytes to the peer's `tx_bytes`.

**Races with the worker are outside the domain.** An operation whose result
depends on whether the worker has run is `unsupported`. The exception is work
queued earlier in the same system call, before it slept. The kernel is
`CONFIG_PREEMPT_NONE` on one CPU, so that worker cannot have run yet.

## 2. Check change (for review)

A C function that labels decisions and that Linux ran in an operation (any
frame of a counted point, in an anchored file) must have at least one
reported decision in that operation.
- **Why:** mutant B1-M2 deleted `wg_noise_keypair_get` from the mirror and
  passed. All of its outcomes are unobservable, so nothing flagged it.
- **Validation:** offline on all recorded WireGuard coverage, then on the
  final full run including the FD corpus: no false positives.
- **Scope:** it closes a class of omissions, not all of them. An omitted
  decision inside a function that reports others is still caught only
  through witnesses.

## 3. Evidence

The final check ran on commit `8de5ba3` (clean tree), on the networking
kernel, with every suite: handwritten, critic, wireguard (28 traces, 14 of
them B1), 1,000 generated FD traces, and 200 generated WireGuard traces (about
half B1).

| Check | Result |
|---|---|
| Behavior: returns, errnos, dumps, emitted datagrams, transmit counters | 1,302 / 1,302 traces agree (38,808 operations) |
| Control flow: witnesses, unreported decisions, unlisted functions, reached functions | all agree |
| Order within each C function | all agree |
| Operands | 320,548 pairs match |

Coverage of the 39 B1 decisions: 18 see both outcomes, 20 see one outcome,
and 1 is never evaluated (`keypair_get.refcount_zero`, which needs a session).

**Mutants**, on commit `8de5ba3`, over the wireguard suite:

| Mutant | Kind | Rejected by |
|---|---|---|
| B1-M1: `find_node` keeps the first match | routing | A1 on `b1_longest_match` (the initiation goes to the wrong listener); on the full suite, a mirror race stop |
| B1-M2: `wg_noise_keypair_get` omitted | behavior-preserving | the new reached-function rule (13 traces) |
| B1-M3: `wg_xmit` keeps its peer reference | behavior-preserving | A2: unreported decisions, reached functions, operands (11 traces); A1 (1) |
| B1-M4: the worker emits for a low-order peer | behavior | A1 (datagrams) |
| B1-M5: `is_dead` tested before expiry | behavior-preserving | A2: order (13 traces) |

The stage A mutants W1–W5 are rerun on the same commit and all stay rejected.
W5 is rejected by A2 alone on `wg_trie_v6`.

**Review.** An independent Fable structural review found no wrong decision,
order or outcome. Its findings, all fixed:
- invalid destinations that Linux's IP layer handles before routing;
- the stale plan text;
- the keepalive-while-up case, now modeled;
- stated assumptions (the keepalive timer invariant, the 0.4 s wait).

## 4. Deviations and gaps

- **No raw packet socket.** An `AF_PACKET` sender was the plan, but the kernel
  has no `CONFIG_PACKET`. Rather than change the kernel U1 approved, datagrams
  go through a UDP sender and routes. As a result, `wg_xmit.bad_protocol` (a
  hand-built packet with the wrong protocol) is unreachable.
- **The worker is checked only through its effects.** Remote coverage (B2,
  U2) can check its decisions later.
- **Races with the worker are excluded,** not modeled. The generator's filter
  drops about 12% of B1 candidates for this.
- **Timing.** Harness timing assumptions: the 0.4 s wait for workers, and the
  4 s bound after `wg_up`. Breaking either shows as a mismatch or an
  environment failure, never as agreement.
- **Timer invariant.** The persistent-keepalive timer is harmless only while no
  session exists. B2 will need to revisit this.

## 5. Next

**B2** (receive path) needs the U2 remote-coverage kernel, which you approved
on 2026-09-29, and packet injection. Everything past MAC1 validation needs
Noise crypto (stage C) or an oracle. The first B2 slice would be parsing and
header validation (`prepare_skb_header`), `wg_packet_receive`'s queueing, and
cookie MAC1 checking with a BLAKE2s reference.
