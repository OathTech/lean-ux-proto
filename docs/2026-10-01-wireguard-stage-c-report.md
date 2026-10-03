# WireGuard stage C (the Noise responder) — report, 2026-10-01

Status: **merged** to `main` with user signoff on 2026-10-01 (integration
record in `.artifacts/runs/evidence/wg-stage-c/`).
Design: [next-plan, stage C](2026-09-29-next-plan.md) [AGENT; the user asked to
proceed without stopping after the design].

## 1. What C delivers

**The harness:**
- `harness/noise.py` is a Noise IKpsk2 initiator in pure Python: X25519,
  ChaCha20-Poly1305, BLAKE2s HMAC and the KDF. It is checked against the
  RFC 7748 and RFC 8439 vectors. It builds valid initiations, and for negative
  traces it can override the ephemeral key, static key or MAC1 key, or tamper
  with a tag.
- The fixture's sender is bound to `[::]:51998`, so a learned endpoint is
  deterministic. `wg_observe` drains the sender too and reports each reply's
  length, type and receiver index.
- `scripts/wg-stage-c-corpus.py` writes the 15 stage C traces
  deterministically. The WireGuard generator gains a handshake class (a sixth
  of its traces).

**The mirror** (`Leanux/WG/Handshake.lean`, `Leanux/WG/NoiseCrypto.lean`):
- `wg_noise_handshake_consume_initiation` with every value. The mirror
  computes the chaining key, the hash, both DH results, both decryptions and
  the timestamp, using Lean references checked at build time against the
  RFC 8439 vector and the Python implementation.
- `wg_noise_handshake_create_response` and `wg_noise_handshake_begin_session`.
  The ephemeral and session keys are random, so their values are not tracked;
  every decision is determined and mirrored, including `kdf`'s per-call-site
  pointer checks.
- `add_new_keypair` for the responder, including putting a pending next
  keypair (`wg_noise_keypair_put` with `kref_put`), and `handshake_zero`.
- `wg_socket_set_peer_endpoint_from_skb`, with the endpoint comparison
  generalized to the source address and interface.
- The rx/tx counters, `mod_peer_timer`, and the traversal timer (a keepalive
  of 4 s or less would fire inside the trace and is `unsupported`).
- `wg_socket_send_buffer_to_peer` is a cut point, recorded as an output
  (`World.sent`). The environment routes it to the fixture's sender; any other
  destination is `unsupported`.
- Existing paths that now meet a live next keypair are mirrored rather than
  excluded: peer removal (`wg_noise_keypairs_clear`) and identity changes
  (`wg_noise_expire_current_peer_keypairs`).

The skb's source (family, address, port, arrival interface) comes from the
environment. That is fixture knowledge, not C.

58 new decisions; the table has 533, and 365 of them have KCOV witnesses.

## 2. Evidence

The final check ran on commit `6b30e91` (clean tree), on the patched kernel
(`vmlinux` sha256 `70a134be…`). It covered every suite:
- handwritten, critic and wireguard (52 traces, 15 of them stage C);
- 1,000 generated FD traces;
- 200 generated WireGuard traces, a sixth of them handshake traces. 36
  handshake responses were sent in those traces.

| Check | Result |
|---|---|
| Behavior, including replies at the sender | 1,325 / 1,325 traces agree (38,927 operations) |
| Control flow over task and remote coverage | all agree |
| Operands, including the remote stream | 320,308 pairs match |

650 outcomes are unobservable, and 168 decisions have no witnessed side
(`decision_coverage`).

**Mutants** (all 18; the earlier 13 are rejected exactly as before, and
B2-M3 still survives):

| Mutant | Kind | Result |
|---|---|---|
| C-M1: an equal timestamp is not a replay | state across packets | rejected: behavior (a reply to a replay, which Linux drops) |
| C-M2: the response carries the index `handshake_zero` cleared | data | rejected: behavior (9 traces) |
| C-M4: the old next keypair stays in the index | behavior-preserving | rejected: opposite outcome covered (3 traces) |
| C-M5: the learned endpoint tests IPv6 first | data | rejected: mirror invariant |
| C-M3: no traversal timer after receiving | behavior-preserving | **survives** |

C-M3 survives for two reasons:
- The same out-of-line function (`wg_timers_any_authenticated_packet_traversal`)
  is called twice in one operation. Coverage is a set of PCs per operation,
  so the second call is invisible.
- The timer it arms never fires within a trace.

This is a real limit of the instrument, as B2-M3 is.

**What paid for itself:**
- **The remote comparison stream**, removed in B2 because it paid nothing, is
  restored. On the responder path, the handshake worker takes and drops peer
  references, and those reference counts are declared comparisons. Without
  the stream they would be unchecked: 54 more operand pairs on the WireGuard
  suite.
- **Remote coverage** corrected four witness spans in `noise.c`. Each is a
  layout fact about this GCC build, read from the trace:
  - `mix_dh`'s line 416 is the shared return epilogue;
  - `no_peer`'s continuation is the argument line 624;
  - `ss_failed=0` is witnessed only by the inlined `mix_precomputed_dh`
    success block;
  - `begin_session`'s `&&` continuation follows both short-circuit paths.

**Review.** An independent Fable structural review re-derived every
crypto vector and confirmed the responder path's decisions, order and
state. Its findings, all fixed:
- `send.c`'s two decisions were anchored two lines early;
- the choice points of `wg_socket_send_buffer_to_peer` and
  `wg_socket_send_skb_to_peer` were unmirrored; they are now mirrored and
  listed;
- timing facts were in the mirror; they are now the environment's timing
  contract (`World.timing`, defined in `Leanux/Env.lean`);
- the worker did not set `CREATED_INITIATION`;
- the IPv6 scope was hard-coded; scoped sources are now `unsupported`;
- three spans and two stale comments.

## 3. Gaps

- **The initiator role is outside the domain:** consuming a response needs the
  device's own random ephemeral key. Data packets with a session are outside
  too (stage D).
- **Index lookups** with entries under random indices remain `unsupported`
  (cookie and data messages after a handshake).
- **Response contents** beyond length, type and receiver index are random,
  and are not compared.
- **wg0's device rx counters** (`dev_sw_netstats_rx_add`) are not tracked:
  nothing observes them yet.
- **Repeated calls are invisible** within one operation (C-M3).
- **Unobservable decisions:** `kdf`'s length checks, the flood and replay
  tests (one source line), and several `create_response` failure arms that
  are constant under the domain.

B2's gaps: handshakes now produce observable responses, so a mirror that
wrongly computed MAC1 "valid" now emits a reply that Linux does not. The
half-checked MAC1 gap is closed for initiations.
