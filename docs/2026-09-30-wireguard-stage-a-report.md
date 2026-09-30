# WireGuard stage A — report, 2026-09-30

Status: **awaiting user signoff** for `main`. Branch `task/wg-stage-a`,
worktree `.worktrees/wg-stage-a`. The plan is
[next-plan section 4](2026-09-29-next-plan.md). Decisions are marked [USER]
or [AGENT].

## 1. What stage A delivers

**Kernel** [USER U1, 2026-09-29]. `scripts/build-kernel` with
`LEANUX_KERNEL_PROFILE=net` is recorded as `kernel/config-x86_64-net`, release
`-leanux-kcov-net`. The build's `vmlinux` sha256 is
`a8c40b559ddeef581a1a48586f33d855ae0789893e25cb3c42ba2116592d1c5b`. It lives in
the worktree's `.artifacts/kernel-net`. The branch makes shared
`.artifacts/kernel-net` the default oracle; the copy there happens at
integration (section 5).

**Harness.**
- Traces with a WireGuard operation run in a fresh network namespace with a
  down WireGuard device `wg0` (ifindex 3) and a generic-netlink socket at
  descriptor 7. Descriptors 4–6 are still `/dev/null`.
- `wg_set` sends a structured `WG_CMD_SET_DEVICE`:
  - private key, listen port, fwmark, replace-peers;
  - peers with public key, preshared key, remove / update-only /
    replace-allowed-ips flags, endpoint, keepalive and allowed IPs;
  - keys and addresses are lowercase hex bytes.
- `wg_get` returns a `WG_CMD_GET_DEVICE` dump. The dump is decoded strictly
  into a canonical device state (`harness/wg.py`).

**Mirror** (`Leanux/WG/`, about 1,080 lines).
- The `allowedips` trie in full: insertion, removal by peer, freeing, reading,
  and each peer's list order.
- Peers:
  - creation and removal;
  - reference counts through `kref`;
  - public-key lookup as a map;
  - endpoints and keepalive.
- The static identity, with Curve25519 computed by an RFC 7748 reference.
- The set path of `netlink.c`: `wg_set_device`, `set_peer`, `set_allowedip`,
  `set_port`.
- The get path of `netlink.c`: `wg_get_device_start/dump/done`, `get_peer`,
  `get_allowedips`.
- The socket calls' `fdget`/`fdput`.

**Decision table.** 209 new decisions across `allowedips.c`, `peer.c`,
`noise.c`, `netlink.c`, `socket.c`, `peerlookup.c`, `cookie.c`,
`curve25519.h` and `refcount.h`. The table now has 394 decisions, and 271 of
them have KCOV witnesses. Every unwitnessed outcome has a reason. Seven spans
were narrowed as `compiler_shared` after reading the binary: shared
epilogues, merged `goto` targets, a duplicated `out:` tail, and a line-table
row that starts another block. Each is commented at its decision.

**Check changes** (for review):
- Witnesses come only from PCs of the functions `kcov.json` lists, and only
  from header lines reached through an inline frame.
- A span line of an anchored `.c` file run by an unlisted function fails.
- The `branch_free` exemption is allowlisted in `kcov.json` (`fls128`).
- Device states compare as canonical JSON, so `true` and `1` differ.
- A guest chunk that exceeds the console-output limit is rerun as halves, and
  the split is recorded.

Details are in `correspondence/README.md`.

**Corpus.** 15 handwritten WireGuard traces (`corpus/wireguard`), plus a
seeded generator (`wireguard-generated`, 200 traces by default).

## 2. Evidence

The final check ran on commit `5b9342e` (clean tree), on the networking
kernel, with all suites: handwritten, critic, wireguard, 1,000 generated FD
traces and 200 generated WireGuard traces.

| Check | Result |
|---|---|
| Behavior, including every decoded dump | 1,288 / 1,288 traces agree (38,652 operations) |
| Control flow: two-sided witnesses, unreported decisions, unlisted functions | all agree |
| Order within each C function | all agree |
| Operands against `KCOV_TRACE_CMP` | 324,964 pairs match (80 declared comparisons) |

The FD/eventfd corpus passes unchanged on the new kernel. U1's condition for
retiring the old oracle is therefore met.

Coverage of the 202 WireGuard and Curve25519 decisions: 99 see both outcomes,
97 see one outcome, and 6 are never evaluated. The unevaluated arms need a
protocol version attribute, a dump cursor, a device that is up, or a changed
sequence number mid-dump, all outside the domain.

**Planted bugs** (the WireGuard suite on the final commit):

| Mutant | Kind | Rejected by |
|---|---|---|
| W1: `read_node` does not mask | behavior | A1 (dump) |
| W2: an equal endpoint is always rewritten | behavior-preserving | A2: outcome not witnessed |
| W3: the displaced peer's reference is not dropped | behavior-preserving | A2: opposite outcome covered |
| W4: fwmark handled after the listen port | behavior-preserving | A2: order |
| W5: the trie picks the wrong bit | dump-invisible on IPv6 | a mirror invariant on removal; A1 on `wg_trie_v4` (run at pre-squash `12f2458`, same trie code, kept on `wg-stage-a-wip-backup`); **A2 alone** on `wg_trie_v6` |

W5 shows that the decision trace sees a trie shape the observable dump
cannot.

**Reviews.**
- An independent Opus review of the tooling found no case where a wrong mirror
  passes today. It found three fail-open paths in the new check rules and
  several in dump decoding. All are fixed and tested.
- An independent Fable structural review found no correspondence error. It
  found one state-shape deviation, now fixed: a null private key must leave
  `static_public` unchanged. It also found a false statement about the crypto
  implementation, corrected in the plan. Its remaining questions are recorded
  below as residual gaps.

## 3. Deviations from the plan

- **Routing through packets is not covered.** The plan's stage table says stage
  A observes routing through packets on a veth pair. The stage A design
  [AGENT 2026-09-30] keeps `wg0` down so that everything stays in process
  context. So `wg_allowedips_lookup_dst`, sockets and timers are not
  exercised. They fit stage B, which brings remote coverage and packet
  injection.
- **Crypto implementation.** The build uses the x86-64 crypto implementations,
  because `WIREGUARD` selects them. The mirror's reference computes the same
  function.
- **The default kernel changes** to `.artifacts/kernel-net`, as U1 foresaw.

## 4. Residual gaps (accepted for the prototype unless you say otherwise)

- The stage A cut points listed in `correspondence/README.md`. They include
  the `hlist` helpers' branches in unanchored headers and the bucket walk of
  the public-key lookup, which is reported as one decision.
- Header span lines run by unlisted functions are not checked. The function
  list is kept complete by review.
- Covered lines in listed functions that are in no span are not checked. The
  structural review checked the two candidates in the binary.
- The FD slice's gaps carry over unchanged.

## 5. Effort, and what integration involves

- **Effort.** About 1,080 lines of mirror and 600 lines of decision table cover
  roughly 1,000 lines of C on the modeled paths. Reading the binary for
  compiler effects took about as long as writing the mirror. The recurring
  effects:
  - merged `goto`/`return` blocks;
  - out-of-line static helpers (`common_bits`, `add.isra.0`);
  - line-table rows that start another block.
- **Integration**, each step needing your signoff:
  1. Fast-forward `main` to the branch.
  2. Copy the worktree's `.artifacts/kernel-net` to shared
     `.artifacts/kernel-net` (U1's own output directory). The old
     `.artifacts/kernel-active-sandbox` stays in place.
  3. Record evidence in `.artifacts/runs/evidence/wg-stage-a/`, with
     `integration.json` holding your signoff.
