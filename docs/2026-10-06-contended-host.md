# Check failures on a contended host — 2026-10-06

Status: regression note for branch `task/flake` (based on `task/wgc`).

The host is shared with other jobs (load average 50-100 on 32 CPUs, with up
to 3 concurrent QEMU guests). Under that load, WireGuard check runs failed
in four ways. Three were modeling gaps: placements Linux really takes, which
the environment model rejected or never modeled. The fourth was an
infrastructure budget. [USER 2026-10-06, via the coordinator]: these
placements are modeling gaps, not flakes. Fix them in the model with exact,
fail-closed rules, never with retries.

## 1. An ambient record inside a loopback NET_RX section

**Symptom.** `b1_other_endpoint`, operation 3, failed with "expected
retransmit_jitter (site 14), the record is site 49"
(`.worktrees/e-a` run `mutant-E-M3`, chunk-000a).

**Records.** These are the remote stream records, by sequence number, of
the handshake send worker:

```
627 section_start send_worker
628-633 clocks, ephemeral, tai64n, index
634 section_start net_rx_action
635 flow_hash_secret
636 start_dl_timer        (ambient)
637 section_stop net_rx_action
638 retransmit_jitter
639 section_stop
```

No resched record appears, and the NET_RX section is nested at the send. It
was not deferred to ksoftirqd. The cause was `skipCut`. It dropped cut
records only up to the first ambient record, then skipped that one record
and stopped, so the section stop that followed was never consumed.

**Fix.**
- `skipCutSites` now continues past ambient records.
- The lax site-level skip of zero or more NET_RX start/stop pairs at the
  send cut points is replaced by an exact rule (`WG.loopbackSend`,
  `Leanux/WG/State.lean`). Each loopback transmission raises NET_RX
  (`World.netRxRaised`). The raise is consumed exactly once, by its section
  at the send's `local_bh_enable`. The section holds only the delivery's cut
  records (the ICMP reply's IP ident, the flow-hash secret) and ambient
  records. An operation ends with no raise pending.

**Why the section is always nested at the send.** The raise happens with
bottom halves disabled, so `raise_softirq_irqoff` does not wake ksoftirqd
(softirq.c:704-709). `__local_bh_enable_ip` then runs `do_softirq` inline
(softirq.c:401-408). The backlog poll also handles the ICMP port-unreachable
reply inside the same section. Deferral to ksoftirqd is therefore not a
placement here, and a section found later is a mismatch.

**Points the rule applies to:**
- `sendBufferToPeer` (handshake messages);
- `sendSkbToPeer` (data);
- `wg_xmit`'s ICMP error. Here the error raises NET_RX only if
  `icmp_global_consume` drew a credit record. `icmp_global_consume` draws
  exactly when the rate limits let the error through (icmp.c:310-339,
  ipv6/icmp.c:195-238).

**A section the old rule had absorbed.** Replaying all recorded model
inputs found 41 `wg_xmit` operations to 224.0.0.1 that recorded one NET_RX
section and nothing else. The source of that section is the fixture's own
multicast loopback copy: `ip_mc_output` clones the packet to
`dev_loopback_xmit` before `ip_finish_output` (ip_output.c:382-424). The
new rule places that copy's section before `wg_xmit`
(`Env.xmitMulticastLoop`). An IPv6 multicast destination is `unsupported`,
because the copy depends on wg0's group memberships.

## 2. The NAPI poll inside `wg_queue_enqueue_per_peer_rx`

**Symptom.** Two traces failed on the same comparison: `rx_roam_v6` (this
branch, run `before-3`) and `rx_in_order` (task/l-g, `regress-wg-fs`). In
operation 4, `__refcount_add_not_zero` (refcount.h:145) gave Linux operands
1, 1, 3, where the mirror reported 1, 1, 2.

**Records.** The comparison child recorded
`net_rx(start, stop), decrypt_start, clock, net_rx_start, clock,
net_rx_stop, resched, decrypt_stop`. This is placement (b/c): a NET_RX
section right after the enqueue.

**Cause.** In `wg_queue_enqueue_per_peer_rx`, an interrupt can arrive at
`__napi_schedule`'s `local_irq_restore`. Its exit runs the NET_RX before
`wg_peer_put`, so the poll's allowed-IPs lookup sees one more peer
reference. The records are identical to placement (c), which comes after
the put. The D2 design said the placements "differ only by the worker's
state, which the poll does not read", and that was wrong for this one.

**Fix.**
- `Env.napiIrqExit` is a hook inside the enqueue. A poll whose records
  leave the placement open is counted, and the mirror reports the count
  (`napi_irq_ambiguous`).
- The placement is an input to the mirror (`napi_irq_before_put`).
- On an operand mismatch, the check reruns the comparison child under the
  other placement vectors, for up to 3 open polls. It accepts one complete
  execution whose operands all agree, and records it in `report.json`
  `napi_irq_placements`.
- No record distinguishes the two placements. Recording one would need a
  kernel change, which this task does not make.

## 3. Guest timeouts

**Old budget.** `guest_timeout` was 120 s, plus 1.6 s per `wg_observe`,
plus 0.05 s per operation. It counted neither `wg_inject`'s 0.4 s wait nor
the 0.1 s queue waits. Across 148 recorded chunk runs in all worktrees,
6 timed out at 1.00-1.01x that budget and 10 more completed at
0.90-0.98x. Run `before-1` lost 100 traces to two such timeouts.

**New budget.** The budget now has two parts:
- the guest's fixed waits, exactly (2 children × 0.4 s per inject or
  observe, plus 0.1 s per set, up or xmit);
- 3 × the measured computation (30 s, plus 2.0 s per WireGuard trace, plus
  0.03 s per operation).

A 50-trace WireGuard chunk now gets about 570 s. It used about 200 s
(ratio 0.29-0.38).

**Retry.** A chunk that fails with `timeout` or `resource_busy` (every trace
alike) is rerun once, and `report.json` `chunk_retries` records it.
`output_limit` is still split, and a mismatch is never rerun.

`LEANUX_QEMU_SLOTS` stays 3, [USER 2026-10-05]. The guest wall times
measured with 3 concurrent guests fit the new budget with more than 2.5x
headroom.

## 4. The in-guest trace bound

The guest now reports each trace's guest time from `wg_up` to its last
operation (`LEANUX_TIMING`, `linux/timing.jsonl`). Over 9 WireGuard suite
runs with this instrument (3960 child runs, three of the runs pinned to one
CPU, below):
- the median was 1.74 s;
- the 99th percentile was 3.0-3.24 s;
- the maximum was **3.84 s**, for `b2_lengths`, which has 3.3 s of planned
  waits after `wg_up`.

The old 4.0 s bound left 0.16 s, so a heavier load fails the trace with
`environment_failure trace_exceeds_rekey_bound`.

**Change.** The bound is now 4.5 s, and its origin is read just before the
`wg_up` ioctl, outside its coverage window. It used to be read after the
ioctl returned. No WireGuard timer is armed before `wg_up`
(`mod_peer_timer` needs a running device), and none fires earlier than 5 s
after it is armed. So the 0.5 s margin holds by construction.
`Env.timing` is unchanged for whole seconds: a timer of 4 s or less may
expire, one of 5 s or more cannot. The generator's wait budget stays at
2.8 s.

**A slip, caught by the check.** The first version read the clock inside
the coverage window. The generic clock hook recorded that read as a choice
from an undeclared consumer, and the check rejected all 220 traces that
contain `wg_up` (runs `pinned-1` to `pinned-3`). Fixed in 997575c.

## 5. Evidence (2026-10-06)

All WireGuard suite runs use `--suite wireguard,wireguard-generated`, 296
traces each.

| Runs | Code | Host | Result |
|---|---|---|---|
| before-1..3, concurrent | task/wgc 86cf5ee | load average 20-98 | 1 pass. before-1 lost 100 traces to 2 guest timeouts. before-3 had 1 control_flow_mismatch (rx_roam_v6, section 2) |
| after-1..3, concurrent | 2cff2f4 | load average falling to about 7 | 3/3 pass (296/296, 11193 operand pairs), no retries |
| final-1..3, concurrent, all pinned to one CPU (`taskset -c 31`, about 2.5x slower guests) | 997575c | load average 4-10 plus the pinning | 3/3 pass, no retries. 50-trace chunks took up to 276 s; the old budget was about 248 s |
| full check | 2cff2f4 | | pass, 1369/1369, 39260 operations, 323087 operand pairs (as D2) |

Other evidence:
- **Pinned runs on the old budget.** In the pinned runs, 8 of 45 chunk runs
  ran longer than the old budget formula allows. The longest took 0.50x the
  new budget.
- **The open placement occurs.** It occurred again in `pinned-3`, where
  `d2_rx_window_boundary` agreed under placement (c').
- **Replays.** Every completed chunk of before-1..3, and of wgc par1/par2
  (same base), replays through the new mirror (`run_chunk` on the recorded
  Linux outputs) with full agreement. That is 20 chunks. `rx_roam_v6` agrees
  under placement (c').
- **Model inputs from every worktree.** All recorded model inputs across the
  worktrees give the same output under the old and new mirror, except the
  b1 trace. That trace now agrees.
- **Record mutants** (`evaluator/test_model_replay.py`). The old rule
  accepted three changes to the records: no section at the send, two
  sections at it, and one placed after the send. The new rule rejects all
  three. An ambient record inside a section is now accepted.
- **Mutants** (`scripts/wg-mutants.py`): W3, B1-M3, D1-M14, H-M10, D2-M10
  and D2-M12 are all rejected. D2-M12 is conclusive, with 3 order (b/c)
  placements. The D2-M10 and D2-M12 patterns were updated for the new
  `irqExit` hook.

## 6. Open

- **50-trace WireGuard chunks are near the output limit.** They produce
  16.66 of 16.78 MB of console output, and every 100-trace chunk exceeds
  it. Under the pinned load the 50-trace chunks exceeded it too, and were
  split to 25. Splitting costs a guest run each time but never fails a
  trace. A smaller first chunk for WireGuard traces would save that run.
- **A pending NAPI poll at any other point of the decrypt worker.** For
  example, an interrupt inside `decrypt_packet` of the next packet. The
  records would show its section there, and the mirror stops with a hidden
  mismatch (fail-closed). It has not been observed.
