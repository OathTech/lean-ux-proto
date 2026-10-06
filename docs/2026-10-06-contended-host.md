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

## 4. The in-guest 4 s bound

The guest now reports each trace's guest time from `wg_up` to its last
operation (`LEANUX_TIMING`, `linux/timing.jsonl`). In 3 WireGuard suite
runs (1320 child runs):
- the median was 1.74 s;
- the 99th percentile was 3.0 s;
- the maximum was **3.80 s**, for `b2_lengths`, which has 3.3 s of planned
  waits after `wg_up`.

That leaves 0.2 s of the 4.0 s bound, so a heavier load fails the trace
with `environment_failure trace_exceeds_rekey_bound`. See section 5 for the
change.

## 5. Evidence

See the integration record of this branch (the final report) for the runs:
- before and after the fix, 3 concurrent WireGuard suite runs each;
- the full check;
- replays of every recorded chunk through the new mirror.
