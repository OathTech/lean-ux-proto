# E under-load reachability probe — results, 2026-10-05

Throwaway probe (`harness/probes/e_underload_probe.c`, run by
`harness/probes/e_underload_run.py`), booted on the oracle kernel
`.artifacts/kernel-net-choice` (single CPU, `PREEMPT_NONE`, TCG). **Not the
oracle.** It answers the audit's C1/C2: is `under_load` (`handshake_queue_len
>= 512`, receive.c:112) reachable on one CPU?

**Method.** A fresh netns with `wg0` (fixed private key, listen port 51820,
up). The probe blasts copies of a *valid-MAC1* handshake initiation (148 B,
MAC1 computed offline for wg0's public key, body otherwise garbage) and counts
`MESSAGE_HANDSHAKE_COOKIE` (type 3) replies back on its socket. A valid-MAC1
initiation processed while `under_load` makes wg0 emit a cookie reply
(receive.c:126-132,139-143 → cookie.c). So **>=1 reply = `under_load` was
crossed**. Four burst mechanisms, each after a 2 s drain + the 1 s
`last_under_load` decay so the reading is clean.

**Result (second run, GSO fixed — `UDP_SEGMENT` takes an `int`, not a `u16`):**

| Mechanism | Datagrams sent | Cookie replies | under_load reached |
|---|---|---|---|
| `gso_sendmmsg` (8 GSO datagrams × 128 segments, one sendmmsg) | 8 | 809 | **yes** |
| `gso_loop` (8 GSO datagrams, a send() loop) | 8 (151552 B) | 794 | **yes** |
| `plain_sendmmsg` (1024 plain datagrams, one sendmmsg) | 1024 | 550 | **yes** |
| `io_uring` (1024 IORING_OP_SEND, one enter) | 1024 | 462 | **yes** |

First run (before the GSO `int` fix) already had `plain_sendmmsg` 568 and
`io_uring` 444; GSO reported `sent=-1` purely from the `u16`/`int` sockopt bug.

**Conclusion. `under_load` is reachable on one CPU, by every mechanism tried,
including plain `sendmmsg`.** The receive worker (`WQ_CPU_INTENSIVE`, process
context) does **not** fully drain at each producer `cond_resched`: the producer
outruns it, and once under load the worker's per-packet cost rises
(make_cookie + a cookie reply over loopback), so the queue stays above 512 for
hundreds of packets. GSO is the strongest: **8 sendmsg calls (1024 segments in
~8 softirqs) suffice**, confirming the audit's C1 — loopback `NETIF_F_GSO_UDP_L4`
delivers up to 128 segments per sendmsg into one NET_RX softirq with no drain
point, and wg's encap socket has no GRO so `udp_rcv_segment` fans them out to
`wg_receive` one by one inside that softirq.

This **refutes** the first draft's "unreachable on one CPU" claim. The revised
design (`2026-10-05-e-dos.md`) rescopes E to include the under-load arms.

Full serial logs are under the task artifact root
(`.artifacts/e-underload-probe/boot.log`, Git-ignored).
