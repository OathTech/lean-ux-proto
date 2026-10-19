# 04 — Staged packets can be put back with no key in view when the flush on key confirmation races another caller's steal, and a confirming keepalive arms no timer to send them

Target: Linux 6.12.110, `drivers/net/wireguard/send.c`,
`drivers/net/wireguard/receive.c`, `drivers/net/wireguard/netlink.c`,
`drivers/net/wireguard/device.c`. Configuration where it matters: SMP, or
a single CPU with a process-context caller racing the receive softirq. On
the oracle (one CPU, no interrupt-raised NET_RX inside a netlink call) the
window does not open. State: **Draft**, not filed. Drafted 2026-10-15.

No patch branch (README §5).

## Affected code (pristine 6.12.110)

- `send.c:342-414`, `wg_packet_send_staged_packets`: steals the whole
  staged queue into a local list (:349-352), returns if it is empty (:353-354),
  reads `current_keypair` (:357-360); with no valid key it puts the packets
  back at the head of the staged queue (:406-408) and queues a handshake
  initiation (:413). The comment at :401-405 accepts a reordering here, not
  a delay.
- `receive.c:343-349`, `wg_packet_consume_data_done`: when the received
  packet confirms a new keypair (`wg_noise_received_with_keypair`), the
  flush `wg_packet_send_staged_packets(peer)` (:348) sends what is staged.
- Other callers of the same flush that run in process context with BH
  enabled: `set_peer` (`netlink.c:482-483`, after any new peer attribute),
  `wg_set_device` (`:577`, after the private key changes), `wg_open`
  (`device.c:55`).
- `receive.c:355-363`: a keepalive (`skb->len == 0`) is counted and jumps
  to `packet_processed`, skipping `wg_timers_data_received` (:365), the
  call that arms the keepalive timer; `receive.c:180-186`: an initiator
  with nothing staged confirms the session with exactly such a keepalive.
- `send.c:21-27` and `:63-67`: a queued initiation is rate limited by
  `last_sent_handshake` against `REKEY_TIMEOUT`.

## Classification

**DESIGN NUANCE, with a QUESTION.** The flush-and-put-back shape is a
documented choice (the comment at :401-405 says why the put-back's
reordering is tolerated). The consequence that seemed worth raising is a
delay, not a loss: if the confirmation's flush runs between another
caller's steal (:351) and that caller's put-back (:407), the flush finds
the queue empty and returns (:353-354); the other caller then puts the
packets back with no key in view and queues an initiation that the
responder's `REKEY_TIMEOUT` rate limit normally suppresses (the response
has just gone out). The packets then wait for the next trigger: another
`wg_xmit` to that peer, a persistent keepalive, or the keepalive timer,
which the confirming packet arms only if it carried data. A confirming
keepalive arms nothing, so a one-shot datagram can sit staged until
unrelated traffic. The question is whether the flush at :348 should run
again, or the put-back path should re-check the key, when a confirmation
raced the steal.

## Reproducer

None in this corpus. The race needs two callers of the flush interleaved
at :351-:407: on SMP, `wg_xmit`'s or a netlink caller's flush on one CPU
against the NAPI poll's confirmation on another; on one CPU, a
process-context caller (`set_peer`, `wg_set_device`, `wg_open`) with
NET_RX run at its `spin_unlock_bh` (:352 or :360) by an interrupt-raised
softirq, which the oracle's fixture never produces inside a netlink call.
A reader without this repository would need an SMP box and a responder
whose first transmissions race the initiator's confirming keepalive, then
observe the staged datagram leaving only with later traffic.

## Expected versus actual

Expected: a packet staged before the session is confirmed leaves when the
session is confirmed. Actual: under the race it stays staged until another
trigger sends it; bounded by `MAX_STAGED_PACKETS` trimming in `wg_xmit` and
by the next keepalive or transmission.

## Impact

Latency on the first packets of a session, under a race that needs SMP or
an interrupt-timed softirq; no loss. Attack feasibility: none identified
(the race is not steerable from the wire beyond the timing of the
response).

## How this repository found it

The correspondence audit of `Leanux/WG/Send.lean` against `send.c`
(`docs/2026-10-15-audit-send.md`, section 19), by reading the flush's
steal-and-put-back against its callers. Rule Zero, read in order: the
mirror is not involved (the race is outside the one-CPU oracle's
schedules and the mirror models no such interleaving); the kernel's
behaviour is a defensible choice with a consequence worth a question;
the former is the usual explanation and does not apply here.

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so.
