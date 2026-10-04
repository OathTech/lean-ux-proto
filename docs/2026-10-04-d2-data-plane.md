# D2: the WireGuard data plane — design, 2026-10-04

Status: **draft for audit** [USER 2026-10-04: the sequence D2 data plane, then
D3 timers, then pipes as the scale test]. The target is "complete on one CPU"
for WireGuard: every path reachable on a single-CPU `CONFIG_PREEMPT_NONE`
kernel, checked against Linux.

D2 adds payload packets in both directions to the mirror. It needs **no
kernel change**: everything it consumes is already captured (random draws,
clocks, dispatch sections, resched records). It changes the fixture, the
mirror, the environment model, the harness's offline Noise code, the
generator and the corpus.

## 1. Target

**Transmit.** A UDP datagram from the fixture's sender, routed into wg0, is:
- staged;
- sent with a session's keypair: nonces, the `ds` field, `create_data`;
- encrypted with its payload: the checksum completed, padding to the MTU
  rule;
- sent by the tx worker.

The check sees the encrypted `message_data` at the fixture's listener (A1
bytes), and the control flow and operands of the whole path. This covers
both packets sent after a session exists and packets staged before it and
flushed when the session completes.

**Receive.** A `message_data` computed offline under the session's keys is
injected and takes the full path:
- `consume_data`: keypair lookup, the peer-dead check, the decrypt queue;
- the decrypt worker: `decrypt_packet`, `enqueue_per_peer_rx`;
- `wg_packet_rx_poll` in a NET_RX section: `counter_validate`, the endpoint
  from the skb;
- `consume_data_done`: endpoint roaming, `received_with_keypair` (the
  responder's confirmation, which promotes `next` to `current`), receive-side
  `keep_key_fresh`, timer arming, keepalive detection, the IPv4/IPv6 checks,
  `lookup_src`, `napi_gro_receive`.

The check sees:
- the inner datagram delivered to the fixture's sender socket;
- `rx_bytes` in the dump;
- the device error counters;
- control flow and operands.

## 2. The inner packet on transmit (environment)

The plaintext that `wg_xmit` receives is built by the IPv4/IPv6 and UDP
stacks, which are cut points. Its bytes must be known exactly, because the
ciphertext is AEAD over them. `Leanux/Env.lean` computes it
(`Env.xmitPacket family dst payload`), replacing `xmitPacketLen`. The
fixture fixes every input:

- **Sender.** `SEND_FD`, bound to `[::]:51998`, dual-stack; IPv4 goes as
  v4-mapped. The destination port is `SEND_PORT` (40000). The source address
  is wg0's (`10.255.254.1` or `fd00:ffff::1`, `route_into_wg0`).
- **IPv4.** `version/ihl 0x45`, tos 0, DF set, **id 0**, TTL 64, protocol
  17, header checksum.
  - **Why id is 0:** `ip_select_ident_segs` (`include/net/ip.h`) gives id 0
    for an unconnected socket with DF set. UDP's default `IP_PMTUDISC_WANT`
    sets DF when the route's MTU is not locked. So no jiffies-derived id
    reaches the bytes; that is a debt in strategy section 7, avoided here.
  - **Verify:** the A1 bytes check this. A wrong assumption fails noisily.
- **IPv6.** Version 6, traffic class 0, **flow label 0**, payload length,
  next header 17, hop limit 64.
  - **Fixture change:** `IPV6_AUTOFLOWLABEL = 0` on `SEND_FD`. Auto flow
    labels hash the flow keys with `hashrnd`, a secret drawn before the
    trace window, which the mirror cannot know.
- **UDP.** Ports 51998 → 40000, length.
  - **Checksum:** wg0 advertises `NETIF_F_HW_CSUM`, so the skb arrives
    `CHECKSUM_PARTIAL`, holding the pseudo-header sum.
  - The environment gives the mirror the partial skb: the bytes,
    `csum_start` and `csum_offset`. `encrypt_packet`'s
    `skb->ip_summed == CHECKSUM_PARTIAL && skb_checksum_help(skb)` becomes a
    real decision.
  - `skb_checksum_help` is a cut. Its output, the folded checksum over the
    transport bytes, is computed by an environment function. Only its
    failure is an `envOk` site.
- **Payload.** The `wg_xmit` operation gains a payload (1 to 1392 bytes for
  IPv4, 1 to 1372 for IPv6), so the packet is at most the MTU, 1420.
  - Larger payloads would fragment locally, and fragments carry a random,
    jiffies-derived id. They are rejected by the generator and by the
    environment (`unsupported`).
  - GSO does not arise for UDP datagrams of this size (no UDP_SEGMENT).
- **MTU.** `PACKET_CB(skb)->mtu = skb_valid_dst ? dst_mtu : dev->mtu`. The
  route through wg0 has dst MTU 1420. This is an environment fact, checked
  by the padding bytes.

## 3. Transmit in the mirror

Widened from D1:
- `wg_xmit`:
  - the staged-queue trim (`> MAX_STAGED_PACKETS`, already modeled);
  - several packets per staged list;
  - `mtu` from the environment.
- `send_staged_packets` with a keypair:
  - per packet: `ds = ip_tunnel_ecn_encap(0, ip_hdr(skb), skb)`, which is 0
    for not-ECT inner traffic; the inline decision is mirrored;
  - the nonce from `sending_counter`;
  - the `REJECT_AFTER_MESSAGES` test.
- `create_data` with a list of packets. **One ring item per staged list**,
  as in the C. The encrypt worker's `skb_list_walk_safe` now walks several
  skbs. A `DEAD` break with remaining skbs follows the C exactly.
- `encrypt_packet` with a payload:
  - padding via `calculate_skb_padding(len, mtu)`, including `len > mtu`,
    which is reachable only via GSO, so not in the domain: the branch is
    mirrored and its outcome stays false;
  - the checksum help;
  - the trailer and the AEAD over the padded plaintext.
- The tx worker sends each packet of the list.
- `wg_timers_data_sent`, today `unsupported`: `mod_timer(new_handshake)` if
  not pending. It **arms a timer only**. `Env.timing.timerMayExpire` must
  say it cannot fire within the trace (it is `REKEY_TIMEOUT + KEEPALIVE_TIMEOUT
  = 15 s` plus jitter, and the guest's trace bound is 4 s).
  - Timer firing stays out of the domain until D3.
- Transmit-side `keep_key_fresh` is exercised with payloads. Its expiry arm
  needs clock steering, which is deferred to D3 (section 8).

Staged before the session: a `wg_xmit` without a keypair stages the packet
and queues an initiation (as today). The offline response then completes the
session, and `send_staged_packets` flushes the staged packets, payloads
included, through the encrypt and tx workers.

## 4. Receive in the mirror

New mirror code, mostly `receive.c` and `queueing.h`:
- `wg_packet_consume_data`:
  - the index lookup now finds keypairs;
  - `keypair_get`;
  - `is_dead`;
  - `enqueue_per_device_and_peer` on the decrypt queue and the peer's
    `rx_queue`.
  - `-ENOSPC` and `-EPIPE` (full queues) are `unsupported`.
- `wg_packet_decrypt_worker` and `decrypt_packet`:
  - keypair validity;
  - `wg_birthdate_has_expired(receiving.birthdate, REJECT_AFTER_TIME)`, with
    a recorded clock;
  - the counter limit;
  - `skb_cow_data` and `skb_to_sgvec` as `envOk` sites;
  - ChaCha20-Poly1305 decryption under `receiving.key` and the nonce, where
    a failure gives `DEAD`;
  - the trim.
- `wg_queue_enqueue_per_peer_rx`: the state set, `napi_schedule`.
- `wg_packet_rx_poll`:
  - the `prev_queue` peek and the state;
  - `counter_validate`, the full RFC 6479 bitmap: `counter`, the
    `backtrack[]` words, `COUNTER_WINDOW_SIZE`, `REJECT_AFTER_MESSAGES`;
  - `wg_socket_endpoint_from_skb`;
  - `wg_reset_packet`, which is a cut;
  - the keypair and peer puts.
- `wg_packet_consume_data_done`, every branch:
  - roaming, via `wg_socket_set_peer_endpoint`;
  - `wg_noise_received_with_keypair`: promoting `next` to `current`, then
    `timers_handshake_complete` and `send_staged_packets`;
  - receive-side `keep_key_fresh`;
  - the timer calls (`any_authenticated_packet_received` deletes a timer;
    `traversal` and `data_received` arm only);
  - keepalive (length 0);
  - the dishonest-size and dishonest-type checks;
  - `ip_tunnel_parse_protocol`;
  - `INET_ECN_decapsulate`, whose inline decisions all have constant
    outcomes for a not-ECT outer header;
  - `pskb_trim`;
  - `wg_allowedips_lookup_src`, a trie walk on the source, mirroring
    `lookup_dst`;
  - `napi_gro_receive`, which is a cut;
  - `update_rx_stats(message_data_len(len_before_trim))`;
  - `DEV_STATS_INC` of `rx_errors`, `rx_frame_errors` and
    `rx_length_errors`.

The **delivery of the inner packet** (the GRO, IP and UDP stacks) is a cut.
The environment decides its outcome, fail-closed:
- **delivered:** a well-formed UDP datagram to wg0's local address at port
  51998 (the sender socket) goes to `senderInbox`;
- **dropped:** a well-formed packet to a non-local destination, or to a
  local port with no socket, is `unsupported`. Forwarding is off, so
  `ip_error` would send a rate-limited ICMP, which is unmodeled.

So the generator's inner packets are either delivered, or rejected by
WireGuard's own checks (dishonest type, size or source, keepalive) before
the stack sees them.

## 5. Scheduling (environment)

**The decrypt worker** is a new dispatched unit (`Worker.decryptWorker`,
dispatch symbol `wg_packet_decrypt_worker`). It is queued by
`consume_data` in the NET_RX softirq of the injected datagram, and runs
after that operation's NET_RX section. Its `cond_resched` (`need_resched`)
gets a resched site (receive.c:494) under the existing `condResched`.

**The NAPI poll.** `napi_schedule` in the decrypt worker raises NET_RX
without waking ksoftirqd. The softirq runs at the next `local_bh_enable`,
which is the worker's next `ptr_ring_consume_bh`, or at an interrupt exit
before that. Either way it runs **inside the decrypt worker's section**, as
a nested NET_RX section.
- The mirror gives the decrypt worker a `softirq` hook at the loop head. If
  the next record starts a NET_RX section and a NAPI poll is pending, it
  runs `rxPoll` in that section (`runWorker .netRx`).
- An interrupt-exit run that leaves no records in between is
  indistinguishable from the loop-head run, and equivalent.
- A pending poll still unrun at the worker's end is consumed at the stop,
  under the same rule.
- This replaces the lax `skipCut` of NET_RX pairs (review finding 2) **for
  the receive path**. The loopback delivery of wg0's own transmissions keeps
  its cut until it, too, has an exact bracket, which is in scope here as a
  stretch goal.

**Ordering checks.** Section records already order the decrypt worker
against the encrypt and tx workers. For example, a received data message
that confirms a session flushes staged packets, which queues the encrypt
worker from inside NET_RX inside the decrypt worker. The scheduler handles
it as in D1, and a missing case fails as a hidden mismatch.

## 6. Harness

- **`harness/noise.py`:**
  - `data_message(keys, receiver_index, counter, plaintext)`: padding as
    the sender would pad, AEAD;
  - builders for inner IPv4/IPv6 UDP packets, including the dishonest
    variants: version, `tot_len` too small or too large, `payload_len` too
    large, a source outside the allowed IPs, empty (keepalive).
  - Tests anchor it to the mirror's `#guard` vectors and to Linux (A1).
- **The guest:**
  - `wg_xmit` gains a payload (wire format: the existing op with a payload
    field);
  - `IPV6_AUTOFLOWLABEL = 0` on `SEND_FD`, before the window;
  - `wg_observe` additionally reports `rx_errors`, `rx_frame_errors`,
    `rx_length_errors` and the sender inbox's inner datagrams (already
    drained).
- **The generator** (steered-handshake class, extended) produces, after a
  completed session:
  - payload transmissions of sizes 1, 15, 16, 17, `mtu - hdr - 32 ± 1` and
    the maximum, so padding covers every case of
    `min(mtu, ALIGN(len, 16))`;
  - staged-before-session flushes, with 1 to 4 packets;
  - injected data messages with counter patterns: in order, a duplicate, a
    reordered packet within the window, older than the window, a jump over
    `COUNTER_BITS_TOTAL`, and `REJECT_AFTER_MESSAGES - 1` / `REJECT_AFTER_MESSAGES`;
  - tampered tags, wrong key indices, keepalives, and dishonest inner
    packets;
  - respond-then-data: the responder's confirmation.
- **The corpus:** `corpus/wireguard/d2_*.json`, one trace per target class,
  frozen.

## 7. Evidence (what D2 must show)

- The full check agrees, with D2 traces in the corpus and the generated
  suite.
- **D2 mutants**, rejected on the corpus:
  - the counter window off by one;
  - the bitmap index unmasked;
  - `++their_counter` dropped;
  - padding with `ALIGN` ignoring the MTU;
  - the checksum not completed;
  - `lookup_src` using the destination;
  - `received_with_keypair` not promoting;
  - `rx_bytes` counting the trimmed length;
  - keepalive not detected;
  - `ds` taken from the inner TOS;
  - the decrypt worker's `DEAD` state treated as `CRYPTED`;
  - the nonce not incremented per packet in a list.
- The environment facts of section 2 (id 0, flow label 0, the partial
  checksum, dst MTU) are checked by the A1 bytes. A deliberately wrong
  environment, a negative control with id ≠ 0, must be rejected.
- Section records order the decrypt worker and the NAPI poll. A control
  that runs the poll outside the decrypt worker must be rejected.

## 8. Out of scope (fail-noisy), and why

| Item | Why it waits |
|---|---|
| Timer firing (keepalive, retransmit, new handshake, zeroing keys) | D3: timer sections and a "fire now" control |
| Key expiry arms (`REJECT_AFTER_TIME`, rekey after time) | Reaching them needs clock steering with monotonic consistency, which belongs with D3's time control |
| `REKEY_AFTER_MESSAGES` / `REJECT_AFTER_MESSAGES` on **send** | 2^60 messages are unreachable without constructing state. The receive-side counter limit is reachable, because the counter is chosen by the sender |
| Full queues (`-ENOSPC`, `-EPIPE`), the ring at 1024 | A bulk-traffic stage |
| Fragmentation, GSO | Fragment ids are jiffies-derived, which is a debt |
| Inner packets the stack drops (non-local, closed port) | `ip_error`'s ICMP is rate-limited; an environment model is needed |
| Cookies, under load, the ratelimiter | A DoS stage |
| Allocation failures | Roadmap step 5 |
| SMP, parallel crypt workers, `prev_queue` races | Research debt |

## 9. Risk assessment

- **Low** for the mirror code. It is C-shaped, and every value is
  observable: ciphertext bytes, inner datagrams, counters.
- **Medium** for the environment's inner packet (section 2). It is checked
  by bytes, and a wrong fact fails noisily. Each fact is verifiable once
  with one trace before the generator relies on it.
- **Medium** for the NAPI scheduling (section 5). It is checked by section
  records. The worry is a softirq run the mirror attributes to the wrong
  place with no records in between. That is equivalent only if no state the
  poll reads changes between the two candidate points; on these paths the
  decrypt worker's remaining work is the next ring poll.

## 10. Execution

Parallel streams, as in D1, coordinated in worktrees, with one signoff at
the end (the merge only, since there is no kernel change):
- **A, transmit:** environment inner packet, fixture payload and flow label,
  mirror widening (section 3).
- **B, receive:** mirror receive path (section 4), the decrypt worker and
  NAPI scheduling (section 5).
- **C, harness:** noise.py data messages and inner packets, the generator,
  the corpus, guest observation of receive stats and inner datagrams.

An interface commit first fixes: `Worker.decryptWorker` and its sites,
`Peer.rxQueue`, `Device.decryptQueue`, `Keypair.receivingCounter` (counter
and backtrack), `DataPacket` with bytes, `csum` and `mtu`, and the wire
format of `wg_xmit`'s payload.
