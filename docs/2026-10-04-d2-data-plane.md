# D2: the WireGuard data plane — design, 2026-10-04

Status: **revised after the audit (section 11)** [USER 2026-10-04: the sequence D2 data plane, then
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
  - **Fixture change:** `IP_MTU_DISCOVER = IP_PMTUDISC_DO` on `SEND_FD`,
    before the window.
  - **Why id is 0, given that change:** under the default
    `IP_PMTUDISC_WANT`, `__ip_make_skb` sets
    `skb->ignore_df = ip_sk_ignore_df(sk)`, which is true
    (`ip_output.c:1435`, `ip.h:462-467`). `ip_select_ident_segs` then draws
    the id from the jiffies-based ident generator even with DF set
    (`ip.h:559-589`). With `DO`, DF is set unconditionally, `ignore_df` is
    0 and the socket is unconnected, so the id is 0.
  - **Side effect, wanted:** an oversize payload fails `sendto` with
    `-EMSGSIZE` instead of fragmenting.
  - **Verify:** the A1 bytes check this. The control: running with `WANT`
    must be rejected by the bytes.
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
  - `skb_checksum_help` is a cut. Its output is computed by an environment
    function: the folded checksum over the transport bytes, starting from
    the stored `~pseudo`, written as `csum_fold(csum) ?: CSUM_MANGLED_0`
    (`dev.c:3425`), so 0 becomes 0xFFFF. Only its failure is an `envOk`
    site.
- **IPv6 destinations.** wg0 (`ARPHRD_NONE`) gets a random link-local
  address when it comes up. A link-local destination would select it as the
  source, so `fe80::/10` destinations are `unsupported` in `Env.xmitPacket`
  and excluded by the generator.
- **Payload.** The `wg_xmit` operation gains a payload (1 to 1392 bytes for
  IPv4, 1 to 1372 for IPv6), so the packet is at most the MTU, 1420.
  - Larger payloads get `-EMSGSIZE` with `IP_PMTUDISC_DO` on IPv4; the
    environment makes them `unsupported` on both families.
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
- `wg_timers_data_sent`, today `unsupported` (`timers.c:145-150`):
  - if `!timer_pending(&timer_new_handshake)`, it arms the timer with a
    jitter drawn by `get_random_u32_below`;
  - the draw is a **mirror site**, `.newHandshakeJitter` (timers.c:150, 1
    byte), consumed with `hidden` exactly on that branch;
  - `Env.timing.timerMayExpire` must say the timer cannot fire within the
    trace (15 s plus jitter, against the guest's 4 s bound).
  - Timer firing stays out of the domain until D3.
- **Timer state is mirror state.** Pending-ness is read on modeled paths, so
  `Peer` gains:
  - `timerNewHandshakePending`: set by `data_sent`, cleared by
    `any_authenticated_packet_received`, which also runs on the handshake
    receive path, so the handshake mirror clears it too;
  - `timerSendKeepalivePending`: set by `data_received`, cleared by
    `any_authenticated_packet_sent`, on every `create_data_done`;
  - `timerNeedAnotherKeepalive`: `data_received`'s else branch, taken when
    two data messages arrive with no transmit between.

  Each is set only under `mod_peer_timer`'s outcome (`netif_running && !is_dead`).
  No timer fires within the 4 s bound, so pending-ness is a function of the
  modeled calls.
- Transmit-side `keep_key_fresh` (`send.c:124-139`) is exercised with
  payloads. Its expiry arm needs clock steering, which is deferred to D3
  (section 8).
- **`wg_xmit` with a session queues crypt work in a system call.** Today
  `Env.requireNoCryptWork` makes that `unsupported`. In D2 the guest waits
  after `wg_xmit` (`QUEUE_WAIT_US`), and the environment runs the encrypt
  and tx workers after the operation, ordered by records. Stream A measures
  whether the wait covers encrypt, tx and loopback on the VM. The dropped
  and opened section counts catch a worker outliving it.

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
  - `if (!keypair) return false`, a constant outcome;
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
  - receive-side `keep_key_fresh` (`receive.c:220-240`). It differs from
    the send side: it returns early on `peer->sent_lastminute_handshake`,
    uses the threshold `REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT`
    (165 s), and sets the flag. `wg_timers_handshake_complete` resets the
    flag (`timers.c:196`). `Peer` gains `sentLastminuteHandshake`;
  - the timer calls, over the timer state of section 3;
  - keepalive (length 0);
  - the dishonest-size and dishonest-type checks;
  - `ip_tunnel_parse_protocol`, whose inline tests have constant outcomes;
  - `INET_ECN_decapsulate`, whose inline decisions all have constant
    outcomes for a not-ECT outer header;
  - `pskb_trim`;
  - `wg_allowedips_lookup_src`, a trie walk on the source, mirroring
    `lookup_dst`;
  - `napi_gro_receive`, which is a cut. The actual delivery happens at
    `napi_complete_done` → `gro_normal_list`, after the poll loop, so the
    environment's delivery cut is placed there;
  - `update_rx_stats(message_data_len(len_before_trim))`;
  - `DEV_STATS_INC` of `rx_errors`, `rx_frame_errors` and
    `rx_length_errors`.

The **delivery of the inner packet** (the GRO, IP and UDP stacks) is a cut.
The environment decides its outcome **fail-closed**, by an exact predicate:
- **IPv4, delivered** when all of these hold:
  - ihl 5 (no options), a correct header checksum, `tot_len` equal to the
    trimmed length, protocol 17;
  - UDP `ulen = tot_len - 20`, at least 8;
  - destination `10.255.254.1`, destination port 51998;
  - the source is not a local, loopback, zeronet, multicast or limited
    broadcast address. The martian checks in `ip_route_input_slow` and
    `fib_validate_source` drop a local source. The fixture's allowed IPs,
    `10.0.0.0/8`, contain wg0's own `10.255.254.1`, so the generator draws
    sources from the allowed range minus local addresses.

  The inner UDP checksum is **not verified**: wg sets
  `CHECKSUM_UNNECESSARY` with `csum_level = ~0`. So any checksum is
  delivered on IPv4.
- **IPv6, delivered** when all of these hold:
  - no extension headers, next header 17;
  - `payload_len + 40` equal to the trimmed length, UDP length equal to
    `payload_len`;
  - destination `fd00:ffff::1`, port 51998;
  - a source that is not loopback or multicast. A local source is accepted
    on IPv6, an asymmetry stated in the environment;
  - a **nonzero** UDP checksum: zero is dropped in `__udp6_lib_rcv`
    (`!uh->check && !udp_get_no_check6_rx(sk)`, `udp.c:1066`), while a
    wrong nonzero value is delivered.
- **Everything else is `unsupported`**: other destination ports, other
  protocols (an ICMP echo or a TCP SYN would make the stack reply through
  wg0), UDP to wg0's own listen port (it re-enters `wg_receive`), and
  options or extension headers.

The generator's inner packets are therefore either delivered by this
predicate, or rejected by WireGuard's own checks before the stack sees
them: dishonest type, size or source, or a keepalive.

**Observation.** After an injected message, the peer's endpoint roams to the
fixture's sender (`127.0.0.1:51998` or `[::1]:51998`). So the sender socket
receives both wg0's ciphertexts and the delivered inner datagrams.
`wg_observe` therefore uses `recvfrom` on `SEND_FD` and reports
`(family, source address, source port, length, bytes)`, and the mirror's
`senderInbox` entries carry the same. The inner source address and port are
then observed: they are `lookup_src`'s operand and the fact of delivery.

## 5. Scheduling (environment)

**The decrypt worker** is a new dispatched unit (`Worker.decryptWorker`,
dispatch symbol `wg_packet_decrypt_worker`). It is queued by
`consume_data` in the NET_RX softirq of the injected datagram, and runs
after that operation's NET_RX section. Its `cond_resched` (`need_resched`)
gets a resched site (`receive.c:505`) under the existing `condResched`.

**The NAPI poll.** `napi_schedule` from the decrypt worker (process
context, BH enabled) calls `raise_softirq_irqoff`, because the worker is not
in `net_rx_action` (`dev.c:4668-4669`). With `!in_interrupt()` that wakes
ksoftirqd: `should_wake_ksoftirqd()` is `true` on this non-RT kernel
(`softirq.c:439-442`). There are three placements, all between the worker's
section start and stop:
- **(a) ksoftirqd.** The worker's `cond_resched` (`receive.c:505`) yields to
  ksoftirqd: a resched record (new site `.reschedDecrypt`), then a
  **top-level** NET_RX section run by ksoftirqd (`run_ksoftirqd` →
  `handle_softirqs`), then the worker's final empty poll. With wakeup
  preemption this is probably the common case.
- **(b) Inline.** No switch: the softirq runs at the worker's next
  `spin_unlock_bh` (`ptr_ring_consume_bh` → `__local_bh_enable_ip` →
  `do_softirq`), as a nested section with no resched record.
- **(c) Interrupt exit.** A tick runs it at irq exit, which is
  indistinguishable from (b) when no records lie between.

The mirror gives the decrypt worker a `softirq` hook at the loop head. It
accepts a preceding resched record (case a; `Env.condResched` already stops
at a NET_RX start). If the next record starts a NET_RX section and a NAPI
poll is pending, it runs `rxPoll` in that section (`runWorker .netRx`).
- `Env.sectionOf`'s comment ("NET_RX runs nested where raised") is
  corrected: NET_RX may also be ksoftirqd's.
- Encrypt and tx work queued from inside that NET_RX (the responder's
  confirmation flush) may run before the decrypt worker's stop. That is the
  deferred-stop path from D1.
- **Evidence requirement:** the D2 corpus must contain at least one trace in
  order (a) and one in order (b). The control "the poll runs outside the
  worker" is inconclusive otherwise, as D1-M15 nearly was. Whether ksoftirqd's
  NET_RX section opens and is accounted by `check.py` (a top-level softirq
  section between a task section's start and stop) is verified first.

This replaces the lax `skipCut` of NET_RX pairs (review finding 2) **for
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
  - `IP_MTU_DISCOVER = IP_PMTUDISC_DO` on `SEND_FD`, before the window;
  - `wg_observe` reports `rx_frame_errors` and `rx_length_errors`
    (`rx_errors` always moves with one of them, so it adds nothing), and
    the sender inbox via `recvfrom` with its source (section 4).
- **The generator** (steered-handshake class, extended) produces, after a
  completed session:
  - payload transmissions of sizes 1, 15, 16 and 17, and inner lengths
    1404, 1405, 1419 and 1420 (IPv4 payloads 1376, 1377, 1391, 1392), so
    padding covers `ALIGN` and the `min(mtu, …)` clamp, which differs only
    in (1404, 1420];
  - staged-before-session flushes, with 1 to 4 packets;
  - injected data messages with counter patterns: in order, a duplicate, a
    reordered packet within the window, older than the window, a jump over
    `COUNTER_BITS_TOTAL`, `REJECT_AFTER_MESSAGES - 1` /
    `REJECT_AFTER_MESSAGES`, and the window boundary pair: after accepting
    N, N − 8128 is accepted and N − 8129 rejected;
  - tampered tags, wrong key indices, keepalives, and dishonest inner
    packets;
  - respond-then-data: the responder's confirmation. The data message is
    built offline under keys that depend on wg0's response ephemeral and
    keypair index, so this class steers `resp_ephemeral` and `index_draw`
    (both already steerable, as in D1's respond-then-initiate).
  - inner sources from the allowed range minus local addresses, and no
    `fe80::/10` transmit destinations.
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
  - the decrypt worker's `DEAD` state treated as `CRYPTED`;
  - the nonce not incremented per packet in a list.
- The environment facts of section 2 (id 0, flow label 0, the partial
  checksum, dst MTU) are checked by the A1 bytes. **Control:** the fixture
  without `IP_PMTUDISC_DO` (ids drawn) must be rejected by the bytes.
- `ds` from the inner TOS is not a mutant here: the fixture's TOS is 0, and
  the outer TOS is in no observed bytes.
- Section records order the decrypt worker and the NAPI poll, with the
  corpus exhibiting orders (a) and (b) of section 5. A control that runs the
  poll outside the worker must be rejected.

## 8. Out of scope (fail-noisy), and why

| Item | Why it waits |
|---|---|
| Timer firing (keepalive, retransmit, new handshake, zeroing keys) | D3: timer sections and a "fire now" control |
| Key expiry arms (`REJECT_AFTER_TIME`, rekey after time) | Reaching them needs clock steering with monotonic consistency, which belongs with D3's time control |
| `REKEY_AFTER_MESSAGES` / `REJECT_AFTER_MESSAGES` on **send** | 2^60 messages are unreachable without constructing state. The receive-side counter limit is reachable, because the counter is chosen by the sender |
| Full queues (`-ENOSPC`, `-EPIPE`), the ring at 1024 | A bulk-traffic stage |
| More than one item in a crypt ring per worker run | Kept from D1. The interrupt-exit equivalence of section 5 relies on it |
| `wg_xmit`'s staged trim (`> MAX_STAGED_PACKETS`) | 129 transmissions × the 100 ms wait exceed the 4 s bound; it stays `unsupported` |
| Inner packets other than the exact predicate of section 4 | Stack replies (ICMP, TCP), re-entry into wg_receive, options |
| Link-local IPv6 transmit destinations | wg0's link-local address is random |
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

## 11. Audit record [AGENT 2026-10-04]

An independent Fable audit checked the draft against the kernel source. Two
claims were re-verified directly: `ip_sk_ignore_df` (`ip.h:462-467`) and
`____napi_schedule` → `raise_softirq_irqoff` (`dev.c:4668-4669`). The
findings and their fixes:
- **C1 (critical).** IPv4 id 0 was false under `IP_PMTUDISC_WANT`.
  - Fix: `IP_PMTUDISC_DO` on the sender (section 2).
- **M1.** `napi_schedule` wakes ksoftirqd, giving three placements.
  - Fix: section 5, with `.reschedDecrypt` at `receive.c:505` and corpus
    evidence for orders (a) and (b).
- **M2.** `wg_timers_data_sent` draws a jitter.
  - Fix: a mirror site, `.newHandshakeJitter`.
- **M3.** Timer pending state is read on modeled paths.
  - Fix: timer state in `Peer`.
- **M4.** Receive-side `keep_key_fresh` has its own conditions.
  - Fix: `sentLastminuteHandshake`.
- **M5.** The delivery rule was fail-open; a local inner source is dropped
  by Linux.
  - Fix: the exact predicate, with everything else `unsupported`.
- **M6.** Roaming mixes ciphertexts and inner datagrams in the sender inbox.
  - Fix: `recvfrom` with the source.
- **M7.** The responder data class needs steering.
  - Fix: steer `resp_ephemeral` and `index_draw`.
- **Minor.**
  - `CSUM_MANGLED_0`;
  - link-local sources;
  - the `ds` mutant dropped;
  - padding and window boundary sizes;
  - the staged trim and the one-item ring listed as out of scope;
  - delivery placed at `napi_complete_done`;
  - constant-outcome choice points listed.

Every finding but M5 would have surfaced noisily, as a hidden or
control-flow mismatch or as bytes. M5 was the one fail-open item. None
needs a kernel change.

