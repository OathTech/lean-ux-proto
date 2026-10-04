#!/usr/bin/env python3
"""Writes the stage D2 (data plane) traces into corpus/wireguard
(docs/2026-10-04-d2-data-plane.md; sprint spec docs/2026-10-04-d2-sprint.md,
section 4, stream C).

Every trace first completes a session with steered hidden inputs, as the D1
traces do (scripts/wg-d1-corpus.py): wg0 initiates (the ephemeral draw, the
tai64n clock read and the index draw are steered) and the peer's response is
computed offline; or, for respond-then-data, the peer initiates and wg0's
response ephemeral and index draws are steered. From the session keys
(harness/noise.py, Session) this script builds:
- transmit: `wg_xmit` operations with payloads (the packet object's optional
  `payload`), whose ciphertext at the fixture's sender is predictable with
  noise.wg0_data;
- receive: message_data messages the peer sends to wg0, carrying inner
  IPv4/IPv6 UDP packets for wg0's address and the sender's port, honest or
  dishonest.

Each trace's comment (TRACES below) says what Linux does. The output is
deterministic: rerunning this script reproduces the committed files.

The guest's waits bound a trace: 0.4 s per wg_inject and wg_observe, 0.1 s
per wg_up, wg_set and wg_xmit, within evaluator/generate.py's
WAIT_BUDGET_SECONDS after wg_up. The receive traces therefore observe once,
at the end; the observation drains every queued datagram.
"""
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness import noise  # noqa: E402
from evaluator.generate import WAIT_BUDGET_SECONDS, wait_after_up  # noqa: E402

_spec = importlib.util.spec_from_file_location("wg_d1_corpus", ROOT / "scripts" / "wg-d1-corpus.py")
d1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d1)

DEVICE, PEER, PORT, LISTENER = d1.DEVICE, d1.PEER, d1.PORT, d1.LISTENER
OBSERVE, GET = d1.OBSERVE, d1.GET
inject = d1.inject

# The peer's allowed IPs: 10.0.0.0/8 (which contains wg0's own 10.255.254.1)
# and 2001:db8::/32. Inner sources come from these ranges minus wg0's local
# addresses; transmit destinations are non-local addresses inside them.
ALLOWED = [{"family": 4, "addr": "0a000000", "cidr": 8},
           {"family": 6, "addr": "20010db8000000000000000000000000", "cidr": 32}]
SRC4 = bytes([10, 0, 0, 2])
SRC6 = bytes.fromhex("20010db8000000000000000000000002")
OUTSIDE4 = bytes([192, 168, 0, 2])                               # in no peer's allowed IPs
OUTSIDE6 = bytes.fromhex("20010db9000000000000000000000002")
DST4 = bytes([10, 0, 0, 1])
DST6 = bytes.fromhex("20010db8000000000000000000000001")
INNER_SPORT = 12345

# Respond-then-data: the peer's initiation, wg0's steered response draws.
PEER_INIT_EPHEMERAL = b"\x46" * 32
PEER_INIT_INDEX = 0x0badcafe
RESP_EPHEMERAL = d1.RESP_EPHEMERAL
INDEX_RESPONDER_SIDE = d1.INDEX_RESPONDER_SIDE

SESSION = d1.EXPECT_SESSION
DATA = ["wg_packet_receive.data=1", "validate_header_len.data=1", "wg_packet_consume_data.no_keypair=0"]
DATA_SENT = ["wg_packet_create_data_done.data_sent=1", "encrypt_packet.checksum_partial=1"]


def payload(n, seed=0):
    return bytes((seed * 31 + 7 * k + 1) % 256 for k in range(n))


def xmit(family, dst, data):
    return {"op": "wg_xmit", "packet": {"family": family, "dst": dst.hex(), "payload": data.hex()}}


def peer_config(keepalive=True):
    p = {"public_key": d1.key(noise.public_key(PEER)), "allowed_ips": ALLOWED, "endpoint": LISTENER}
    if keepalive:
        p["keepalive"] = 25
    return p


def setup(keepalive=True):
    return [{"op": "wg_set", "config": {"private_key": d1.key(DEVICE), "listen_port": PORT,
                                        "peers": [peer_config(keepalive)]}},
            {"op": "wg_up"}]


def initiator():
    """wg0 initiates (D1's steered values); the peer responds. Returns the
    response message, wg0's session and the steering schedule."""
    init = d1.wg0_initiation()
    response = d1.respond(init)
    return response.message, noise.initiator_session(response), d1.steer_initiation()


def after_session(*ops, keepalive=True):
    """wg_up stages a keepalive and sends the initiation; the response
    completes the session, and the keepalive goes out with counter 0
    (D1's d1_basic). Then `ops`, one observation, and a dump."""
    message, session, steer = initiator()
    return setup(keepalive) + [OBSERVE, inject(message), *ops, OBSERVE, GET], session, steer


def staged_flush(packets):
    """No persistent keepalive, so wg_up sends nothing. The first wg_xmit
    stages its packet and queues the initiation (steered); later ones stage
    behind it, the initiation rate-limited (REKEY_TIMEOUT). The response
    completes the session and the response arm's wg_packet_send_keepalive
    finds the staged queue non-empty, so it adds no keepalive: the staged
    packets are flushed as one list with counters 0..n-1."""
    message, session, steer = initiator()
    ops = setup(keepalive=False) + [xmit(*p) for p in packets] + [OBSERVE, inject(message), OBSERVE, GET]
    return ops, steer, SESSION + ["wg_packet_send_staged_packets.no_keypair=1"] + DATA_SENT


def to_wg0(session, counter, inner, **kw):
    return inject(session.to_wg0(counter, inner, **kw))


def inner4(text, **kw):
    return noise.to_wg0(4, kw.pop("src", SRC4), text.encode(), sport=INNER_SPORT, **kw)


def padded_len(plaintext):
    return len(plaintext) + noise.padding(len(plaintext))


def inner6(text, **kw):
    return noise.to_wg0(6, kw.pop("src", SRC6), text.encode(), sport=INNER_SPORT, **kw)


def receive(build, expect):
    """A receive trace after an initiator session: `build(session)` gives
    the injected operations."""
    message, session, steer = initiator()
    ops = setup() + [OBSERVE, inject(message), *build(session), OBSERVE, GET]
    return ops, steer, SESSION + DATA + expect


def respond_then_data(stage=False):
    """The peer initiates; wg0 responds with steered draws (resp_ephemeral,
    then index_draw), holding the new keypair as `next`. The peer's first
    data message (counter 0) confirms it: wg_noise_received_with_keypair
    promotes next to current, then timers_handshake_complete and
    send_staged_packets. With `stage`, a wg_xmit before the confirmation
    finds no current keypair: the packet is staged and the initiation it
    queues is rate-limited (the response set last_sent_handshake), so the
    confirmation flushes it under the new keypair (counter 0, to the peer's
    sender index). The endpoint is the sender's, learned from the
    initiation, and receives the response and the data."""
    theirs = noise.initiation(noise.public_key(DEVICE), PEER, PEER_INIT_EPHEMERAL, noise.tai64n(1, 0), PEER_INIT_INDEX)
    session = noise.responder_session(noise.wg0_response(theirs, DEVICE, RESP_EPHEMERAL, None, INDEX_RESPONDER_SIDE))
    ops = [{"op": "wg_set", "config": {"private_key": d1.key(DEVICE), "listen_port": PORT,
                                        "peers": [peer_config(keepalive=False)]}},
           {"op": "wg_up"}, inject(theirs)]
    if stage:
        ops.append(xmit(4, DST4, payload(48, 9)))
    ops += [to_wg0(session, 0, inner4("confirm")), OBSERVE, GET]
    steer = [["resp_ephemeral", RESP_EPHEMERAL.hex()], ["index_draw", d1.le32(INDEX_RESPONDER_SIDE)]]
    expect = ["wg_receive_handshake_packet.initiation=1", "add_new_keypair.initiator=0"] + DATA
    if stage:
        expect += ["wg_packet_send_staged_packets.no_keypair=1", "wg_packet_send_staged_packets.no_keypair=0"] + DATA_SENT
    return ops, steer, expect


R = noise.REJECT_AFTER_MESSAGES
N = 10000   # the window boundary pair's highest accepted counter


def traces():
    xmit_session, _, steer = after_session(xmit(4, DST4, payload(64, 1)), xmit(6, DST6, payload(33, 2)))
    small, _, _ = after_session(*[xmit(4, DST4, payload(n, n)) for n in (1, 15, 16, 17, 20)])
    mtu, _, _ = after_session(*[xmit(4, DST4, payload(n, n)) for n in (1376, 1377, 1391, 1392)],
                              xmit(6, DST6, payload(1372, 3)))
    out = {
        # Transmit after the session: an IPv4 and an IPv6 payload, encrypted
        # with counters 1 and 2 (the keepalive took 0), each completing its
        # UDP checksum (CHECKSUM_PARTIAL); the first data_sent arms the
        # new-handshake timer with a jitter draw.
        "d2_xmit_after_session": (xmit_session, steer,
                                  SESSION + DATA_SENT + ["wg_timers_data_sent.not_pending=1"]),
        # Staged before the session and flushed by it: one packet; then four
        # (both families, padding 3, 0, 3 and 4 bytes) in one list.
        "d2_staged_flush_1": staged_flush([(4, DST4, payload(20, 4))]),
        "d2_staged_flush_4": staged_flush([(4, DST4, payload(1, 5)), (6, DST6, payload(100, 6)),
                                           (4, DST4, payload(4, 7)), (4, DST4, payload(16, 8))]),
        # Padding to ALIGN(len, 16): IPv4 payloads 1, 15, 16, 17 and 20 are
        # inner lengths 29, 43, 44, 45 and 48 (padding 3, 5, 4, 3 and 0).
        "d2_padding_small": (small, steer, SESSION + DATA_SENT),
        # The MTU clamp: inner lengths 1404 and 1405 pad to 1408; 1419 and
        # 1420 to 1420, not 1424 (min(mtu, ALIGN)); IPv6 payload 1372 is
        # inner length 1420. Each message is 32 bytes longer than its
        # padded plaintext (1452 at most).
        "d2_padding_mtu": (mtu, steer, SESSION + DATA_SENT),
        # In-order data: counters 0, 1, 2 with IPv4 UDP datagrams from
        # 10.0.0.2:12345, each delivered to the sender socket (port 51998).
        # The first arms the send-keepalive timer; the next two find it
        # pending (no transmit between) and set need_another_keepalive.
        "d2_rx_in_order": receive(lambda s: [to_wg0(s, c, inner4(f"in order {c}")) for c in range(3)],
                                  ["wg_timers_data_received.not_pending=1", "wg_timers_data_received.not_pending=0"]),
        # A keepalive (empty plaintext, no padding): rx_bytes grows by 32,
        # nothing is delivered and data_received is not called.
        "d2_rx_keepalive": receive(lambda s: [to_wg0(s, 0, b"")], []),
        # A duplicate: counter 0 accepted and delivered, then counter 0 again,
        # which decrypts but counter_validate rejects (the bit is set);
        # nothing more is delivered.
        "d2_rx_duplicate": receive(lambda s: [to_wg0(s, 0, inner4("first")), to_wg0(s, 0, inner4("again"))],
                                   ["wg_timers_data_received.not_pending=1"]),
        # The window boundary pair: after accepting N = 10000 (the counter is
        # then N + 1), N - 8128 is accepted (8128 + N - 8127 is not below
        # N + 1) and N - 8129 rejected (8128 + N - 8128 is). Two datagrams
        # are delivered.
        "d2_rx_window_boundary": receive(lambda s: [to_wg0(s, N, inner4(f"n {N}")),
                                                    to_wg0(s, N - 8128, inner4(f"n {N - 8128}")),
                                                    to_wg0(s, N - 8129, inner4(f"n {N - 8129}"))],
                                         ["wg_timers_data_received.not_pending=1"]),
        # A tampered tag: decryption fails, the packet is DEAD and dropped in
        # the poll without counter_validate; the same counter (0) is then
        # accepted with a valid tag and delivered.
        "d2_rx_tampered_tag": receive(lambda s: [to_wg0(s, 0, inner4("tampered"), tamper=True),
                                                 to_wg0(s, 0, inner4("valid"))],
                                      ["wg_timers_data_received.not_pending=1"]),
        # Dishonest type (rx_errors and rx_frame_errors): version 5 in 20+
        # bytes; 10 bytes (padded to 16, shorter than an IPv4 header);
        # version 6 in 30 bytes (padded to 32, shorter than an IPv6 header).
        "d2_rx_dishonest_type": receive(lambda s: [to_wg0(s, 0, inner4("v5", version=5)),
                                                   to_wg0(s, 1, b"\x45" + bytes(9)),
                                                   to_wg0(s, 2, b"\x60" + bytes(29))],
                                        ["wg_timers_data_received.not_pending=1"]),
        # Dishonest size (rx_errors and rx_length_errors): IPv4 tot_len 19;
        # IPv4 tot_len one more than the padded plaintext (32 bytes); IPv6
        # payload_len + 40 (140) beyond the padded plaintext (64 bytes).
        "d2_rx_dishonest_size": receive(lambda s: [to_wg0(s, 0, inner4("short", tot_len=19)),
                                                   to_wg0(s, 1, inner4("long", tot_len=padded_len(inner4("long")) + 1)),
                                                   to_wg0(s, 2, inner6("long", payload_len=100))],
                                        ["wg_timers_data_received.not_pending=1"]),
        # Dishonest source (rx_errors and rx_frame_errors): lookup_src finds
        # no peer for 192.168.0.2 or 2001:db9::2; nothing is delivered.
        "d2_rx_dishonest_source": receive(lambda s: [to_wg0(s, 0, inner4("v4", src=OUTSIDE4)),
                                                     to_wg0(s, 1, inner6("v6", src=OUTSIDE6))],
                                          ["wg_timers_data_received.not_pending=1"]),
        # IPv4 delivery: the inner UDP checksum is not verified
        # (CHECKSUM_UNNECESSARY), so correct, wrong and zero checksums are all
        # delivered. The second message comes from [::1]:51998: the endpoint
        # roams to IPv6.
        "d2_rx_deliver_v4": receive(lambda s: [to_wg0(s, 0, inner4("correct")),
                                               inject(s.to_wg0(1, inner4("wrong", checksum="wrong")), family=6),
                                               to_wg0(s, 2, inner4("zero", checksum="zero"))],
                                    ["wg_timers_data_received.not_pending=1"]),
        # IPv6 delivery from 2001:db8::2: a correct and a wrong nonzero
        # checksum are both delivered.
        "d2_rx_deliver_v6": receive(lambda s: [to_wg0(s, 0, inner6("correct")),
                                               to_wg0(s, 1, inner6("wrong", checksum="wrong"))],
                                    ["wg_timers_data_received.not_pending=1"]),
        # The receive-side message limit: REJECT_AFTER_MESSAGES decrypts but
        # counter_validate rejects it; REJECT_AFTER_MESSAGES - 1 is accepted
        # and delivered, leaving the counter at REJECT_AFTER_MESSAGES; then
        # counter 5 is DEAD in decrypt_packet (the counter limit), which
        # invalidates the receiving key.
        "d2_rx_reject_after_messages": receive(lambda s: [to_wg0(s, R, inner4("limit")),
                                                          to_wg0(s, R - 1, inner4("limit - 1")),
                                                          to_wg0(s, 5, inner4("after"))],
                                               ["wg_timers_data_received.not_pending=1"]),
        # The responder's confirmation: the first data message promotes next
        # to current; its datagram is delivered.
        "d2_respond_then_data": respond_then_data(),
        # The confirmation flushes a packet staged while only `next` existed.
        "d2_respond_stage_then_data": respond_then_data(stage=True),
    }
    result = {}
    for name, (ops, steer, expect) in out.items():
        if wait_after_up(ops) > WAIT_BUDGET_SECONDS:
            raise AssertionError(f"{name} exceeds the guest's wait budget")
        if len(expect) > 16:
            raise AssertionError(f"{name}: at most 16 expected outcomes")
        result[name] = {"version": 1, "id": name, "ops": ops, "steer": steer, "expect": list(dict.fromkeys(expect))}
    return result


def main():
    out = ROOT / "corpus" / "wireguard"
    written = traces()
    for name, trace in written.items():
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
    print(f"wrote {len(written)} traces to {out}")


if __name__ == "__main__":
    main()
