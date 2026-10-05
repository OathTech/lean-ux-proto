#!/usr/bin/env python3
"""Writes stream B's D2 receive probe traces (corpus/wireguard/rx_*.json).

Each trace first completes a session as D1 does (scripts/wg-d1-corpus.py):
wg0 initiates with steered values and the peer's response comes from the
fixture's sender. The peer then sends `message_data`s under the session's
keys (wg0's receiving key is the initiator's receiving key), injected from
the fixture's sender. One trace (rx_respond_then_data) has wg0 respond, so
its data message confirms wg0's next keypair.

These are stream B's own checks of the receive path (docs/2026-10-04-d2-sprint.md,
section 4); stream C's frozen corpus (d2_*.json) is separate. The data
messages are built here from harness/noise.py's AEAD (stream C's helpers
were not yet available); the output is deterministic.
"""
import json
import struct
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
from harness import noise  # noqa: E402

d1 = __import__("wg-d1-corpus")

WG0_V4 = bytes([10, 255, 254, 1])
WG0_V6 = bytes.fromhex("fd00ffff000000000000000000000001")
SENDER_PORT = 51998
INNER_SRC = bytes([10, 1, 2, 3])       # in the peer's allowed 10.0.0.0/8, not local
INNER_SPORT = 4242
INNER_SRC6 = bytes.fromhex("fd000000000000000000000000000002")
REJECT_AFTER_MESSAGES = (2**64 - 1) - (8192 - 64) - 1


def ip_checksum(header):
    s = sum(struct.unpack(f"!{len(header) // 2}H", header))
    while s >> 16:
        s = (s & 0xffff) + (s >> 16)
    return (~s) & 0xffff


def ipv4_udp(payload, src=INNER_SRC, dst=WG0_V4, sport=INNER_SPORT, dport=SENDER_PORT, *,
             version=4, tot_len=None, udp_len=None, checksum_ok=True):
    """An inner IPv4 UDP datagram (no options, DF, id 0, TTL 64); the UDP
    checksum is left zero (not verified on IPv4: wg sets CHECKSUM_UNNECESSARY)."""
    total = 20 + 8 + len(payload)
    tl = total if tot_len is None else tot_len
    ul = 8 + len(payload) if udp_len is None else udp_len
    header = struct.pack("!BBHHHBBH4s4s", (version << 4) | 5, 0, tl, 0, 0x4000, 64, 17, 0, src, dst)
    csum = ip_checksum(header) if checksum_ok else 0x1234
    header = header[:10] + struct.pack("!H", csum) + header[12:]
    return header + struct.pack("!HHHH", sport, dport, ul, 0) + payload


def ipv6_udp(payload, src, dst=WG0_V6, sport=INNER_SPORT, dport=SENDER_PORT, *, udp_checksum=0xbeef):
    plen = 8 + len(payload)
    header = struct.pack("!IHBB16s16s", 6 << 28, plen, 17, 64, src, dst)
    return header + struct.pack("!HHHH", sport, dport, plen, udp_checksum) + payload


def padded(plaintext, mtu=1420):
    """The sender's padding (calculate_skb_padding): ALIGN(len, 16), clamped
    to the MTU."""
    if not plaintext:
        return plaintext
    size = min(mtu, (len(plaintext) + 15) // 16 * 16)
    return plaintext + bytes(size - len(plaintext))


# Payloads are at least 4 bytes: the observation reports a reply's first
# word as its type only from 4 bytes on (harness/guest.c), which the
# mirror's observe does not yet follow for shorter ones (stream A owns it).
def data_message(key, receiver_index, counter, plaintext, *, tamper=False, pad=True):
    body = padded(plaintext) if pad else plaintext
    sealed = noise.aead_encrypt(key, bytes(4) + struct.pack("<Q", counter), body, b"")
    if tamper:
        sealed = sealed[:-1] + bytes([sealed[-1] ^ 1])
    return struct.pack("<IIQ", 4, receiver_index, counter) + sealed


def session():
    init = d1.wg0_initiation()
    resp = d1.respond(init)
    # wg0 is the initiator: it receives with the initiator's receiving key,
    # under its own index (the initiation's sender index)
    return resp, resp.initiator_receiving, d1.INDEX


def data_trace(messages, extra=(), family=4, **peer_extra):
    resp, _, _ = session()
    # every injection waits 0.4 s: one observation at the end keeps the
    # longest trace inside the guest's 4 s bound
    ops = d1.setup(**peer_extra) + [d1.OBSERVE, d1.inject(resp.message)]
    ops += [d1.inject(m, family=family) for m in messages]
    ops += [d1.OBSERVE] + list(extra) + [d1.GET]
    return ops, d1.steer_initiation()


def respond_then_data():
    """The peer initiates (from the sender); wg0 responds with a steered
    ephemeral and index, holding the new keypair as next; the peer's first
    data message confirms it (received_with_keypair promotes it)."""
    theirs = noise.initiation(noise.public_key(d1.DEVICE), d1.PEER, d1.PEER_EPHEMERAL, noise.tai64n(1, 0), 0x0badcafe)
    ours = noise.response(theirs, d1.DEVICE, noise.clamp(d1.RESP_EPHEMERAL), None, d1.INDEX_RESPONDER_SIDE,
                          initiator_public=noise.public_key(d1.PEER))
    # the peer (initiator) sends with the initiator's sending key to wg0's index
    msg = data_message(ours.initiator_sending, d1.INDEX_RESPONDER_SIDE, 0, ipv4_udp(b"confirm"))
    ops = [{"op": "wg_set", "config": {"private_key": d1.key(d1.DEVICE), "listen_port": d1.PORT,
                                       "peers": [d1.peer()]}},
           {"op": "wg_up"}, d1.inject(theirs), d1.OBSERVE, d1.inject(msg), d1.OBSERVE, d1.GET]
    steer = [["resp_ephemeral", d1.RESP_EPHEMERAL.hex()], ["index_draw", d1.le32(d1.INDEX_RESPONDER_SIDE)]]
    return ops, steer


def traces():
    _, key, index = session()
    v4 = lambda payload, **kw: ipv4_udp(payload, **kw)
    n = 8200
    out = {
        # a keepalive (empty plaintext)
        "rx_keepalive": data_trace([data_message(key, index, 0, b"")]),
        # two in-order data messages with delivered inner datagrams
        "rx_in_order": data_trace([data_message(key, index, 0, v4(b"hello")),
                                   data_message(key, index, 1, v4(b"world, again"))]),
        # the same counter twice: the second fails counter_validate
        "rx_duplicate": data_trace([data_message(key, index, 0, v4(b"once")),
                                    data_message(key, index, 0, v4(b"once"))]),
        # after accepting N, N - 8128 is accepted and N - 8129 rejected
        "rx_window": data_trace([data_message(key, index, n, b""),
                                 data_message(key, index, n - 8128, b""),
                                 data_message(key, index, n - 8129, b"")]),
        # a flipped tag: decryption fails, the packet is DEAD
        "rx_tampered": data_trace([data_message(key, index, 0, v4(b"tampered"), tamper=True)]),
        # an inner version 5 header: dishonest type; then fewer than 20 bytes
        "rx_dishonest_type": data_trace([data_message(key, index, 0, v4(b"x", version=5)),
                                         data_message(key, index, 1, b"\x45\x00\x00", pad=False)]),
        # tot_len beyond the packet, then below the header: dishonest size
        "rx_dishonest_size": data_trace([data_message(key, index, 0, v4(b"abc", tot_len=200)),
                                         data_message(key, index, 1, v4(b"abc", tot_len=19))]),
        # a source outside the peer's allowed IPs: dishonest peer
        "rx_dishonest_source": data_trace([data_message(key, index, 0, v4(b"abc", src=bytes([192, 168, 1, 1])))]),
        # an IPv6 inner datagram (the peer has no IPv6 allowed IPs: dishonest peer)
        "rx_v6_unallowed": data_trace([data_message(key, index, 0, ipv6_udp(b"six!", bytes.fromhex(
            "fd000000000000000000000000000002")))]),
        "rx_respond_then_data": respond_then_data(),
        # a duplicate above COUNTER_BITS_TOTAL: the bitmap index wraps (masked)
        "rx_duplicate_high": data_trace([data_message(key, index, 9000, b""),
                                         data_message(key, index, 9000, b"")]),
        # REJECT_AFTER_MESSAGES - 1 is accepted; then decrypt_packet rejects
        # the keypair (counter limit, then invalid)
        "rx_counter_limit": data_trace([data_message(key, index, REJECT_AFTER_MESSAGES - 1, b""),
                                        data_message(key, index, 0, b""),
                                        data_message(key, index, 1, b"")]),
        # a jump over COUNTER_BITS_TOTAL clears the whole bitmap; an older
        # counter within the window is then accepted
        "rx_counter_jump": data_trace([data_message(key, index, 5, b""),
                                       data_message(key, index, 5 + 8192 + 70, b""),
                                       data_message(key, index, 5 + 8192 + 3, b"")]),
        # partial bitmap clears (1 <= top <= 127, review m3), three messages
        # each (the per-trace time bound): 100 (word 1), 160 (word 2: clears
        # one word), 99 (word 1 kept: accepted); and 100, 300 (clears words
        # 2-4), 100 again (word 1 kept: rejected as a duplicate)
        "rx_word_boundary": data_trace([data_message(key, index, c, b"") for c in (100, 160, 99)]),
        "rx_word_clear": data_trace([data_message(key, index, c, b"") for c in (100, 300, 100)]),
        # data from [::1]: the endpoint roams to the sender's IPv6 address
        "rx_roam_v6": data_trace([data_message(key, index, 0, v4(b"from six"))], family=6),
        # an IPv6 inner datagram from an allowed source, delivered
        "rx_v6_delivered": data_trace(
            [data_message(key, index, 0, ipv6_udp(b"six!", INNER_SRC6))],
            allowed_ips=[{"family": 4, "addr": "0a000000", "cidr": 8},
                         {"family": 6, "addr": "fd000000000000000000000000000000", "cidr": 16}]),
    }
    return {name: {"version": 1, "id": name, "ops": ops, "steer": steer} for name, (ops, steer) in out.items()}


def main():
    out = ROOT / "corpus" / "wireguard"
    written = traces()
    for name, trace in written.items():
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
    print(f"wrote {len(written)} traces to {out}")


if __name__ == "__main__":
    main()
