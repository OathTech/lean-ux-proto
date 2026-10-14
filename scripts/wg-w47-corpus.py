#!/usr/bin/env python3
"""Writes the W4 traces (docs/2026-10-06-w4-w7-transmit-bulk.md, sections 6
and 16.1: the kept transmit-shape classes) and the W7 core-tier batches
(section 6, stream B) into corpus/wireguard, and the
three boundary domain controls (section 8) into corpus/w47-controls.
Each W4 class names the WireGuard line, decision or outcome it alone reaches.
Sessions, steering and advances come from the D1-D3 corpus scripts; the
output is deterministic.
    scripts/in-bundle python3 scripts/wg-w47-corpus.py
"""
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from evaluator.generate import HZ, WAIT_BUDGET_SECONDS, fire_advance, wait_after_up  # noqa: E402
from harness.trace import validate_trace  # noqa: E402
from harness import noise  # noqa: E402

_spec = importlib.util.spec_from_file_location("wg_d3_corpus", ROOT / "scripts" / "wg-d3-corpus.py")
d3 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d3)
d2, d1 = d3.d2, d3.d1

OBSERVE, GET, inject, advance, fired = d3.OBSERVE, d3.GET, d3.inject, d3.advance, d3.fired
SESSION = d1.EXPECT_SESSION
DST4 = d2.DST4
PERSISTENT_5 = fire_advance(5 * HZ)   # 1350: the 5 s persistent keepalive fires, nothing else


def xmit(data, gso_size=None, pmtudisc=None):
    packet = {"family": 4, "dst": DST4.hex(), "payload": data.hex()}
    if gso_size:
        packet["gso_size"] = gso_size
    if pmtudisc:
        packet["pmtudisc"] = pmtudisc
    return {"op": "wg_xmit", "packet": packet}


def batch(items, wait_ms):
    return {"op": "wg_batch", "items": items, "wait_ms": wait_ms}


def inject_item(sess, counter, text):
    """A data message (counter `counter`) carrying an inner IPv4 UDP datagram,
    as a batch item to wg0's port."""
    message = sess.to_wg0(counter, d2.inner4(text))
    return {"kind": "inject", "family": 4, "port": d1.PORT,
            "message": message.hex() if isinstance(message, (bytes, bytearray)) else message}


def xmit_item(data):
    return {"kind": "xmit", "packet": {"family": 4, "dst": DST4.hex(), "payload": data.hex()}}


DEQUEUE_MORE = "wg_prev_queue_dequeue.more_remain=1"   # the queue held two or more items (queueing.c:91)


def set_mtu(mtu):
    return {"op": "wg_set_mtu", "mtu": mtu}


def traces():
    out = {}
    # After a session, one IPv4 UDP_SEGMENT datagram of two full-size
    # segments (gso_size 1392, payload 2784): wg_xmit's GSO arm
    # (`.xmitNotGso` false, `.xmitGsoError` false), a two-iteration walk, and
    # encrypt_packet's CHECKSUM_NONE arm; two ciphertexts with ids 0 and 1.
    ops, sess, steer = d3.session(keepalive=5)
    out["w4_gso_4_2"] = (ops + [xmit(d2.payload(2784, 1), 1392), OBSERVE, GET], steer,
                         SESSION + ["wg_xmit.not_gso=0", "wg_xmit.gso_error=0", "wg_xmit.segments_iterate=1",
                                    "encrypt_packet.checksum_partial=0"])
    # No session: two GSO datagrams of 128 eight-byte segments stage 256
    # packets and queue the initiation; a third datagram (one packet) finds
    # 256 > MAX_STAGED_PACKETS and the trim loop drops the oldest 128
    # (tx_dropped 128); the response then flushes the 129 staged packets as
    # 80-byte data messages in one ring item.
    message, sess, steer = d2.initiator()
    out["w4_gso_trim"] = (d2.setup(keepalive=False)
                          + [xmit(d2.payload(1024, 2), 8), xmit(d2.payload(1024, 3), 8), xmit(d2.payload(1, 4)),
                             OBSERVE, inject(message), OBSERVE, GET],
                          steer, SESSION + ["wg_xmit.staged_trim_iter=1", "wg_packet_send_staged_packets.no_keypair=1",
                                            "encrypt_packet.checksum_partial=0"])
    # A host route to the destination with MTU 1300 and an IP_PMTUDISC_PROBE
    # send of a 1420-byte packet: dst_mtu is 1300, so calculate_skb_padding
    # takes `len > mtu` (padding 8); the sender did not fragment (PROBE).
    ops, sess, steer = d3.session(keepalive=5)
    out["w4_route_mtu_probe_4"] = (ops + [xmit(d2.payload(1392, 5), pmtudisc="probe"), OBSERVE, GET], steer,
                                   SESSION + ["calculate_skb_padding.over_mtu=1", "wg_xmit.not_gso=1"],
                                   {"routes": [{"family": 4, "dst": DST4.hex(), "mtu": 1300}]})
    # SIOCSIFMTU 1300 under a session: a 1300-byte packet pads 0 under the
    # device's MTU (12 under a constant 1420), and the persistent keepalive,
    # fired by the advance, reads the MTU at send.c:232.
    ops, sess, steer = d3.session(keepalive=5)
    out["w4_set_mtu_1300"] = (ops + [set_mtu(1300), xmit(d2.payload(1272, 6)), OBSERVE, advance(PERSISTENT_5),
                                     OBSERVE, GET],
                              steer, SESSION + [fired("send_persistent_keepalive"), d3.INTERVAL + "=1"])
    # SIOCSIFMTU 0 under a session (the kernel accepts it; the IPv6 device
    # goes below 1280 and the IPv4 device below 68): the fired keepalive
    # takes calculate_skb_padding's `!mtu` arm; a down and up afterwards take
    # wg_open's `dev_v4` and `dev_v6` false arms, the fixture expecting the
    # kernel's refusals of its addresses and routes. Terminal.
    # The keepalive is turned off before the down, so the up stages nothing
    # and sends no second initiation (whose draws the schedule does not name).
    ops, sess, steer = d3.session(keepalive=5)
    out["w4_set_mtu_0"] = (ops + [set_mtu(0), advance(PERSISTENT_5), OBSERVE, d3.keepalive_off(), {"op": "wg_down"},
                                  {"op": "wg_up"}, OBSERVE, GET],
                           steer, SESSION + [fired("send_persistent_keepalive"), d3.INTERVAL + "=1",
                                             "calculate_skb_padding.no_mtu=1", "wg_open.has_inet_device=0",
                                             "wg_open.has_inet6_device=0"])
    # dev_validate_mtu's two -EINVAL arms (net/core/dev.c:9061-9075), found by
    # the device correspondence audit (docs/2026-10-13-audit-device.md, M1):
    # above wg0's max_mtu (2147483552, device.c:297), and at 2^31, which the
    # guest's `(int)op->a` makes negative (guest.c:2393). Both leave the MTU
    # and the session untouched, so the GET afterwards is the same as before.
    ops, sess, steer = d3.session(keepalive=5)
    out["w4_set_mtu_over_max"] = (ops + [set_mtu(2147483553), OBSERVE, GET], steer, SESSION)
    ops, sess, steer = d3.session(keepalive=5)
    out["w4_set_mtu_negative"] = (ops + [set_mtu(2147483648), OBSERVE, GET], steer, SESSION)
    # W7 (section 6, the core tier): batches of n data messages under a
    # session, injected in one io_uring_enter, so the decrypt ring and the
    # peer's rx_queue hold n items at once: wg_prev_queue_dequeue's "more
    # remain" arm (queueing.c:91-95), and with the poll between items an
    # UNCRYPTED head left peeked (`.prevQueuePeeked` true). n = 8 is the
    # instance where per-item yields and two-item polls occur.
    for n in (2, 8):
        ops, sess, steer = d3.session(keepalive=5)
        items = [inject_item(sess, k, f"rx{k}") for k in range(n)]
        out[f"w7_multi_rx_{n}"] = (ops + [batch(items, 200 if n == 2 else 400), OBSERVE, GET], steer,
                                   SESSION + d2.DATA + [DEQUEUE_MORE])
    # The tx-side twins: n transmits in one batch stage n ring items; the
    # tx worker meets the tx_queue's dequeue arms, and an UNCRYPTED head
    # when it runs between the encrypt worker's items (send.c:269-272).
    for n in (2, 8):
        ops, sess, steer = d3.session(keepalive=5)
        items = [xmit_item(d2.payload(64 + k, 10 + k)) for k in range(n)]
        out[f"w7_multi_tx_{n}"] = (ops + [batch(items, 200 if n == 2 else 400), OBSERVE, GET], steer,
                                   SESSION + d2.DATA_SENT + [DEQUEUE_MORE])
    # Injects and transmits in one batch: the encrypt and decrypt workers
    # both queued, ordered by their section starts (Env.afterBatch).
    ops, sess, steer = d3.session(keepalive=5)
    items = [inject_item(sess, 0, "mix0"), xmit_item(d2.payload(64, 20)), inject_item(sess, 1, "mix1"),
             xmit_item(d2.payload(65, 21))]
    out["w7_mixed"] = (ops + [batch(items, 400), OBSERVE, GET], steer, SESSION + d2.DATA + d2.DATA_SENT + [DEQUEUE_MORE])
    # Nine data messages in one batch, the 8th an inner IPv4 TCP SYN (the
    # stack's RST goes back through wg_xmit inside the poll, with its
    # records) and the 9th from the IPv6 sender (the endpoint roams inside
    # the batch: dst_cache_reset's jiffies record; the endpoint family
    # decision is evaluated with both outcomes in one operation, hence its
    # `repeatable` mark). Written for the receive audit's F6b (GRO's flush at
    # a batch of 8 inside one poll); on this one-CPU kernel the NET_RX
    # softirq runs inline at every decrypt (19 polls for 9 packets here), so
    # no poll holds 8 packets and the flush point is not observable, but the
    # roam-in-batch and RST-in-batch combination was new to the corpus.
    ops, sess, steer = d3.session(keepalive=5)
    syn = noise.ipv4_tcp(d2.SRC4, noise.WG0_ADDR4, 40009, 80, 0x11223344, 0, 2)
    items = [inject_item(sess, k, f"rx{k}") for k in range(7)]
    items.append({"kind": "inject", "family": 4, "port": d1.PORT, "message": sess.to_wg0(7, syn).hex()})
    items.append({"kind": "inject", "family": 6, "port": d1.PORT, "message": sess.to_wg0(8, d2.inner4("rx8")).hex()})
    out["w7_multi_rx_9_rst_roam"] = (ops + [batch(items, 400), OBSERVE, GET], steer,
                                     SESSION + d2.DATA + [DEQUEUE_MORE, "wg_timers_data_received.not_pending=1",
                                                          "wg_packet_create_data_done.data_sent=1",
                                                          "encrypt_packet.checksum_partial=0"])
    return out


def tier():
    """The full-ring tier (docs/2026-10-13-w7-full-ring-tier.md): the 1024-slot
    encrypt ring filled by one wg_batch of transmits, on the ring the session
    already used. The session's first keepalive (op 3, under the response)
    takes slot 0 and is consumed; `__ptr_ring_discard_one` zeroes consumed
    slots only once a batch of 16 has accrued (or at the ring's end), so the
    slot stays physically occupied, as does each later consumed slot below
    the batch, and `__ptr_ring_produce`'s full test (occupancy, not the
    count) fails the producer that wraps onto it; a failed produce leaves the
    producer index where it is, so every later item of the same batch fails
    at the same slot. Drops per trace = items - (1024 - the uncleared slots
    carried into the batch). Sessions with the 25 s persistent keepalive: the
    comparison child's console drain after the batch runs past 5 s, and a 5 s
    keepalive would open sections after the readout. Keepalive-size payloads
    (one byte) keep the wire and the listeners' drain small; the second
    batch's wait is the tier's 1000 ms default (section 12, P-A)."""
    out = {}
    def trace(name, first, count, expect, keepalive=25):
        ops, sess, steer = d3.session(keepalive=keepalive)
        batches = [batch([xmit_item(d2.payload(1, 1 + k)) for k in range(first)], 200)] if first else []
        batches.append(batch([xmit_item(d2.payload(1, 100 + k)) for k in range(count)], 1000))
        out[name] = (ops + batches + [OBSERVE, GET], steer, SESSION + d2.DATA_SENT + expect)
    full = ["wg_queue_enqueue_per_device_and_peer.ring_full=1", "wg_packet_create_data.epipe=1"]
    fits = ["wg_queue_enqueue_per_device_and_peer.ring_full=0", "wg_packet_create_data.epipe=0"]
    # the keepalive's slot 0 and op 4's slot 1 carried: 1022 fit, items 1023 and 1024 fail at slot 0
    trace("w7_ring_wrap", 1, 1024, full)
    # the same two carried slots, one fewer item: 1022 fit, item 1023 fails
    trace("w7_ring_1023", 1, 1023, full)
    # one more item: 1022 fit, items 1023, 1024 and 1025 fail
    trace("w7_ring_1025", 1, 1025, full)
    # no op 4: only the keepalive's slot carried: 1023 fit, item 1024 fails
    trace("w7_ring_fresh_1024", 0, 1024, full)
    # 15 items in op 4: with the keepalive, 16 consumed, the batch rule clears
    # slots 0..15 at the 16th consume: nothing carried, all 1024 fit
    trace("w7_ring_batch_clear", 15, 1024, fits)
    # Shorter keepalives (1, 2 and 5 s, tried 2026-10-13 for the claim-point
    # robustness work) do not put a timer inside the batch: the persistent
    # keepalive is re-armed at every authenticated packet, so it fires only
    # after the last send, in the console drain between operations, where no
    # window records it (the 2 s and 5 s variants fail the guest's opened-
    # sections guard, the 1 s one as a bare observation difference). The 25 s
    # session stays; the variants are not written.
    out.update(rx_1025())
    return out


def rx_1025():
    """The receive twin of the queue limit (receive.c:534-539, the receive
    audit's F1): 1025 data messages to one peer in one batch, all queued
    before the decrypt worker runs; the 1025th finds the peer's rx_queue at
    MAX_QUEUED_PACKETS and wg_prev_queue_enqueue refuses it (-ENOSPC): the
    keypair and peer puts and a silent dev_kfree_skb, no counter. Keepalive-
    sized data messages (32 bytes, an empty inner), since the guest's
    MAX_PAYLOAD (65536 bytes per operation) cannot carry 1025 items with an
    inner datagram each. The 1024 inline NAPI polls that follow meet the
    (c') placement ambiguity about a thousand times; the protocol's ceiling
    on open placements is the trace's injected-message count, so the check's
    placement selection runs over all of them (claim-point robustness,
    2026-10-13)."""
    ops, sess, steer = d3.session()
    items = [{"kind": "inject", "family": 4, "port": d1.PORT, "message": sess.to_wg0(k, b"").hex()}
             for k in range(1025)]
    return {"w7_ring_rx_1025": (ops + [batch(items, 1000), OBSERVE, GET], steer,
                                SESSION + ["wg_queue_enqueue_per_device_and_peer.peer_queue_full=1",
                                           "wg_packet_consume_data.enqueued=0",
                                           "wg_packet_consume_data.enqueued_epipe=0"])}


def controls():
    """Beyond the WireGuard boundary (section 16): the mirror answers
    `unsupported` (fail-noisy), never a prediction. Each is a well-formed
    trace the harness would also refuse (validate_packet), fed to the mirror
    alone by scripts/wg-w47-controls.py."""
    ops, sess, steer = d3.session(keepalive=5)
    dst6 = d2.DST6
    gso6 = {"op": "wg_xmit", "packet": {"family": 6, "dst": dst6.hex(), "payload": d2.payload(2744, 7).hex(),
                                        "gso_size": 1372}}
    short_last = xmit(d2.payload(1400, 8), 1000)    # 1000 + 400: a short last segment
    probe6 = {"op": "wg_xmit", "packet": {"family": 6, "dst": dst6.hex(), "payload": d2.payload(1300, 9).hex(),
                                          "pmtudisc": "probe"}}
    return {"wc_gso_ipv6": (ops + [gso6, OBSERVE], steer, SESSION, None),
            "wc_gso_short_last": (ops + [short_last, OBSERVE], steer, SESSION, None),
            "wc_probe_ipv6": (ops + [probe6, OBSERVE], steer, SESSION, None)}


def finish(out, validate=True):
    result = {}
    for name, entry in out.items():
        ops, steer, expect = entry[:3]
        fixture = entry[3] if len(entry) > 3 else None
        if wait_after_up(ops) > WAIT_BUDGET_SECONDS:
            raise AssertionError(f"{name} exceeds the guest's wait budget")
        trace = {"version": 1, "id": name, "ops": ops, "steer": steer, "expect": list(dict.fromkeys(expect))}
        if fixture:
            trace["net_fixture"] = fixture
        result[name] = validate_trace(trace) if validate else trace
    return result


def main():
    for directory, written in ((ROOT / "corpus" / "wireguard", finish(traces())),
                               (ROOT / "corpus" / "w47-controls", finish(controls(), validate=False)),
                               (ROOT / "corpus" / "w7-tier", finish(tier()))):
        directory.mkdir(exist_ok=True)
        for name, trace in written.items():
            (directory / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
        print(f"wrote {len(written)} traces to {directory}")


if __name__ == "__main__":
    main()
