#!/usr/bin/env python3
"""Writes the W4 traces (docs/2026-10-06-w4-w7-transmit-bulk.md, sections 6
and 16.1: the kept transmit-shape classes) into corpus/wireguard, and the
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
    return out


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
                               (ROOT / "corpus" / "w47-controls", finish(controls(), validate=False))):
        directory.mkdir(exist_ok=True)
        for name, trace in written.items():
            (directory / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
        print(f"wrote {len(written)} traces to {directory}")


if __name__ == "__main__":
    main()
