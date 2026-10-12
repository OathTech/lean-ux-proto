#!/usr/bin/env python3
"""Writes the W5+W6 traces into corpus/wireguard (docs/2026-10-06-w5-w6-receive.md,
section 6; revision v3: the ECN/DS arms, the scoped outer source, tstats and
the IPv4 TCP RST).

Every trace completes a session as the D2 traces do (scripts/wg-d2-corpus.py:
wg0 initiates with steered draws, the peer's response is injected from the
fixture's sender, so the endpoint roams to the sender). Then:
- W5 ECN (2.1): the peer sends a data message carrying an inner UDP packet
  with an ECN codepoint in its TOS / traffic class, injected with an outer
  DS field (`tos` on the injection); the sender's `recvmsg` reports the
  inner TOS after `INET_ECN_decapsulate`'s rewrite;
- W5 DS on transmit: `wg_xmit` with a `tos`; the listeners report the outer
  DS `ip_tunnel_ecn_encap` computed (the inner ECN bits, CE as ECT(0));
- W5 scoped source (2.5): an injection `from: "ll"` roams the endpoint to
  [fe80::1%1]:51998 (src6 ::1); wg0's replies land at the link-local
  address (the sender's `IPV6_PKTINFO`), the dump shows the scope;
- W5 tstats (2.6): a keepalive and data messages count in rx_packets/rx_bytes;
- W6 (2.4.1): an inner IPv4 TCP segment to wg0's address finds no socket;
  Linux answers with a RST that re-enters wg_xmit inside the NAPI poll's
  NET_RX section as CHECKSUM_NONE; the sender's inbox holds its ciphertext.

The output is deterministic: rerunning this script reproduces the files.
"""
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness import noise  # noqa: E402
from evaluator.generate import WAIT_BUDGET_SECONDS, wait_after_up  # noqa: E402

_spec = importlib.util.spec_from_file_location("wg_d2_corpus", ROOT / "scripts" / "wg-d2-corpus.py")
d2 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d2)
d1 = d2.d1

OBSERVE, GET = d1.OBSERVE, d1.GET
SRC4, SRC6, DST4, DST6 = d2.SRC4, d2.SRC6, d2.DST4, d2.DST6
INNER_SPORT = d2.INNER_SPORT
SESSION, DATA = d2.SESSION, d2.DATA
DATA_RECEIVED = ["wg_timers_data_received.not_pending=1"]

NOT_ECT, ECT1, ECT0, CE = 0, 1, 2, 3
DSCP = 0xb8   # AF41 << 2: a DSCP the kept classes carry alongside the ECN bits


def inject(message, family=4, tos=None, ll=False):
    op = d1.inject(message, family)
    if tos is not None:
        op["tos"] = tos
    if ll:
        op["from"] = "ll"
    return op


def xmit(family, dst, data, tos=None):
    op = d2.xmit(family, dst, data)
    if tos is not None:
        op["tos"] = tos
    return op


def inner(family, text, tos):
    """An inner UDP datagram to the sender with this TOS / traffic class."""
    if family == 4:
        return noise.to_wg0(4, SRC4, text.encode(), sport=INNER_SPORT, tos=tos)
    return noise.to_wg0(6, SRC6, text.encode(), sport=INNER_SPORT, traffic_class=tos)


def ecn_trace(family, outer, inner_tos, what):
    """After the session: one data message with the inner TOS, injected with
    the outer DS field; the sender sees the (possibly rewritten) inner TOS."""
    def build(s):
        return [inject(s.to_wg0(0, inner(family, what, inner_tos)), family=family, tos=outer)]
    return d2.receive(build, DATA_RECEIVED)


def traces():
    out = {}
    # W5 ECN decapsulation (2.1), per family: the arms of RFC 6040's table
    # as inet_ecn.h takes them for an inner header with DSCP 0xb8:
    #   outer CE,     inner ECT(0): set_ce, check += htons(0xFFFE), tos |= CE
    #   outer CE,     inner ECT(1): set_ce, check += htons(0xFFFD)
    #   outer CE,     inner CE:     set_ce changes nothing (ecn 00)
    #   outer CE,     inner not-ECT: rc 2 ("drop"), ignored: delivered unchanged
    #   outer ECT(1), inner ECT(0): set_ect1, check += htons(1), tos ^= 3
    #   outer ECT(1), inner ECT(1): set_ect1 changes nothing
    #   outer ECT(0), inner not-ECT: rc 1, delivered unchanged
    # (IPv6: the same arms on the traffic class, no checksum.)
    for family, tag in ((4, "v4"), (6, "v6")):
        for name, outer, inner_tos in (("ce_ect0", CE, DSCP | ECT0), ("ce_ect1", CE, DSCP | ECT1),
                                       ("ce_ce", CE, DSCP | CE), ("ce_notect", CE, DSCP | NOT_ECT),
                                       ("ect1_ect0", ECT1, DSCP | ECT0), ("ect1_ect1", ECT1, DSCP | ECT1),
                                       ("ect0_notect", ECT0, DSCP | NOT_ECT)):
            out[f"w5_ecn_{tag}_{name}"] = ecn_trace(family, outer, inner_tos, f"ecn {tag} {name}")
    # W5 DS on transmit (send.c:378): the outer DS field of wg0's data
    # message is the inner ECN bits, CE encapsulated as ECT(0); the DSCP is
    # not copied. Five transmits per family, counters 1-5 (the keepalive took 0).
    for family, tag, dst in ((4, "v4", DST4), (6, "v6", DST6)):
        ops, _session, steer = d2.after_session(*[xmit(family, dst, d2.payload(16 + k, k), tos=t)
                                                  for k, t in enumerate((NOT_ECT, ECT1, ECT0, CE, DSCP | ECT1))])
        out[f"w5_ds_xmit_{tag}"] = (ops, steer, SESSION + d2.DATA_SENT + ["wg_timers_data_sent.not_pending=1"])
    # W5 tstats (2.6): rx_packets counts the keepalive (32 bytes) and the two
    # data messages; rx_bytes their message_data lengths.
    out["w5_stats_keepalive"] = d2.receive(lambda s: [d2.to_wg0(s, 0, b""), d2.to_wg0(s, 1, d2.inner4("stats 1")),
                                                      d2.to_wg0(s, 2, d2.inner4("stats 2"))], DATA_RECEIVED)
    # W5 scoped source (2.5): a data message from the link-local sender
    # (fe80::1 on lo, IPV6_PKTINFO) roams the endpoint to [fe80::1%1]:51998
    # with src6 = ::1; wg0's transmit then goes from ::1 to fe80::1 (send6
    # with flowi6_oif 1), delivered to the sender with that destination.
    def scoped_probe(s):
        return [inject(s.to_wg0(0, inner(6, "scoped", 0)), family=6, ll=True), xmit(6, DST6, d2.payload(24, 3))]
    out["w5_scoped_probe"] = d2.receive(scoped_probe, DATA_RECEIVED + d2.DATA_SENT)
    # The roam between the scoped and the unscoped endpoint: ::1 (scope 0)
    # after fe80::1 (scope 1) is a different endpoint (endpoint_eq compares
    # the scope); then back.
    def scoped_roam(s):
        return [inject(s.to_wg0(0, inner(6, "ll", 0)), family=6, ll=True),
                inject(s.to_wg0(1, inner(6, "lo", 0)), family=6),
                inject(s.to_wg0(2, inner(6, "ll again", 0)), family=6, ll=True)]
    out["w5_scoped_roam"] = d2.receive(scoped_roam, DATA_RECEIVED)
    # W6 (2.4.1): inner IPv4 TCP segments to wg0's address, answered with a
    # RST that re-enters wg_xmit from the NAPI poll (CHECKSUM_NONE: the
    # checksum-help decision's false outcome) and reaches the sender as a
    # data message. A SYN: RST|ACK with ack_seq = seq + 1. With ACK and a
    # payload: RST with seq = the segment's ack_seq. FIN with a payload under
    # a TOS with ECN bits: ack_seq counts both; the RST's TOS drops the ECN.
    RST = DATA + DATA_RECEIVED + ["wg_packet_create_data_done.data_sent=1", "encrypt_packet.checksum_partial=0"]
    wg0 = noise.WG0_ADDR4
    out["w6_rst_syn"] = d2.receive(lambda s: [d2.to_wg0(s, 0, noise.ipv4_tcp(SRC4, wg0, 40001, 80, 0x11223344, 0, 2))], RST)
    out["w6_rst_ack"] = d2.receive(lambda s: [d2.to_wg0(s, 0, noise.ipv4_tcp(SRC4, wg0, 40002, 443, 7, 0x55667788, 16 | 8, b"GET / HTTP/1.0\r\n"))], RST)
    out["w6_rst_ecn_tos"] = d2.receive(lambda s: [d2.to_wg0(s, 0, noise.ipv4_tcp(SRC4, wg0, 40003, 22, 0xfffffffe, 0, 1, b"xyz", tos=DSCP | CE))], RST)
    # the inner TOS with ECN bits under an outer CE: set_ce rewrites the
    # segment's header before the stack reads it; the RST's TOS is the
    # rewritten one less the ECN bits (0xb8 either way)
    out["w6_rst_outer_ce"] = d2.receive(lambda s: [inject(s.to_wg0(0, noise.ipv4_tcp(SRC4, wg0, 40004, 25, 1, 0, 2, tos=DSCP | ECT0)), tos=CE)], RST)
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
