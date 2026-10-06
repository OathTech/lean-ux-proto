#!/usr/bin/env python3
"""D3 stream M: probe traces for the mirror's timers (docs/2026-10-05-d3-timers.md,
sections 5-7), until stream H's corpus lands. Each fires one WireGuard timer
with `wg_advance`, or reaches one key-expiry arm (section 6), and states what
it is for in `expect` labels (`fired:<callback>` and decision outcomes).

The traces are written to a directory (default `corpus/d3m`, untracked) and
checked as an extra suite:

    scripts/d3-m-probes.py [--out corpus/d3m]
    LEANUX_KERNEL_DIR=... scripts/in-bundle python3 scripts/d3-m-probes.py --check OUTDIR

Every initiation after the first steered one draws its ephemeral, timestamp
and index (`draw` entries): a steered trace must schedule every encounter of
its steered sites (stream K, section 13.5).
"""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
from harness import noise  # noqa: E402
from harness.trace import validate_trace  # noqa: E402

d1 = __import__("wg-d1-corpus")
rx = __import__("wg-d2-rx-probes")

XMIT = {"op": "wg_xmit", "packet": {"family": 4, "dst": "0a000001", "payload": "6c65757864336d70"}}
DRAWN_INITIATION = [["init_ephemeral", "draw"], ["tai64n_now", "draw"], ["index_draw", "draw"]]


def advance(ticks):
    return {"op": "wg_advance", "ticks": ticks}


def no_keepalive():
    return [{"op": "wg_set", "config": {"private_key": d1.key(d1.DEVICE), "listen_port": d1.PORT,
                                        "peers": [d1.peer()]}}, {"op": "wg_up"}]


def initiator_session():
    """wg0 initiates (persistent keepalive 25, as D1): the keepalive wg_up
    stages queues the initiation; the response completes the session."""
    resp, key, index = rx.session()
    return d1.setup() + [d1.OBSERVE, d1.inject(resp.message)], key, index


def quiet_initiator_session():
    """wg0 initiates with persistent keepalive 0: a transmitted packet queues
    the initiation and is sent on the response (data_sent arms the new-handshake
    timer); the peer's keepalive (an empty data message) deletes it
    (any_authenticated_packet_received) and arms nothing (no data_received).
    Only the zero-key timer stays pending."""
    resp, key, index = rx.session()
    ops = no_keepalive() + [XMIT, d1.OBSERVE, d1.inject(resp.message),
                            d1.inject(rx.data_message(key, index, 0, b"", pad=False))]
    return ops, key, index


def quiet_responder_session():
    """wg0 responds (persistent keepalive 0); the peer's keepalive confirms
    the keypair. Only the zero-key timer is pending (session_derived)."""
    theirs = noise.initiation(noise.public_key(d1.DEVICE), d1.PEER, d1.PEER_EPHEMERAL, noise.tai64n(1, 0), 0x0badcafe)
    ours = noise.response(theirs, d1.DEVICE, noise.clamp(d1.RESP_EPHEMERAL), None, d1.INDEX_RESPONDER_SIDE,
                          initiator_public=noise.public_key(d1.PEER))
    key = ours.initiator_sending
    ops = no_keepalive() + [d1.inject(theirs), d1.OBSERVE,
                            d1.inject(rx.data_message(key, d1.INDEX_RESPONDER_SIDE, 0, b"", pad=False))]
    steer = [["resp_ephemeral", d1.RESP_EPHEMERAL.hex()], ["index_draw", d1.le32(d1.INDEX_RESPONDER_SIDE)]]
    return ops, steer, key, d1.INDEX_RESPONDER_SIDE, theirs


def traces():
    out = {}
    steer = d1.steer_initiation()
    ses, key, index = initiator_session()
    quiet, qkey, qindex = quiet_initiator_session()
    resp_ops, resp_steer, rkey, rindex, theirs = quiet_responder_session()
    data = lambda k, i, n, text: d1.inject(rx.data_message(k, i, n, rx.ipv4_udp(text)))   # noqa: E731

    # no session: the xmit queues an initiation, whose send arms the
    # retransmit timer (1250 + [0, 83)); each advance of 1450 fires it
    out["d3m_retransmit"] = (no_keepalive() + [XMIT, d1.OBSERVE, advance(1450), d1.OBSERVE, advance(1450), d1.OBSERVE],
                             DRAWN_INITIATION * 3,
                             ["fired:wg_expired_retransmit_handshake", "wg_expired_retransmit_handshake.give_up=0"])
    # attempts 1..19 retry, the 20th firing gives up: the staged packet is
    # purged (tx_dropped 1), the keepalive timer deleted, the zero-key timer
    # armed. A stretch (section 10): 20 advances nearly use the guest's 4 s
    # real-time bound, so no observation follows (one exceeded it)
    out["d3m_retransmit_gives_up"] = (no_keepalive() + [XMIT] + [advance(1450)] * 20,
                                      DRAWN_INITIATION * 20,
                                      ["fired:wg_expired_retransmit_handshake", "wg_expired_retransmit_handshake.give_up=1",
                                       "wg_expired_retransmit_handshake.zero_key_not_pending=1"])
    # a data message arms the keepalive timer (2500); advance 2600 fires it
    out["d3m_keepalive"] = (ses + [data(key, index, 0, b"one"), advance(2600), d1.OBSERVE], steer,
                            ["fired:wg_expired_send_keepalive", "wg_expired_send_keepalive.need_another=0"])
    # two data messages without a send between: need_another_keepalive; the
    # callback re-arms (+10 s) and the keepalive's tx worker deletes the
    # re-arm, so the second advance fires nothing (one keepalive)
    out["d3m_keepalive_rearm_deleted"] = (ses + [data(key, index, 0, b"one"), data(key, index, 1, b"two"),
                                                 advance(2600), advance(2600), d1.OBSERVE], steer,
                                          ["fired:wg_expired_send_keepalive", "wg_expired_send_keepalive.need_another=1"])
    # a data packet sent arms the new-handshake timer (3750 + [0, 83))
    out["d3m_new_handshake"] = (ses + [XMIT, advance(3950), d1.OBSERVE], steer + DRAWN_INITIATION,
                                ["fired:wg_expired_new_handshake"])
    # the persistent keepalive (25 s = 6250, level 3: up to 512 late)
    out["d3m_persistent"] = (ses + [d1.OBSERVE, advance(6800), d1.OBSERVE], steer,
                             ["fired:wg_expired_send_persistent_keepalive",
                              "wg_expired_send_persistent_keepalive.interval=1"])
    # a 2 s persistent keepalive fires in real time, in one of the 0.4 s
    # waits after the junk injections (a 1-byte message, dropped before any
    # traversal re-arm), about 2 s after the response; the next firing (4 s)
    # is after the trace. No wg_observe: its wait is before its coverage
    # window, so a section there would be lost (and flagged)
    natural = d1.setup()
    natural[0]["config"]["peers"][0]["keepalive"] = 2
    junk = {"op": "wg_inject", "family": 4, "port": d1.PORT, "message": "01"}
    out["d3m_persistent_natural"] = (natural + [d1.inject(rx.session()[0].message)] + [junk] * 5,
                                     steer, ["fired:wg_expired_send_persistent_keepalive"])
    # 540 s: the persistent keepalive (the keypair has expired: an
    # initiation), then the zero-key timer and its clear work
    out["d3m_zero_key"] = (ses + [d1.OBSERVE, advance(139200), d1.OBSERVE, d1.GET], steer + DRAWN_INITIATION,
                           ["fired:wg_expired_zero_key_material", "wg_expired_zero_key_material.alive=1",
                            "wg_expired_zero_key_material.already_queued=0"])
    # only the zero-key timer pending, then a data message under the cleared
    # keys (no keypair for its index) and a transmission (an initiation)
    out["d3m_zero_key_quiet"] = (quiet + [advance(139200), data(qkey, qindex, 1, b"late"), XMIT, d1.OBSERVE, d1.GET],
                                 steer + DRAWN_INITIATION, ["fired:wg_expired_zero_key_material"])
    # section 6: send with an expired key (181 s): an initiation, the packet stays staged
    out["d3m_send_expired"] = (resp_ops + [advance(45250), XMIT, d1.OBSERVE, d1.GET], resp_steer + DRAWN_INITIATION,
                               ["wg_packet_send_staged_packets.birthdate_expired=1"])
    # receive with an expired key: rejected (is_valid = false)
    out["d3m_recv_expired"] = (resp_ops + [advance(45250), data(rkey, rindex, 1, b"old"), d1.OBSERVE, d1.GET],
                               resp_steer, ["decrypt_packet.key_expired=1"])
    # send-side keep_key_fresh at 121 s (initiator): the data, then an initiation
    out["d3m_send_fresh"] = (quiet + [advance(30250), XMIT, d1.OBSERVE], steer + DRAWN_INITIATION,
                             ["keep_key_fresh.birthdate_expired=1", "keep_key_fresh.send=1"])
    # receive-side keep_key_fresh at 166 s: an initiation after the first
    # message; the second returns before the clock read (sent_lastminute_handshake)
    out["d3m_recv_fresh"] = (quiet + [advance(41500), data(qkey, qindex, 1, b"one"), data(qkey, qindex, 2, b"two"),
                                      d1.OBSERVE], steer + DRAWN_INITIATION,
                             ["keep_key_fresh.rx_birthdate_expired=1", "keep_key_fresh.sent_lastminute=1"])
    # the 5 s rate limit without the key trick: respond, advance 1450, transmit
    out["d3m_rate_limit"] = (no_keepalive() + [d1.inject(theirs), d1.OBSERVE, advance(1450), XMIT, d1.OBSERVE],
                             resp_steer + DRAWN_INITIATION, ["wg_packet_send_queued_handshake_initiation.not_expired=0"])
    result = []
    for name, (ops, schedule, expect) in out.items():
        trace = {"version": 1, "id": name, "ops": ops, "steer": schedule, "expect": expect}
        result.append(validate_trace(trace))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", type=Path, default=ROOT / "corpus" / "d3m")
    parser.add_argument("--check", type=Path, help="run evaluator.check on the written suite, report in this directory")
    parser.add_argument("--only", help="comma-separated trace ids to write")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    only = set(args.only.split(",")) if args.only else None
    for old in args.out.glob("*.json"):
        old.unlink()
    for trace in traces():
        if only is None or trace["id"] in only:
            (args.out / f"{trace['id']}.json").write_text(json.dumps(trace, indent=2) + "\n")
    if args.check:
        import evaluator.check as check
        suite = args.out.resolve().relative_to(ROOT / "corpus").as_posix()
        check.SUITES = check.SUITES + (suite,)
        return check.main(["--suite", suite, "--out", str(args.check)])


if __name__ == "__main__":
    sys.exit(main())
