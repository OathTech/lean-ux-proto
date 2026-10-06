#!/usr/bin/env python3
"""Writes the A1 allocation-outcome traces into corpus/alloc
(docs/2026-10-05-a-alloc.md, section 7).

A1 steers the class-(a) sites only [USER A1]: the three GFP_ATOMIC alloc_skb
calls. Each is an `__alloc_skb` helper site with two encounters on success
(the sk_buff, then the data buffer), so a schedule naming a site lists every
encounter of it in the trace: `fail` fails the sk_buff, `draw, fail` the
data buffer, `draw, draw` lets a success through recorded. The chunk holding
such a trace is armed with the `__alloc_skb`/`kmalloc_reserve` ranges, so
every allocation through them is recorded and consumed by the mirror.

`replySkb` (socket.c:217, cookie replies under load) is not reachable on this
base: the mirror stops at `under_load` (Receive.lean). Its trace,
`a_reply_nomem`, is pending stream E-B.

The output is deterministic: rerunning this script reproduces the files.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness import noise  # noqa: E402

DEVICE = b"\x11" * 32
INITIATOR = b"\x22" * 32
PORT = 51820
LISTENER = {"family": 4, "addr": "7f000001", "port": 51999}
FAIL = "00" * 8
OBSERVE = {"op": "wg_observe"}
GET = {"op": "wg_get"}
SENDBUF_NOMEM = "wg_socket_send_buffer_to_peer.no_mem"
KEEPALIVE_NOMEM = "wg_packet_send_keepalive.no_mem"


def init(ephemeral=0x33, stamp=1, index=7):
    return noise.initiation(noise.public_key(DEVICE), INITIATOR, bytes([ephemeral]) * 32,
                            bytes(11) + bytes([stamp]), index)


def peer(**extra):
    p = {"public_key": noise.public_key(INITIATOR).hex(),
         "allowed_ips": [{"family": 4, "addr": "0a000000", "cidr": 8}]}
    p.update(extra)
    return p


def setup(**extra):
    return [{"op": "wg_set", "config": {"private_key": DEVICE.hex(), "listen_port": PORT, "peers": [peer(**extra)]}},
            {"op": "wg_up"}]


def inject(message, family=4):
    return {"op": "wg_inject", "family": family, "port": PORT, "message": message.hex()}


XMIT = {"op": "wg_xmit", "packet": {"family": 4, "dst": "0a000001"}}

# name: (ops, steer, expect[, rlimit_nofile])
TRACES = {
    # wg0 initiates (wg_xmit with no session queues the initiation; the send
    # worker's alloc_skb at socket.c:192): recorded unsteered, then each failure
    "a_sendbuf_init_draw": (setup(endpoint=LISTENER) + [XMIT, OBSERVE, GET],
                            [["sendBufSkb", "draw"], ["sendBufSkb", "draw"]], [f"{SENDBUF_NOMEM}=0"]),
    "a_sendbuf_init_nomem": (setup(endpoint=LISTENER) + [XMIT, OBSERVE, GET],
                             [["sendBufSkb", FAIL]], [f"{SENDBUF_NOMEM}=1"]),
    "a_sendbuf_nodata": (setup(endpoint=LISTENER) + [XMIT, OBSERVE, GET],
                         [["sendBufSkb", "draw"], ["sendBufSkb", FAIL]], [f"{SENDBUF_NOMEM}=1"]),
    # wg0 responds (the receive worker): the session is begun and
    # last_sent_handshake set before the send fails; tx_bytes stays 0
    "a_sendbuf_nomem": ([*setup(), inject(init()), OBSERVE, GET],
                        [["sendBufSkb", FAIL]], [f"{SENDBUF_NOMEM}=1", "wg_noise_handshake_begin_session.initiator=0"]),
    "a_sendbuf_resp_nodata": ([*setup(), inject(init(), 6), OBSERVE, GET],
                              [["sendBufSkb", "draw"], ["sendBufSkb", FAIL]], [f"{SENDBUF_NOMEM}=1"]),
    # a failed response, then a newer initiation whose response goes out
    "a_sendbuf_resp_retry": ([*setup(), inject(init()), OBSERVE, inject(init(ephemeral=0x34, stamp=2, index=9)),
                              OBSERVE, GET],
                             [["sendBufSkb", FAIL], ["sendBufSkb", "draw"], ["sendBufSkb", "draw"]],
                             [f"{SENDBUF_NOMEM}=1", f"{SENDBUF_NOMEM}=0"]),
    # the staged keepalive of wg_up (persistent keepalive set before up;
    # send.c:226 in the syscall): no keepalive staged, no initiation queued
    "a_keepalive_nomem": (setup(endpoint=LISTENER, keepalive=25) + [OBSERVE, GET],
                          [["keepaliveSkb", FAIL]], [f"{KEEPALIVE_NOMEM}=1"]),
    "a_keepalive_nodata": (setup(endpoint=LISTENER, keepalive=25) + [OBSERVE, GET],
                           [["keepaliveSkb", "draw"], ["keepaliveSkb", FAIL]], [f"{KEEPALIVE_NOMEM}=1"]),
    # a recorded keepalive allocation: the staged keepalive queues the
    # initiation, whose send-buffer allocation is armed and consumed too
    "a_keepalive_draw": (setup(endpoint=LISTENER, keepalive=25) + [OBSERVE, GET],
                         [["keepaliveSkb", "draw"], ["keepaliveSkb", "draw"]], [f"{KEEPALIVE_NOMEM}=0"]),
    # the staged keepalive of a wg_set that turns persistent keepalive on
    # while wg0 is up
    "a_keepalive_set_nomem": (setup(endpoint=LISTENER) + [
        {"op": "wg_set", "config": {"peers": [{"public_key": noise.public_key(INITIATOR).hex(), "keepalive": 25}]}},
        OBSERVE, GET], [["keepaliveSkb", FAIL]], [f"{KEEPALIVE_NOMEM}=1"]),
    # an FS run armed with the kvmalloc helper range (a draw: the task class
    # is not failed [USER A1]): the dup3 expands the table to 1024 slots, an
    # 8 KiB fd array (the slab attempt with __GFP_NORETRY) and its bitmaps,
    # each one recorded and consumed
    "a_fdtable_kvmalloc_draw": ([{"op": "eventfd2", "init": 0, "flags": 0},
                                 {"op": "dup3", "fd": {"ref": 0}, "newfd": {"literal": 1000}, "flags": 0},
                                 {"op": "write", "fd": {"literal": 1000}, "count": 8, "value": "1"},
                                 {"op": "read", "fd": {"ref": 0}, "count": 8}],
                                [["kvmallocFdArray", "draw"]], ["alloc_fdtable.fd_array_failed=0"], 1024),
}


def main():
    out = ROOT / "corpus/alloc"
    out.mkdir(exist_ok=True)
    for name, (ops, steer, expect, *rlimit) in TRACES.items():
        trace = {"version": 1, "id": name, "ops": ops, "steer": steer, "expect": expect}
        if rlimit:
            trace["rlimit_nofile"] = rlimit[0]
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
    print(f"wrote {len(TRACES)} traces to {out}")


if __name__ == "__main__":
    main()
