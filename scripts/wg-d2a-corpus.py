#!/usr/bin/env python3
"""Writes D2 stream A's transmit traces (corpus/wireguard/d2a_*.json).

wg0 initiates with steered values and the peer's offline response completes
the session (the D1 setup, scripts/wg-d1-corpus.py); then the fixture's
sender transmits UDP datagrams with payloads into wg0 (`wg_xmit`), which
wg0 encrypts and sends to the peer's endpoint, the sender itself after the
response. The check compares the ciphertexts the sender receives with the
mirror's, so the inner IP packets the environment builds (Env.xmitPacket:
id 0, flow label 0, the completed UDP checksum, the MTU) are checked by
bytes. `--verify DIR` decrypts the ciphertexts a check run observed under
the offline session keys and prints the inner packets.

Classes: transmit after a session (IPv4 payload sizes 1, 15, 16, 17 and
1376, 1377, 1391, 1392, the inner lengths 1404, 1405, 1419, 1420 around the
MTU clamp of calculate_skb_padding; IPv6), and packets staged before the
session, flushed with the staged keepalive as one list when it completes.
"""
import argparse
import json
import struct
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
from harness import noise  # noqa: E402

import importlib.util  # noqa: E402
_spec = importlib.util.spec_from_file_location("d1", ROOT / "scripts" / "wg-d1-corpus.py")
d1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d1)

V4_DST = "0a000002"                               # 10.0.0.2, in the peer's 10.0.0.0/8
V6_DST = "fd000000000000000000000000000002"       # fd00::2, in the peer's fd00::/16


def payload(n, seed=0):
    return bytes((seed + 7 * k) % 256 for k in range(n)).hex()


def xmit(family, dst, n, seed=0):
    return {"op": "wg_xmit", "packet": {"family": family, "dst": dst, "payload": payload(n, seed)}}


def setup():
    p = d1.peer(keepalive=25)
    p["allowed_ips"] = p["allowed_ips"] + [{"family": 6, "addr": "fd00" + "0" * 28, "cidr": 16}]
    return [{"op": "wg_set", "config": {"private_key": d1.key(d1.DEVICE), "listen_port": d1.PORT, "peers": [p]}},
            {"op": "wg_up"}]


def session(after):
    """The D1 session, then `after`: the response's keepalive and every
    datagram after it go to the sender."""
    basic = d1.respond(d1.wg0_initiation())
    return setup() + [d1.OBSERVE, d1.inject(basic.message), d1.OBSERVE] + after + [d1.GET]


EXPECT_DATA = d1.EXPECT_SESSION + ["wg_packet_create_data_done.not_keepalive=1", "wg_timers_data_sent.not_pending=1"]


def traces():
    obs = d1.OBSERVE
    out = {
        "d2a_xmit_small": session([xmit(4, V4_DST, n, n) for n in (1, 15, 16, 17)] + [obs]),
        "d2a_xmit_mtu": session([xmit(4, V4_DST, n, n) for n in (1376, 1377, 1391, 1392)] + [obs]),
        "d2a_xmit_v6": session([xmit(6, V6_DST, n, n) for n in (1, 16, 1372)] + [obs]),
        # staged before the session: wg_up staged a keepalive and queued the
        # initiation; two payload packets join the staged queue; the
        # response flushes all three as one list (nonces 0, 1, 2)
        "d2a_staged_flush": setup() + [obs, xmit(4, V4_DST, 100, 1), xmit(6, V6_DST, 200, 2), obs,
                                       d1.inject(d1.respond(d1.wg0_initiation()).message), obs, d1.GET],
    }
    return {name: {"version": 1, "id": name, "ops": ops, "steer": d1.steer_initiation(), "expect": EXPECT_DATA}
            for name, ops in out.items()}


def verify(run):
    """Decrypt the data messages the sender received in a check run."""
    basic = d1.respond(d1.wg0_initiation())
    key = basic.responder_receiving
    for line in (Path(run) / "linux" / "observations.jsonl").read_text().splitlines() if (Path(run) / "linux" / "observations.jsonl").exists() else []:
        obs = json.loads(line)
        if not obs["id"].startswith("d2a_"):
            continue
        for o in obs["observations"]:
            for r in o.get("replies", []):
                data = bytes.fromhex(r[-1])
                if data[:4] != struct.pack("<I", 4):
                    continue
                index, counter, plain = noise.open_data(data, key)
                print(obs["id"], o["index"], "src", r[1], r[2], "counter", counter, "len", len(plain), plain.hex())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", type=Path)
    args = parser.parse_args()
    if args.verify:
        return verify(args.verify)
    out = ROOT / "corpus" / "wireguard"
    written = traces()
    for name, trace in written.items():
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
    print(f"wrote {len(written)} traces to {out}")


if __name__ == "__main__":
    main()
