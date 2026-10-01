#!/usr/bin/env python3
"""Writes the stage C (Noise responder) traces into corpus/wireguard.

The handshake initiations carry real Noise IKpsk2 cryptography, so they are
built here with harness/noise.py rather than written by hand. The output is
deterministic: rerunning this script reproduces the committed files.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness import noise  # noqa: E402

DEVICE = b"\x11" * 32
INITIATOR = b"\x22" * 32
OTHER_DEVICE = b"\x55" * 32
LOW_ORDER = bytes(32)
PORT = 51820


def key(b):
    return b.hex()


def ts(n):
    return bytes(11) + bytes([n])


def init(device=DEVICE, ephemeral=0x33, stamp=1, index=7, **kw):
    return noise.initiation(noise.public_key(device), INITIATOR, bytes([ephemeral]) * 32, ts(stamp), index, **kw)


def peer(public=None, **extra):
    p = {"public_key": key(noise.public_key(INITIATOR) if public is None else public),
         "allowed_ips": [{"family": 4, "addr": "0a000000", "cidr": 8}]}
    p.update(extra)
    return p


def setup(private=DEVICE, peers=None):
    config = {"listen_port": PORT, "peers": peers if peers is not None else [peer()]}
    if private is not None:
        config["private_key"] = key(private)
    return [{"op": "wg_set", "config": config}, {"op": "wg_up"}]


def inject(message, family=4):
    return {"op": "wg_inject", "family": family, "port": PORT, "message": message.hex()}


OBSERVE = {"op": "wg_observe"}
GET = {"op": "wg_get"}

TRACES = {
    # a valid initiation: the response goes to the sender, the endpoint is learned
    "c_initiation": setup() + [inject(init()), OBSERVE, GET],
    "c_initiation_v6": setup() + [inject(init(), 6), OBSERVE, GET],
    # the same message again is a replay; a newer timestamp from IPv6 starts a
    # new session, putting the pending next keypair
    "c_replay_then_newer": setup() + [inject(init()), OBSERVE, inject(init()), OBSERVE,
                                      inject(init(ephemeral=0x34, stamp=2, index=9), 6), OBSERVE, GET],
    # a newer initiation from the same endpoint (the endpoint compares equal)
    "c_newer_same_endpoint": setup() + [inject(init()), inject(init(ephemeral=0x34, stamp=2, index=8)),
                                        OBSERVE, GET],
    # an older timestamp after a newer one
    "c_older_timestamp": setup() + [inject(init(stamp=5)), inject(init(ephemeral=0x34, stamp=3, index=8)),
                                    OBSERVE, GET],
    # the static key decrypts but names no configured peer
    "c_unknown_peer": setup(peers=[peer(noise.public_key(b"\x44" * 32))]) + [inject(init()), OBSERVE, GET],
    # no private key: MAC1 is checked under the zero key, then consumption stops
    "c_no_identity": setup(private=None) + [inject(init(mac1_key=bytes(32))), OBSERVE, GET],
    "c_bad_static": setup() + [inject(init(tamper="static")), OBSERVE, GET],
    "c_bad_timestamp": setup() + [inject(init(tamper="timestamp")), OBSERVE, GET],
    # a low-order ephemeral key makes the es DH the null point
    "c_low_order_ephemeral": setup() + [inject(init(ephemeral_public=LOW_ORDER)), OBSERVE, GET],
    # a low-order static key: the peer exists but its static-static DH is null
    "c_low_order_static": setup(peers=[peer(LOW_ORDER)]) + [inject(init(static_public=LOW_ORDER)), OBSERVE, GET],
    # a persistent keepalive: the traversal timers are armed; the endpoint
    # configured at the listener is replaced by the sender's
    "c_keepalive_endpoint": setup(peers=[peer(keepalive=25, endpoint={"family": 4, "addr": "7f000001",
                                                                      "port": 51999})])
                            + [OBSERVE, inject(init()), OBSERVE, GET],
    "c_preshared_key": setup(peers=[peer(preshared_key="aa" * 32)]) + [inject(init()), OBSERVE, GET],
    # removing a peer with a pending next keypair puts that keypair
    "c_remove_after_handshake": setup() + [inject(init()), OBSERVE,
                                           {"op": "wg_set", "config": {"peers": [
                                               {"public_key": key(noise.public_key(INITIATOR)), "remove": True}]}},
                                           GET],
    # a new private key expires the session; the next initiation must target
    # the new key and still be newer than the last timestamp
    "c_key_change_after_handshake": setup() + [inject(init()), OBSERVE,
                                               {"op": "wg_set", "config": {"private_key": key(OTHER_DEVICE)}},
                                               inject(init()),
                                               inject(init(device=OTHER_DEVICE, ephemeral=0x34, stamp=2, index=8)),
                                               OBSERVE, GET],
}


def main():
    out = ROOT / "corpus" / "wireguard"
    for name, ops in TRACES.items():
        trace = {"version": 1, "id": name, "ops": ops}
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
    print(f"wrote {len(TRACES)} traces to {out}")


if __name__ == "__main__":
    main()
