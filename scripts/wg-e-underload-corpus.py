#!/usr/bin/env python3
"""Writes the stage E-B under-load traces (docs/2026-10-05-e-dos.md §6.B) into
corpus/wireguard/e_underload_*.json, and the merged-injection negative control
into corpus/underload-controls/.

Each trace creates wg0 in-window (L's wg_create, so the cookie secret is
captured as `.cookieSecret`), configures its private key (so the cookie
encryption key `blake2s("cookie--" || wg0_public)` is precomputed) and listen
port, and brings it up. A `wg_flood` of invalid-MAC1 initiations via io_uring
crosses the `handshake_queue_len >= 512` under_load threshold and sets the
kernel-global `last_under_load`; every flood packet is dropped at the MAC1 check
(reply-free). Within the one-second decay, N valid-MAC1 initiations are injected:
each is under load (via the decay), takes the VALID_MAC_BUT_NO_COOKIE arm and
makes wg0 send exactly one cookie reply, built from the captured secret and the
recorded nonce. `wg_observe` then sees N byte-exact cookie replies at the sender.

The merged-injection control bundles a valid initiation into the flood's
io_uring batch, so the kernel processes it in the flood's (discarded) receive-
worker section: the mirror's section-bracket discard then meets a modeled record
inside the flood section and fails closed (the two-distinct-sections assertion,
§4.1).

Deterministic: rerunning reproduces the files.
"""
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness import noise  # noqa: E402

_spec = importlib.util.spec_from_file_location("wg_d1_corpus", ROOT / "scripts" / "wg-d1-corpus.py")
d1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d1)

DEVICE, PEER, PORT = d1.DEVICE, d1.PEER, d1.PORT
BARE = {"net_fixture": "bare"}
CREATE = {"op": "wg_create"}
UP = {"op": "wg_up"}
OBSERVE = {"op": "wg_observe"}
GET = {"op": "wg_get"}
# Just above the 512 threshold: io_uring runs the sends inline in the trace task
# (KCOV on), so a larger count overflows the task and remote KCOV areas. All
# `count` packets queue before the single-CPU receive worker runs (io_uring_enter
# does not sleep), so the queue reaches `count` and crosses 512.
FLOOD_COUNT = 520


def configure():
    # the private key precomputes mac1_key and cookie_encryption_key; no peer
    # is needed (the cookie-reply path never consumes the initiation)
    return {"op": "wg_set", "config": {"private_key": d1.key(DEVICE), "listen_port": PORT, "peers": []}}


# arm C (ratelimiter): the cookie secret is steered, so the fixture computes
# make_cookie and a valid MAC2 to reach the ratelimiter; wg0's responses are
# steered (D1).
RL_SECRET = bytes(range(0x90, 0xb0))
RESP_EPHEMERAL_2 = bytes(range(0x21, 0x41))
RL_INDEX_1, RL_INDEX_2 = 0x11223344, 0x55667788
SENDER_SADDR = bytes([127, 0, 0, 1])
SENDER_SPORT = 51998


def configure_peer():
    return {"op": "wg_set", "config": {"private_key": d1.key(DEVICE), "listen_port": PORT,
            "peers": [{"public_key": d1.key(noise.public_key(d1.PEER)),
                       "allowed_ips": [{"family": 4, "addr": "0a000000", "cidr": 8}]}]}}


def rl_initiation(ephemeral, sec, index):
    """A real Noise initiation (peer -> wg0) with a valid MAC1 and a valid MAC2
    (from make_cookie under the steered secret), so wg0 under load reaches the
    ratelimiter; an allow makes wg0 consume it and send a handshake response."""
    cookie = noise.make_cookie(RL_SECRET, SENDER_SADDR, SENDER_SPORT)
    init = noise.initiation(noise.public_key(d1.DEVICE), d1.PEER, ephemeral, noise.tai64n(sec, 0), index)
    return noise.with_mac2(init, cookie)


def valid_initiation(index, ephemeral):
    """A valid-MAC1 initiation to wg0 (MAC1 keyed by blake2s('mac1----' ||
    wg0_public)); its body is not consumed (the under-load path sends a cookie
    and returns before consume_initiation)."""
    return noise.initiation(noise.public_key(DEVICE), PEER, ephemeral, noise.tai64n(1, 0), index)


def flood(leading=(), control=None, **extra):
    op = {"op": "wg_flood", "count": FLOOD_COUNT, "port": PORT}
    if leading:
        op["messages"] = [m.hex() for m in leading]
    if control is not None:
        op["control"] = control.hex()
    op.update(extra)
    return op


def base_ops():
    return [CREATE, configure(), UP]


def traces():
    # corpus/wireguard (default suite). The queue-depth design (docs/2026-10-05-
    # e-dos.md §4.1 appendix): the valid-MAC1 initiation(s) are submitted FIRST in
    # the flood's io_uring batch, so the worker processes them while the whole
    # batch is still queued (handshake_queue_len >= 512 -> under_load via the
    # queue depth, deterministic on both guest children, no 1-second decay). The
    # mirror checks each leading packet's records and its byte-exact cookie reply,
    # then discards the invalid flood. No injection, so nothing depends on the
    # decay.
    v1, v2 = valid_initiation(0x1111_1111, b"\x51" * 32), valid_initiation(0x2222_2222, b"\x52" * 32)
    return {
        # the flood crosses under_load with no leading valid: no cookie reply,
        # the whole section discarded (robust under_load + discard check)
        "e_underload_flood": base_ops() + [flood(), OBSERVE, GET],
        # one leading valid under load -> exactly one byte-exact cookie reply
        "e_underload_cookie": base_ops() + [flood(leading=[v1]), OBSERVE, GET],
        # two leading valids under load -> two byte-exact cookie replies
        "e_underload_two_replies": base_ops() + [flood(leading=[v1, v2]), OBSERVE, GET],
    }


def controls():
    return {
        # a mid-flood valid initiation the mirror does not model (`control`,
        # submitted after the leading valid): the kernel makes a cookie reply for
        # it inside the flood section, so its modeled records (the nonce) land in
        # the region the mirror discards after the checked leading packet. The
        # discard meets a modeled record and fails closed (supersedes E19's
        # two-section assertion; docs/2026-10-05-e-dos.md §4.1 appendix).
        "e_underload_merged": base_ops()
        + [flood(leading=[valid_initiation(0x3333_3333, b"\x53" * 32)],
                 control=valid_initiation(0x4444_4444, b"\x54" * 32)), OBSERVE, GET],
    }


def ratelimit_traces():
    # arm C: a flood sets under_load; then two valid-MAC1+MAC2 Noise initiations
    # from one source IP reach the ratelimiter. The first inserts a bucket entry
    # (always allows) and is consumed -> a handshake response. The second, same
    # IP, hits the bucket (ratelimiter.c:121, the token arithmetic): with tokens
    # left it is allowed and consumed, but noise.c's own flood check (50/s,
    # last_initiation_consumption) drops a second consume in the same tick, so it
    # produces no response. So the ratelimiter's allow is checked by the record
    # stream (allow -> consume reads flood_now; deny -> dropped before consume),
    # and its token compare by the operands; only the first response is steered.
    two = flood(leading=[rl_initiation(d1.PEER_EPHEMERAL, 1, d1.PEER_INDEX),
                         rl_initiation(d1.PEER_EPHEMERAL_2, 2, d1.PEER_INDEX_2)])
    steer = [["cookie_secret", RL_SECRET.hex()],
             ["resp_ephemeral", d1.RESP_EPHEMERAL.hex()], ["index_draw", d1.le32(RL_INDEX_1)]]
    expect = ["wg_receive_handshake_packet.initiation=1", "wg_ratelimiter_allow.entry_matches=1",
              "wg_ratelimiter_allow.inet=1"]
    return {"e_underload_ratelimit": dict(ops=[CREATE, configure_peer(), UP, two, OBSERVE, GET],
                                          steer=steer, expect=expect)}


def write_suite(subdir, cases):
    out = ROOT / "corpus" / subdir
    out.mkdir(exist_ok=True)
    for name, ops in cases.items():
        (out / f"{name}.json").write_text(json.dumps({"version": 1, "id": name, "net_fixture": "bare", "ops": ops},
                                                     indent=2) + "\n")


def write_steered(subdir, cases):
    out = ROOT / "corpus" / subdir
    out.mkdir(exist_ok=True)
    for name, c in cases.items():
        trace = {"version": 1, "id": name, "net_fixture": "bare", "ops": c["ops"],
                 "steer": c["steer"], "expect": c["expect"]}
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")


def main():
    write_suite("wireguard", traces())
    write_steered("wireguard", ratelimit_traces())
    write_suite("underload-controls", controls())
    print(f"wrote {len(traces())} + {len(ratelimit_traces())} wireguard and {len(controls())} control traces")


if __name__ == "__main__":
    main()
